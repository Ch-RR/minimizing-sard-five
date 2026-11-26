"""Run with lake env python check.py after fetching the matching mathlib cache."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent
os.chdir(ROOT)
BUILD = ROOT / ".proof-build"
BUILD.mkdir(exist_ok=True)
env = os.environ.copy()
env["LEAN_PATH"] = os.pathsep.join(filter(None, [str(BUILD), env.get("LEAN_PATH")]))
ledger = json.loads((ROOT / "sources.json").read_text(encoding="utf-8"))
order = {}
for name, expected in ledger.items():
    path = ROOT / name
    if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
        raise ValueError(f"Source digest mismatch for {name}")
    imports = re.findall(r"^import\s+([A-Za-z0-9_.]+)", path.read_text(encoding="utf-8"), re.M)
    order[name] = {dep + ".lean" for dep in imports if dep + ".lean" in ledger}
done = set()
while len(done) < len(order):
    ready = sorted(name for name, deps in order.items() if name not in done and deps <= done)
    if not ready:
        raise RuntimeError("Cyclic project imports")
    for name in ready:
        print(f"[{len(done) + 1}/{len(order)}] {name}", flush=True)
        subprocess.run(["lean", "-o", str(BUILD / Path(name).with_suffix(".olean")), name],
                       env=env, check=True)
        done.add(name)
subprocess.run(["lean", "--run", "replay.lean", str(BUILD),
                "MinimizingSard.Five.five_dimensional_metric_minimizing_sard"], env=env, check=True)
for audit in ("Proposition63.lean", "AuditAnchors.lean"):
    subprocess.run(["lean", audit], env=env, check=True)
