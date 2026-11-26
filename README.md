# An autonomous proof of the minimizing Sard conjecture in dimension five with GPT-6.2 Astra

**Renrui Chen** · [2470521716@qq.com](mailto:2470521716@qq.com)

[中文导读](README.zh-CN.md) · [Read the paper (PDF)](paper/minimizing-sard-five.pdf) · [Proof audit](audit/minimizing-sard-five-audit.pdf) · [Lean theorem](lean/FiveDimensionalMinimizingSard.lean#L75)

Fix a starting point. Perturb the controls of a shortest horizontal path. The path is singular if its endpoint cannot move in every tangent direction to first order. In dimension five, the set of endpoints reached by at least one such shortest path has zero smooth outer volume.

## The five-dimensional minimizing Sard conjecture

Let $M$ be a connected, second-countable Hausdorff smooth five-manifold without boundary. Equip a smooth bracket-generating distribution of constant rank $0<m<5$ with a smooth positive horizontal metric. For a source $x$, write $E_x$ for the endpoint map on horizontal Sobolev paths starting at $x$, and $L$ for their length. For every smooth positive density $\mu$, the theorem gives

$$
\mu^*\!\left(\{y\in M:\exists\gamma,\ E_x(\gamma)=y,\ L(\gamma)=d(x,y),\ \operatorname{rank}D_\gamma E_x<5\}\right)=0.
$$

The quantifier is **every fixed source**. A single singular minimizer puts its endpoint in the exceptional set, even if a regular minimizer reaches the same point. The assertion concerns attained minima and permits incomplete sub-Riemannian distance.

## Relation to earlier work

Rifford's Theorem 1.1 establishes the minimizing Sard property for complete structures under an almost-everywhere upper bound of one on the Goh rank of minimizing paths. One consequence covers distributions of corank two. In a five-manifold a rank-two distribution has corank three. The theorem in this repository treats that case for arbitrary smooth bracket-generating rank-two distributions, including points of variable bracket growth. The geometric dimension is fixed at five. [Rifford, *Journal de l’École polytechnique — Mathématiques* (2023)](https://doi.org/10.5802/jep.242)

**MSC 2020** · 53C17 (sub-Riemannian geometry), 49K15 (optimal control), 93B05 (controllability).

## Read the proof

1. Section 4.3 identifies a bracket-defined line in the two missing endpoint directions of the difficult rank-two branch.
2. Sections 4.4–4.5 bound the cost of endpoint corrections and obtain entire rectangles of nearby endpoints at lower cost.
3. Section 4.1 shows that base points of such anisotropic descent rectangles form a null set. Section 4.6 treats the supported branch and assembles the conclusion.

To examine the rank-two argument, start with Proposition 4.4 and Proposition 6.3 of the [paper](paper/minimizing-sard-five.pdf). The [audit](audit/minimizing-sard-five-audit.pdf) maps the numbered paper results to Lean declarations and records the scope of the formal instances. The proof of the common-null-set statement also has a [separate Lean check](lean/Proposition63.lean).

The [declaration index](lean/AuditAnchors.lean) lists the Lean names used in the paper audit. For the formal statement, open the [main theorem](lean/FiveDimensionalMinimizingSard.lean#L75).

## Reproduce the check

Install Git, [elan](https://github.com/leanprover/elan), and Python 3.8+. Run from the repository root:

```sh
cd lean
lake exe cache get
lake env python3 check.py
```

For an ordinary Lake build, run `lake build` in the same directory after fetching the cache. Open `lean/` as the editor workspace. The [CI workflow](.github/workflows/verify.yml) also checks the target’s axiom dependencies and the skipped-declaration audit. [View runs](https://github.com/Ch-RR/minimizing-sard-five/actions/workflows/verify.yml).

Use `python` if that is your Python executable. The first build downloads dependencies. The [verification script](lean/check.py) checks source hashes, compiles the 150 frozen project modules, replays their safe declarations, and checks two supplementary audit files. See the [archived replay record](audit/README.md).

Renrui Chen directed the investigation and specified the proof target. GPT-6.2 Astra, used through OpenAI’s Codex, developed the mathematical arguments, wrote and revised the Lean formalization, and drafted the manuscript. To report a discrepancy, include the paper statement number, Lean declaration and the step in question.
