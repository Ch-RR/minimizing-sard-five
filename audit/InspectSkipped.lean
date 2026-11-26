import Lean.Replay
import Lean.Util.Path

open Lean

def main (args : List String) : IO Unit := do
  let [directory] := args | throw <| IO.userError "expected project object directory"
  initSearchPath (← findSysroot)
  let mut project : Std.HashMap Name ConstantInfo := {}
  let mut skipped : NameSet := {}
  for file in (← (System.FilePath.mk directory).readDir) do
    unless file.path.extension == some "olean" do continue
    let (data, _) ← readModuleData file.path
    for ci in data.constants do
      project := project.insert ci.name ci
      if ci.isUnsafe || ci.isPartial then
        IO.println s!"{file.path.fileStem.get!} | {ci.name} | unsafe={ci.isUnsafe} partial={ci.isPartial}"
        skipped := skipped.insert ci.name
  let target := `MinimizingSard.Five.five_dimensional_metric_minimizing_sard
  unless project.contains target do throw <| IO.userError "target missing"
  let mut pending := [target]
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    if seen.contains n then continue
    let some ci := project[n]? | continue
    seen := seen.insert n
    pending := ci.getUsedConstantsAsSet.toArray.toList ++ pending
  let hits := skipped.toArray.filter (fun n => seen.contains n)
  IO.println s!"project declarations reached = {seen.size}, skipped = {skipped.size}, intersection = {hits}"
  unless hits.isEmpty do throw <| IO.userError "target reaches a skipped declaration"
