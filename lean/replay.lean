import Lean.Replay
import Lean.Util.Path

open Lean

private def sameTheorem : ConstantInfo → ConstantInfo → Bool
  | .thmInfo a, .thmInfo b =>
    a.name == b.name && a.levelParams == b.levelParams && a.type == b.type && a.value == b.value
  | _, _ => false

/-- Recheck the declarations stored in a frozen project run against an
environment containing only its external dependencies. -/
def main (args : List String) : IO Unit := do
  let [directory, theoremName] := args
    | throw <| IO.userError "expected a frozen run directory and a fully qualified theorem name"
  initSearchPath (← findSysroot)
  let files := (← (System.FilePath.mk directory).readDir).filter (fun f => f.path.extension == some "olean")
  if files.isEmpty then throw <| IO.userError "no project artifacts"
  let project := files.foldl (init := ({} : NameSet)) (fun acc f => acc.insert f.path.fileStem.get!.toName)
  let mut imports : NameSet := {}
  let mut constants : Std.HashMap Name ConstantInfo := {}
  let mut modules := #[]
  for file in files do
    let (data, _) ← readModuleData file.path
    modules := modules.push (file.path.fileStem.get!.toName, data)
    for dep in data.imports do
      if !project.contains dep.module then imports := imports.insert dep.module
    for ci in data.constants do
      if let some old := constants[ci.name]? then
        if !sameTheorem old ci then throw <| IO.userError s!"distinct declarations share name {ci.name}"
        continue
      if !ci.isUnsafe && !ci.isPartial then
        if ci matches .axiomInfo _ then throw <| IO.userError s!"project axiom {ci.name}"
        if ci.getUsedConstantsAsSet.contains `sorryAx then throw <| IO.userError s!"placeholder in {ci.name}"
      constants := constants.insert ci.name ci
  let target := theoremName.toName
  let some (.thmInfo _) := constants[target]? | throw <| IO.userError s!"missing theorem {target}"
  let base ← importModules (imports.toArray.map fun mod => { module := mod }) {} 0
  for mod in project do
    if (base.getModuleIdx? mod).isSome then throw <| IO.userError s!"project import in replay base: {mod}"
  let mut checked := base
  let mut doneModules : NameSet := {}
  let mut total := 0
  let mut skipped := 0
  while doneModules.size < files.size do
    let start := doneModules.size
    for (mod, data) in modules do
      if doneModules.contains mod then continue
      if !data.imports.all (fun dep => !project.contains dep.module || doneModules.contains dep.module) then continue
      let mut block : Std.HashMap Name ConstantInfo := {}
      for ci in data.constants do
        if let some old := checked.toKernelEnv.find? ci.name then
          if !sameTheorem old ci then throw <| IO.userError s!"distinct declaration in dependencies: {ci.name}"
          continue
        if ci.isUnsafe || ci.isPartial then skipped := skipped + 1
        else total := total + 1
        block := block.insert ci.name ci
      -- Start a new elaborator name table for each module. The kernel
      -- environment, including all its checked declarations, is retained.
      let next ← checked.replay block
      checked := Environment.ofKernelEnv next.toKernelEnv
      for (name, ci) in block.toList do
        if !ci.isUnsafe && !ci.isPartial && (checked.toKernelEnv.find? name).isNone then
          throw <| IO.userError s!"declaration absent after kernel replay: {name}"
      doneModules := doneModules.insert mod
    if doneModules.size == start then throw <| IO.userError "cyclic project imports"
  if (checked.toKernelEnv.find? target).isNone then throw <| IO.userError s!"target absent after kernel replay: {target}"
  IO.println s!"kernel replay accepted {target}"
  IO.println s!"project modules: {files.size}; safe declarations checked: {total}; unsafe/partial declarations skipped by Lean.Replay: {skipped}"
