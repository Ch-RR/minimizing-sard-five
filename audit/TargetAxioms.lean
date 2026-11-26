import FiveDimensionalMinimizingSard
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let axioms ← collectAxioms `MinimizingSard.Five.five_dimensional_metric_minimizing_sard
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for ax in axioms do
    unless allowed.contains ax do
      throwError "Unexpected axiom in the final theorem: {ax}"
  logInfo m!"Final theorem axiom dependencies: {axioms}"
