import PrimitivePairing
import ControlledPathDependence

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace MinimizingSard.Five
open Volterra
variable {E U : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup U] [NormedSpace ℝ U]

/-- Solve the controlled linearized equation at once for every initial
tangent vector. The entire solution operator is bounded and linear. -/
theorem linear_input_evolution (D : C(Time,E →L[ℝ] U →L[ℝ] E)) (u : Causal.Signals U) :
    ∃ S : E →L[ℝ] C(Time,E), ∀ a, TimePrimitive (S a) a
      (fun r => D (clamp r) (S a (clamp r)) (u r)) := by
  let H := (ContinuousLinearMap.apply ℝ C(Time,E) u).comp (Volterra.operator U E)
  let K := H.comp (PathCalculus.multiplier Time E (U →L[ℝ] E) D)
  obtain ⟨g,ge⟩ := controlled_linear_inverse u D
  let J := ContinuousLinearEquiv.unitsEquiv ℝ (C(Time,E)) g
  let I : E →L[ℝ] C(Time,E) := ContinuousLinearMap.const ℝ Time
  let S := J.symm.toContinuousLinearMap.comp I
  refine ⟨S,fun a => ?_⟩
  let B := PathCalculus.multiplier Time E (U →L[ℝ] E) D (S a)
  have eq := J.apply_symm_apply (I a)
  change (g : C(Time,E) →L[ℝ] C(Time,E)) (S a) = I a at eq
  rw [ge] at eq
  refine ⟨Volterra.intervalIntegrable B u,fun t => ?_⟩
  have val := congrArg (fun b : C(Time,E) => b t) eq
  change S a t - Volterra.operator U E B u t = a at val
  rw [operator_eq_interval] at val
  exact sub_eq_iff_eq_add.mp val

variable {m : ℕ}
private abbrev Row := State →L[ℝ] ℝ
private abbrev Jet (m : ℕ) := State →L[ℝ] Fiber m →L[ℝ] State

private def dualJet (D : Jet m) : Row →L[ℝ] Fiber m →L[ℝ] Row :=
  -(((ContinuousLinearMap.compL ℝ (Fiber m) (State →L[ℝ] State) Row).flip D.flip).comp
    (ContinuousLinearMap.compL ℝ State State ℝ))

private theorem dualJet_apply (D : Jet m) (p : Row) (v : Fiber m) (h : State) :
    dualJet D p v h = -p (D h v) := rfl

/-- The terminal value problem for the true costate along a rough controlled
trajectory. Forward state variations prove injectivity of terminal covector
transport, which is then onto by finite dimensionality. -/
theorem terminal_linear_adjoint (D : C(Time,Jet m)) (u : Causal.Signals (Fiber m)) (η : Row) :
    ∃ p : C(Time,Row), p (clamp 1) = η ∧
      TimePrimitive p (p (clamp 0)) (fun r => -((p (clamp r)).comp ((D (clamp r)).flip (u r)))) := by
  letI : NormedAddCommGroup Row := inferInstance
  letI : NormedSpace ℝ Row := inferInstance
  letI : NormedAddCommGroup (Fiber m →L[ℝ] Row) := inferInstance
  letI : NormedSpace ℝ (Fiber m →L[ℝ] Row) := inferInstance
  letI : NormedAddCommGroup (Row →L[ℝ] Fiber m →L[ℝ] Row) := inferInstance
  have cd : Continuous (fun t : Time => dualJet (D t)) := by
    apply continuous_clm_apply.mpr
    intro p
    apply continuous_clm_apply.mpr
    intro v
    apply continuous_clm_apply.mpr
    intro h
    exact (p.continuous.comp ((D.continuous.clm_apply continuous_const).clm_apply continuous_const)).neg
  let A : C(Time,Row →L[ℝ] Fiber m →L[ℝ] Row) := ⟨_,cd⟩
  obtain ⟨P,hp⟩ := linear_input_evolution A u
  obtain ⟨W,hw⟩ := linear_input_evolution D u
  let R := (ContinuousMap.evalCLM ℝ (clamp 1) : C(Time,Row) →L[ℝ] Row).comp P
  have ker : LinearMap.ker R.toLinearMap = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro b hb
    change P b (clamp 1) = 0 at hb
    apply ContinuousLinearMap.ext
    intro a
    have rule : ∀ᵐ r ∂volume.restrict (Ioo (0:ℝ) 1),
        A (clamp r) (P b (clamp r)) (u r) (W a (clamp r)) +
        P b (clamp r) (D (clamp r) (W a (clamp r)) (u r)) = (0:ℝ) := by
      exact .of_forall (fun r => neg_add_cancel _)
    have pair := time_pairing (hw a) (hp b) (fun _ => 0) intervalIntegrable_const rule (clamp 1)
    simpa [hb] using pair.symm
  have onto := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := R.toLinearMap) rfl).mp (LinearMap.ker_eq_bot.mp ker)
  obtain ⟨b,hb⟩ := onto η
  exact ⟨P b,hb,(hp b).at_zero.symm ▸ hp b⟩

#print axioms linear_input_evolution
#print axioms terminal_linear_adjoint
end MinimizingSard.Five
