import AllFrameAdjoint
import NormalEndpointParameters

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
open Volterra
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] {m : ℕ}

/-- One original segment already supplies a Hamiltonian piece in every
horizontal rank. The singleton subdivision preserves every competitor. -/
theorem all_rank_segment_lift : SegmentLiftSolver M m := by
  intro e u x y seg G dg gr η sup
  obtain ⟨Z,hZ,z₀,z₁,incoming⟩ := all_frame_normal_piece e u seg G dg gr η sup
  let R := (ContinuousLinearEquiv.funUnique (Fin 1) ℝ (Control m)).symm
  let k : Fin 2 → State := ![e.chart x,e.chart y]
  let p : Fin 2 → State →L[ℝ] ℝ := ![(Z (clamp 0)).2,η]
  refine ⟨1,R,k,p,fun _ => Z,rfl,rfl,ContinuousLinearMap.ext incoming,rfl,?_,?_,?_⟩
  · intro v
    rw [length_pieces,Fin.sum_univ_one]
    rfl
  · intro v a b
    constructor
    · intro path
      refine ⟨![a,b],rfl,rfl,fun i => ?_⟩
      fin_cases i
      exact path
    · rintro ⟨q,qa,qb,s⟩
      simpa only [← qa,← qb] using s 0
  · intro i
    fin_cases i
    exact ⟨Prod.ext z₀ rfl,z₁,hZ⟩

variable [IsManifold 𝓘(ℝ,State) ∞ M] [T2Space M]

/-- A common null set covers every singular endpoint having any supporting
length covector, simultaneously for all chart sequences and durations. -/
theorem ae_no_supported_singular (Γ : Geometry M m) (x : M)
    (c : OpenPartialHomeomorph M State) (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) :
    ∀ᵐ Q : State, ∀ y, Q = c y → y ∈ c.source → ∀ {n : ℕ} (e : Fin (n+1) → Frame M m)
      (w : Fin (n+1) → Control m), (∀ i, e i ∈ Γ.frames) → Joins e w x y →
      ∀ G : (Fin (n+1) → Control m) → State, G w = c y → DifferentiableAt ℝ G w →
      (∀ᶠ v in 𝓝 w, G v ∈ c.target ∧ ∀ t, Joins e v x t ↔ t = c.symm (G v)) →
      ¬ Function.Surjective (fderiv ℝ G w) → ¬ HasCostMultiplier length (fderiv ℝ G w) w := by
  let P := normalParameterMap Γ x c
  let C (i : Bool) := P i '' {z | DifferentiableAt ℝ (P i) z ∧ ¬ Function.Surjective (fderiv ℝ (P i) z)}
  have null : volume (⋃ i, C i) = 0 := measure_iUnion_null fun i => critical_values_null (P i)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp null] with Q outside
  intro y eq cy n e w he walk G gw dg gr bad support
  obtain ⟨i,ξ,V,vw,dv,factor⟩ := parameter_factor_of_segment_solver
    (fun f u a b seg => frame_segment_graph f u a b seg 1 le_rfl) all_rank_segment_lift
    Γ x y c hc cy e w he walk G gw gr support
  have eq₀ : P i ξ = Q := factor.self_of_nhds.trans (by simp only [Function.comp_apply,vw,gw,eq])
  apply outside
  apply mem_iUnion.mpr
  exact ⟨i,eq₀ ▸ critical_of_control_factor (P i) ξ V G dv (vw.symm ▸ dg) factor (vw.symm ▸ bad)⟩

#print axioms all_rank_segment_lift
#print axioms ae_no_supported_singular
end MinimizingSard.Five
