import AllRankNormalValues
import FrameHorizontalRank

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] [IsManifold 𝓘(ℝ,State) ∞ M] [T2Space M]

/-- A common null set excludes all minimizing singular controls with a
four-dimensional endpoint differential in every horizontal rank at least two. -/
theorem ae_no_rank_four_minimizer {m : ℕ} (Γ : Geometry M m) (hm : 2 ≤ m) (x : M)
    (c : OpenPartialHomeomorph M State) (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) :
    ∀ᵐ Q : State, ∀ y, Q = c y → y ∈ c.source → ∀ {n : ℕ} (e : Fin (n+1) → Frame M m)
      (w : Fin (n+1) → Control m), (∀ i, e i ∈ Γ.frames) → Joins e w x y →
      (∀ (k : ℕ) (f : Fin (k+1) → Frame M m) (v : Fin (k+1) → Control m),
        (∀ i, f i ∈ Γ.frames) → Joins f v x y → length w ≤ length v) →
      ∀ G : (Fin (n+1) → Control m) → State, G w = c y → DifferentiableAt ℝ G w →
      (∀ᶠ v in 𝓝 w, G v ∈ c.target ∧ ∀ t, Joins e v x t ↔ t = c.symm (G v)) →
      ¬ Function.Surjective (fderiv ℝ G w) →
      Module.finrank ℝ (LinearMap.range (fderiv ℝ G w).toLinearMap) ≠ 4 := by
  filter_upwards [ae_no_supported_singular Γ x c hc,all_rank_corank_one_multiplier Γ hm x c hc]
    with Q exclude mult
  rintro y rfl cy n e w he walk minimal G gw dg gr bad rank
  have h := mult (c.map_source cy) e w G
  rw [c.left_inv cy] at h
  exact exclude y rfl cy e w he walk G gw dg gr bad (h he walk minimal gr rank)

/-- Fixed-source minimizing Sard in five dimensions for horizontal rank four,
in the original local frame/control definition, on arbitrary smooth charts. -/
theorem rank_four_minimizing_sard : ConclusionAtRank M 4 := by
  intro Γ x c hc
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [ae_no_rank_four_minimizer Γ (by decide) x c hc] with Q outside
  rintro ⟨y,⟨cy,n,e,w,he,path,sing,minimal⟩,rfl⟩
  obtain ⟨G,D,gw,gr,dg,bad⟩ := (singular_iff_in_chart e w x y c hc cy).mp sing
  rw [← dg.fderiv] at bad
  let W := LinearMap.range (fderiv ℝ G w).toLinearMap
  have low : 4 ≤ Module.finrank ℝ W := all_rank_endpoint_floor e w x y path c hc cy G dg.differentiableAt gr
  have lt : W < ⊤ := lt_top_iff_ne_top.mpr (fun eq => bad (LinearMap.range_eq_top.mp eq))
  have high := Submodule.finrank_lt_finrank_of_lt lt
  rw [finrank_top,Module.finrank_fin_fun] at high
  apply outside y rfl cy e w he path minimal G gw dg.differentiableAt gr bad
  change Module.finrank ℝ W = 4
  omega

/-- The outstanding horizontal-rank-three problem is confined to endpoint
differential rank three with no supporting length covector. -/
theorem ae_rank_three_residual (Γ : Geometry M 3) (x : M)
    (c : OpenPartialHomeomorph M State) (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) :
    ∀ᵐ Q : State, ∀ y, Q = c y → y ∈ c.source → ∀ {n : ℕ} (e : Fin (n+1) → Frame M 3)
      (w : Fin (n+1) → Control 3), (∀ i, e i ∈ Γ.frames) → Joins e w x y →
      (∀ (k : ℕ) (f : Fin (k+1) → Frame M 3) (v : Fin (k+1) → Control 3),
        (∀ i, f i ∈ Γ.frames) → Joins f v x y → length w ≤ length v) →
      ∀ G : (Fin (n+1) → Control 3) → State, G w = c y → DifferentiableAt ℝ G w →
      (∀ᶠ v in 𝓝 w, G v ∈ c.target ∧ ∀ t, Joins e v x t ↔ t = c.symm (G v)) →
      ¬ Function.Surjective (fderiv ℝ G w) →
      Module.finrank ℝ (LinearMap.range (fderiv ℝ G w).toLinearMap) = 3 ∧
        ¬ HasCostMultiplier length (fderiv ℝ G w) w := by
  filter_upwards [ae_no_supported_singular Γ x c hc,ae_no_rank_four_minimizer Γ (by decide) x c hc]
    with Q exclude four
  rintro y rfl cy n e w he walk minimal G gw dg gr bad
  refine ⟨?_,exclude y rfl cy e w he walk G gw dg gr bad⟩
  let W := LinearMap.range (fderiv ℝ G w).toLinearMap
  have low : 3 ≤ Module.finrank ℝ W := all_rank_endpoint_floor e w x y walk c hc cy G dg gr
  have ne : Module.finrank ℝ W ≠ 4 := four y rfl cy e w he walk minimal G gw dg gr bad
  have lt : W < ⊤ := lt_top_iff_ne_top.mpr (fun eq => bad (LinearMap.range_eq_top.mp eq))
  have high := Submodule.finrank_lt_finrank_of_lt lt
  rw [finrank_top,Module.finrank_fin_fun] at high
  change Module.finrank ℝ W = 3
  omega

#print axioms ae_no_rank_four_minimizer
#print axioms rank_four_minimizing_sard
#print axioms ae_rank_three_residual
end MinimizingSard.Five
