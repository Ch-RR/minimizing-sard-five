import ControlledPathDependence

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff
namespace MinimizingSard.Five
open Volterra
variable {U E : Type} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- An actual absolutely continuous controlled solution in an open coordinate domain. -/
def IsControlledPath (O : Set E) (X : E → U →L[ℝ] E) (u : Causal.Signals U) (q : E) (w : C(Time,E)) : Prop :=
  (∀ t, w t ∈ O) ∧ ∀ t : Time, w t = q + ∫ r in (0:ℝ)..(t:ℝ), X (w (clamp r)) (u r)

/-- Uniqueness among all solutions remaining in the original coordinate
domain, including competitors outside the neighborhood from the inverse
function argument. -/
theorem controlled_path_unique (O : Set E) (op : IsOpen O) (X : E → U →L[ℝ] E) (cx : ContDiffOn ℝ 1 X O)
    (u : Causal.Signals U) (q : E) (w z : C(Time,E)) (hw : IsControlledPath O X u q w)
    (hz : IsControlledPath O X u q z) : w = z := by
  let K := range w ∪ range z
  have comp : IsCompact K := (isCompact_range w.continuous).union (isCompact_range z.continuous)
  have sub : K ⊆ O := union_subset (range_subset_iff.mpr hw.1) (range_subset_iff.mpr hz.1)
  obtain ⟨Y,V,cy,_,contains,_,same⟩ := compact_smooth_extension O K op comp
    ((range_nonempty w).mono subset_union_left) sub X cx
  have wy (r : Time) : Y (w r) = X (w r) := same (contains (Or.inl (mem_range_self r)))
  have zy (r : Time) : Y (z r) = X (z r) := same (contains (Or.inr (mem_range_self r)))
  let B := closedBall (0:E) (‖w‖+‖z‖)
  have inW (r : Time) : w r ∈ B := by
    simpa only [B,mem_closedBall,dist_zero_right] using (w.norm_coe_le_norm r).trans (le_add_of_nonneg_right (norm_nonneg z))
  have inZ (r : Time) : z r ∈ B := by
    simpa only [B,mem_closedBall,dist_zero_right] using (z.norm_coe_le_norm r).trans (le_add_of_nonneg_left (norm_nonneg w))
  have cd := (cy.fderiv_right (m := 0) (by decide)).continuous
  obtain ⟨C,bd⟩ := (isCompact_closedBall (0:E) (‖w‖+‖z‖)).bddAbove_image cd.norm.continuousOn
  have cap (x) (hx : x ∈ B) : ‖fderiv ℝ Y x‖ ≤ C := bd (mem_image_of_mem _ hx)
  have cp := (norm_nonneg (fderiv ℝ Y (w (clamp 0)))).trans (cap _ (inW (clamp 0)))
  let ν (r : ℝ) := C*‖u r‖
  have iv : IntervalIntegrable ν volume 0 1 := (signal_norm_integrable u).const_mul C
  let W := pathField Y cy.continuous w
  let Z := pathField Y cy.continuous z
  have wi := Volterra.intervalIntegrable W u
  have zi := Volterra.intervalIntegrable Z u
  let h : C(Time,E) := w-z
  have dom : IntegralMajorant ν h h := by
    intro t
    have subint {F : Type} [NormedAddCommGroup F] {f : ℝ → F} (i : IntervalIntegrable f volume 0 1) :
        IntervalIntegrable f volume 0 (t:ℝ) :=
      i.mono_set (by rw [uIcc_of_le t.property.1,uIcc_of_le zero_le_one]; exact Icc_subset_Icc le_rfl t.property.2)
    have hW := hw.2 t
    have hZ := hz.2 t
    simp_rw [← wy] at hW
    simp_rw [← zy] at hZ
    have eq : h t = ∫ r in (0:ℝ)..(t:ℝ), (W (clamp r)-Z (clamp r)) (u r) := by
      change w t-z t = _
      rw [hW,hZ,add_sub_add_left_eq_sub]
      change (∫ r in (0:ℝ)..(t:ℝ), W (clamp r) (u r)) - (∫ r in (0:ℝ)..(t:ℝ), Z (clamp r) (u r)) = _
      rw [← intervalIntegral.integral_sub (subint wi) (subint zi)]
      rfl
    rw [eq]
    have im := iv.mul_continuousOn (g := fun r => ‖h (clamp r)‖)
      (h.continuous.comp (show Continuous clamp from continuous_projIcc)).norm.continuousOn
    have diff := Volterra.intervalIntegrable (W-Z) u
    apply (intervalIntegral.norm_integral_le_integral_norm t.property.1).trans
      (intervalIntegral.integral_mono_on t.property.1 (subint diff.norm) (subint im) ?_)
    intro r _
    have lip := (convex_closedBall (0:E) (‖w‖+‖z‖)).norm_image_sub_le_of_norm_fderiv_le
      (fun x _ => cy.differentiable (by decide) x) cap (inZ (clamp r)) (inW (clamp r))
    calc ‖(W (clamp r)-Z (clamp r)) (u r)‖ ≤ ‖W (clamp r)-Z (clamp r)‖*‖u r‖ :=
          (W (clamp r)-Z (clamp r)).le_opNorm _
         _ ≤ (C*‖h (clamp r)‖)*‖u r‖ := mul_le_mul_of_nonneg_right lip (norm_nonneg _)
         _ = _ := by dsimp [ν]; ring
  exact sub_eq_zero.mp (zero_of_integral_majorant ν iv (fun r => mul_nonneg cp (norm_nonneg _)) h dom)

#print axioms controlled_path_unique
end MinimizingSard.Five
