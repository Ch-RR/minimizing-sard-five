import SobolevFrameCharts

noncomputable section
open Set Filter MeasureTheory IsManifold Metric
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
open Volterra

/-- Chain rule for the ambient L² velocity with a compact trajectory.
The resulting Bochner primitive gives pointwise equality at every time. -/
theorem ambient_chain (p : State × Control 5) (Y : State → State) (cy : ContDiff ℝ 1 Y) :
    let J := pathField (fderiv ℝ Y) (cy.continuous_fderiv le_rfl) (ambientPath p)
    ∀ t : Time, ambientPath (Y p.1,multiplyVelocity State State J p.2) t = Y (ambientPath p t) := by
  intro J
  let w := ambientPath p
  let z (r : ℝ) := w (clamp r)
  let v := multiplyVelocity State State J p.2
  have prim := ambient_primitive p
  have w0 : z 0 = p.1 := prim.at_zero
  let B := closedBall (0:State) ‖w‖
  have inB (r : ℝ) : z r ∈ B := by simpa [B,z] using w.norm_coe_le_norm (clamp r)
  obtain ⟨C,bound⟩ := (isCompact_closedBall (0:State) ‖w‖).bddAbove_image (cy.continuous_fderiv le_rfl).norm.continuousOn
  have cap (x : State) (hx : x ∈ B) : ‖fderiv ℝ Y x‖ ≤ C := bound (mem_image_of_mem _ hx)
  have cpos := (norm_nonneg _).trans (cap _ (inB 0))
  have dom : DominatedPath (fun r => Y (z r)) := prim.dominated.map_bound _ C cpos (by
    intro s _ t _ _
    simpa only [dist_eq_norm] using (convex_closedBall (0:State) ‖w‖).norm_image_sub_le_of_norm_fderiv_le
      (fun x _ => cy.differentiable le_rfl x) cap (inB s) (inB t))
  have ae := multiplyVelocity_ae J p.2
  have ae' : (fun r => v r) =ᵐ[volume.restrict (Ioo (0:ℝ) 1)] (fun r => J (clamp r) (p.2 r)) := by
    simpa only [Measure.restrict_congr_set Ioo_ae_eq_Icc] using ae
  have iv := (ambient_primitive (Y p.1,v)).1
  have int := dom.integral (fun r => v r) iv (by
    filter_upwards [prim.ae_derivative,ae'] with r der vel
    exact vel.symm ▸ (cy.differentiable le_rfl (z r)).hasFDerivAt.comp_hasDerivAt r der)
  intro t
  have ev := int t t.property
  rw [w0] at ev
  change Y (w (clamp (t:ℝ))) = _ at ev
  rw [show clamp (t:ℝ) = t from projIcc_val _ _] at ev
  exact ((ambient_primitive (Y p.1,v)).2 t).trans ev.symm

/-- A smooth state coordinate change acts smoothly on ambient W¹,² coordinates.
Its velocity is the genuine almost-everywhere chain rule along each nearby path. -/
theorem sobolev_coordinate_germ (O : Set State) (op : IsOpen O) (T : State → State) (reg : ContDiffOn ℝ ∞ T O)
    (p : State × Control 5) (inside : ∀ t, ambientPath p t ∈ O) (k : ℕ) :
    ∃ H : State × Control 5 → State × Control 5, ContDiffAt ℝ k H p ∧ ∀ᶠ z in 𝓝 p,
      (H z).1 = T z.1 ∧ (∀ t, ambientPath z t ∈ O ∧ ambientPath (H z) t = T (ambientPath z t)) ∧
      (fun r => (H z).2 r) =ᵐ[controlMeasure] (fun r => fderiv ℝ T (ambientPath z (clamp r)) (z.2 r)) := by
  let w := ambientPath p
  obtain ⟨Y,V,cy,ov,wv,sub,agree⟩ := compact_smooth_extension O (range w) op
    (isCompact_range w.continuous) (range_nonempty _) (range_subset_iff.mpr inside) T
    (reg.of_le (by exact_mod_cast (le_top : ((k+1):ℕ∞) ≤ ⊤)) : ContDiffOn ℝ (k+1 : ℕ) T O)
  have c₁ : ContDiff ℝ 1 Y := cy.of_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k))
  have dY : ContDiff ℝ k (fderiv ℝ Y) := cy.fderiv_right (by simp)
  let J (z : State × Control 5) := pathField (fderiv ℝ Y) dY.continuous (ambientPath z)
  let H (z : State × Control 5) := (Y z.1,multiplyVelocity State State (J z) z.2)
  have cj : ContDiff ℝ k J := (pathField_smooth _ dY).comp ambientPath.contDiff
  have ch : ContDiffAt ℝ k H p := ((cy.of_le (by exact_mod_cast Nat.le_succ k)).contDiffAt.comp p contDiffAt_fst).prodMk
    (multiplyVelocity_smooth cj.contDiffAt contDiffAt_snd)
  have stay : {z : C(Time,State) | MapsTo z univ V} ∈ 𝓝 w :=
    (ContinuousMap.isOpen_setOf_mapsTo isCompact_univ ov).mem_nhds (fun t _ => wv (mem_range_self t))
  refine ⟨H,ch,?_⟩
  filter_upwards [(ambientPath.continuous.tendsto p) stay] with z near
  have good (t : Time) : ambientPath z t ∈ V := near (mem_univ t)
  refine ⟨agree (by rw [← (ambient_primitive z).at_zero]; exact good _),fun t => ⟨sub (good t),?_⟩,?_⟩
  · exact (ambient_chain z Y c₁ t).trans (agree (good t))
  · filter_upwards [multiplyVelocity_ae (J z) z.2] with r h
    have same : Y =ᶠ[𝓝 (ambientPath z (clamp r))] T := Filter.mem_of_superset (ov.mem_nhds (good _)) agree
    exact h.trans (DFunLike.congr_fun (same.fderiv_eq (𝕜 := ℝ)) _)

#print axioms ambient_chain
#print axioms sobolev_coordinate_germ
end MinimizingSard.Five
