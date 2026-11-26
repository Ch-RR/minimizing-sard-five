import CompactPathField
import VolterraInverse

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff
namespace MinimizingSard.Five
open Volterra
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Smooth dependence, in the uniform path norm, along an entire prescribed
compact solution on an open chart. The length of the interval and the size
of its spatial derivative impose no smallness condition. -/
theorem orbit_path_dependence (U : Set E) (openU : IsOpen U) (X : E → E) (cx : ContDiffOn ℝ 1 X U)
    (w : C(Time,E)) (inside : ∀ t, w t ∈ U)
    (eq : ∀ t : Time, w t = w (clamp 0) + ∫ r in (0:ℝ)..(t:ℝ), X (w (clamp r))) :
    ∃ S : E → C(Time,E), S (w (clamp 0)) = w ∧ ContDiffAt ℝ 1 S (w (clamp 0)) ∧
      ∀ᶠ a in 𝓝 (w (clamp 0)), (∀ t, S a t ∈ U) ∧
        ∀ t : Time, S a t = a + ∫ r in (0:ℝ)..(t:ℝ), X (S a (clamp r)) := by
  obtain ⟨Y,V,cy,ov,contains,sub,agree⟩ := compact_smooth_extension U (range w) openU
    (isCompact_range w.continuous) (range_nonempty _) (range_subset_iff.mpr inside) X cx
  let N := pathField Y cy.continuous
  let H (z : C(Time,E)) := z - integralPath (N z)
  let I : E →L[ℝ] C(Time,E) := ContinuousLinearMap.const ℝ Time
  have cH : ContDiff ℝ 1 H := contDiff_id.sub ((integralPath (F := E)).contDiff.comp (pathField_smooth Y cy))
  have cd : Continuous (fderiv ℝ Y) := (cy.fderiv_right (m := 0) (by decide)).continuous
  let D := pathField (fderiv ℝ Y) cd w
  have dN : HasFDerivAt N (PathCalculus.multiplier Time E E D) w :=
    PathCalculus.hasFDerivAt_subst (liftField Y cy.continuous) (liftField (fderiv ℝ Y) cd)
      (fun _ x => (cy.differentiable (by decide) x).hasFDerivAt) w
  have dH : HasFDerivAt H (1 - pathVolterra D) w :=
    (hasFDerivAt_id w).sub ((integralPath (F := E)).hasFDerivAt.comp w dN)
  obtain ⟨g,ge⟩ := volterra_isUnit D
  let B := ContinuousLinearEquiv.unitsEquiv ℝ (C(Time,E)) g
  have dh : HasFDerivAt H B.toContinuousLinearMap w := by
    change HasFDerivAt H (g : C(Time,E) →L[ℝ] C(Time,E)) w
    rwa [ge]
  let T := cH.contDiffAt.toOpenPartialHomeomorph H dh (by decide)
  have src : w ∈ T.source := cH.contDiffAt.mem_toOpenPartialHomeomorph_source dh (by decide)
  have tgt := T.map_source src
  have inv : ContDiffAt ℝ 1 T.symm (H w) := cH.contDiffAt.to_localInverse dh (by decide)
  let q := w (clamp 0)
  have base : H w = I q := by
    ext t : 1
    change w t-(∫ r in (0:ℝ)..(t:ℝ), Y (w (clamp r))) = q
    have equal (r : ℝ) : Y (w (clamp r)) = X (w (clamp r)) := agree (contains (mem_range_self _))
    simp_rw [equal]
    exact sub_eq_iff_eq_add.mpr (eq t)
  let S := T.symm ∘ I
  have root : S q = w := by
    change T.symm (I q) = w
    rw [← base]; exact T.left_inv src
  have cs : ContDiffAt ℝ 1 S q := (base ▸ inv).comp q I.contDiff.contDiffAt
  have stay : {z : C(Time,E) | MapsTo z univ V} ∈ 𝓝 (S q) := by
    rw [root]
    exact (ContinuousMap.isOpen_setOf_mapsTo isCompact_univ ov).mem_nhds (fun t _ => contains (mem_range_self t))
  have pin : I q ∈ T.target := base ▸ tgt
  refine ⟨S,root,cs,?_⟩
  filter_upwards [cs.continuousAt stay,I.continuous.continuousAt (T.open_target.mem_nhds pin)] with a good hit
  refine ⟨fun t => sub (good (mem_univ t)),fun t => ?_⟩
  have result := congrArg (fun z : C(Time,E) => z t) (T.right_inv hit)
  change S a t-(∫ r in (0:ℝ)..(t:ℝ), Y (S a (clamp r))) = a at result
  have equal (r : ℝ) : Y (S a (clamp r)) = X (S a (clamp r)) := agree (good (mem_univ _))
  simp_rw [equal] at result
  exact sub_eq_iff_eq_add.mp result

#print axioms orbit_path_dependence
end MinimizingSard.Five
