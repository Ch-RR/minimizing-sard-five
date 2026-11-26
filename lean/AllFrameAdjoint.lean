import FrameFirstVariation
import LinearInputAdjoint
import NormalArc

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace MinimizingSard.Five
open Volterra
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] {m : ℕ}

theorem frame_adjoint_representation (e : Frame M m) (u : Control m) {x y : M} (seg : Segment e u x y)
    (G : State × Control m → State) (dg : DifferentiableAt ℝ G (e.chart x,u))
    (gr : ∀ᶠ b in 𝓝 (e.chart x,u), b.1 ∈ e.chart.target ∧ G b ∈ e.chart.target ∧
      ∀ t, Segment e b.2 (e.chart.symm b.1) t ↔ t = e.chart.symm (G b))
    (η : State →L[ℝ] ℝ) :
    ∃ (w : C(Time,State)) (p : C(Time,State →L[ℝ] ℝ)), e.Solves u (e.chart x) w ∧
      w (clamp 1) = e.chart y ∧ p (clamp 1) = η ∧
      TimePrimitive p (p (clamp 0))
        (fun r => -(p (clamp r)).comp ((fderiv ℝ e.coefficient (w (clamp r))).flip (u r))) ∧
      ∀ h : State × Control m, η (fderiv ℝ G (e.chart x,u) h) = p (clamp 0) h.1 +
        ∫ r in (0:ℝ)..1, ∑ i, h.2 r i * p (clamp r) (e.X i (w (clamp r))) := by
  obtain ⟨w,hw,wy,D,reg,vars⟩ := frame_segment_differential e u seg G dg gr
  obtain ⟨p,pη,hp⟩ := terminal_linear_adjoint D (frameSignal m u) η
  have pd : TimePrimitive p (p (clamp 0))
      (fun r => -(p (clamp r)).comp ((fderiv ℝ e.coefficient (w (clamp r))).flip (u r))) := by
    simpa only [reg,frameSignal_apply] using hp
  refine ⟨w,p,hw,wy,pη,pd,fun h => ?_⟩
  obtain ⟨z,zh,hz⟩ := vars h
  let X : C(Time,Fiber m →L[ℝ] State) := ⟨fun t => e.coefficient (w t),
    e.coefficient_smooth.continuousOn.comp_continuous w.continuous hw.1⟩
  let B : C(Time,Fiber m →L[ℝ] ℝ) := ⟨fun t => (p t).comp (X t),p.continuous.clm_comp X.continuous⟩
  let f (r : ℝ) := B (clamp r) (frameSignal m h.2 r)
  have temp := time_pairing hz hp f (Volterra.intervalIntegrable B (frameSignal m h.2)) (by
    apply Filter.Eventually.of_forall
    intro r
    change -(p (clamp r) (D (clamp r) (z (clamp r)) (frameSignal m u r))) +
      p (clamp r) (D (clamp r) (z (clamp r)) (u r) + e.velocity (w (clamp r)) (h.2 r)) =
      p (clamp r) (e.coefficient (w (clamp r)) (frameSignal m h.2 r))
    rw [frameSignal_apply,frameSignal_apply,map_add,Frame.coefficient_apply]
    abel) (clamp 1)
  have rep (r : ℝ) : f r = ∑ i, h.2 r i * p (clamp r) (e.X i (w (clamp r))) := by
    change p (clamp r) (e.coefficient (w (clamp r)) (frameSignal m h.2 r)) = _
    simp only [frameSignal_apply,Frame.coefficient_apply,Frame.velocity,map_sum,map_smul,smul_eq_mul]
  simpa only [zh,pη,rep,show ((clamp 1):ℝ) = 1 by simp [clamp]] using temp

private theorem coefficient_derivative_apply (e : Frame M m) (q : State) (inside : q ∈ e.chart.target) (v : Fiber m) :
    (fderiv ℝ e.coefficient q).flip v = ∑ i, v i • fderiv ℝ (e.X i) q := by
  let A := ContinuousLinearMap.apply ℝ State v
  have de := (e.coefficient_smooth.contDiffAt (e.chart.open_target.mem_nhds inside)).differentiableAt (by simp)
  have d₁ := A.hasFDerivAt.comp q de.hasFDerivAt
  have d₂ := HasFDerivAt.sum (u := Finset.univ) (fun i _ =>
    (((e.smooth i).contDiffAt (e.chart.open_target.mem_nhds inside)).differentiableAt (by simp)).hasFDerivAt.const_smul (v i))
  have same : A ∘ e.coefficient = fun z => ∑ i, v i • e.X i z :=
    funext (fun z => e.coefficient_apply z v)
  rw [same] at d₁
  apply d₁.unique (d₂.congr_of_eventuallyEq _)
  exact .of_forall fun z => by simp only [Finset.sum_apply,Pi.smul_apply]

/-- A supporting length row gives the Hamilton equations on an entire original
frame segment, for arbitrary rank, with its actual measurable clock. -/
theorem all_frame_normal_piece (e : Frame M m) (u : Control m) {x y : M} (seg : Segment e u x y)
    (G : State × Control m → State) (dg : DifferentiableAt ℝ G (e.chart x,u))
    (gr : ∀ᶠ b in 𝓝 (e.chart x,u), b.1 ∈ e.chart.target ∧ G b ∈ e.chart.target ∧
      ∀ t, Segment e b.2 (e.chart.symm b.1) t ↔ t = e.chart.symm (G b))
    (η : State →L[ℝ] ℝ)
    (support : ∀ v, pieceLength u+η (fderiv ℝ G (e.chart x,u) (0,v-u)) ≤ pieceLength v) :
    ∃ Z : C(Time,Phase), NormalPiece e u Z ∧ (Z (clamp 0)).1 = e.chart x ∧
      Z (clamp 1) = (e.chart y,η) ∧ ∀ h, (Z (clamp 0)).2 h = η (fderiv ℝ G (e.chart x,u) (h,0)) := by
  obtain ⟨w,p,hw,wy,pη,hp,rep⟩ := frame_adjoint_representation e u seg G dg gr η
  let Z : C(Time,Phase) := ⟨fun t => (w t,p t),w.continuous.prodMk p.continuous⟩
  let ν (t : ℝ) := Real.sqrt (speedSq (u t))
  let B := (η.comp (fderiv ℝ G (e.chart x,u))).comp (ContinuousLinearMap.inr ℝ State (Control m))
  let b : C(Time,Fiber m) := ⟨fun t i => p t (e.X i (w t)),continuous_pi fun i => p.continuous.clm_apply
    ((e.smooth i).continuousOn.comp_continuous w.continuous hw.1)⟩
  have align := explicit_support_alignment u B b support (fun v => by simpa using rep (0,v))
  let C : C(Time,Fiber m →L[ℝ] State) := ⟨fun t => e.coefficient (w t),
    e.coefficient_smooth.continuousOn.comp_continuous w.continuous hw.1⟩
  let vel (r : ℝ) := C (clamp r) (frameSignal m u r)
  have pw : TimePrimitive w (e.chart x) vel := ⟨Volterra.intervalIntegrable C (frameSignal m u),hw.2⟩
  have cs : Continuous (fun r => Z (clamp r)) := Z.continuous.comp continuous_projIcc
  have ch : Continuous (fun r => hamiltonianField e.X (Z (clamp r))) := continuous_iff_continuousAt.mpr
    (fun r => (hamiltonianField_smoothAt e _ (hw.1 _)).continuousAt.comp (x := r) cs.continuousAt)
  refine ⟨Z,⟨hw.1,align,?_⟩,pw.at_zero,Prod.ext wy pη,fun h => ?_⟩
  · apply (pw.dominated.prod hp.dominated).integral
    · exact (original_speed_integrable u).smul_continuousOn ch.continuousOn
    · filter_upwards [pw.ae_derivative,hp.ae_derivative,ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self align] with r dw dp a
      have d := dw.prodMk dp
      convert d using 1
      apply Prod.ext
      · change ν r • (∑ i, normalCoefficients e.X (Z (clamp r)) i • e.X i (w (clamp r))) = e.coefficient (w (clamp r)) (frameSignal m u r)
        rw [frameSignal_apply,Frame.coefficient_apply,a]
        simp only [ν,Z,b,normalCoefficients,Frame.velocity,Finset.smul_sum,Pi.smul_apply,smul_eq_mul,mul_smul,
          ContinuousMap.coe_mk]
      · change ν r • (-(∑ i, normalCoefficients e.X (Z (clamp r)) i • (p (clamp r)).comp (fderiv ℝ (e.X i) (w (clamp r))))) =
          -(p (clamp r)).comp ((fderiv ℝ e.coefficient (w (clamp r))).flip (u r))
        rw [coefficient_derivative_apply e _ (hw.1 _) (u r),a]
        ext h
        simp only [ν,Z,b,normalCoefficients,Finset.smul_sum,smul_neg,Pi.smul_apply,smul_eq_mul,mul_smul,
          ContinuousLinearMap.neg_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.sum_apply,map_sum,map_smul,ContinuousMap.coe_mk]
  · have h0 := rep (h,(0:Control m))
    have zero : (fun r => ∑ i, (0:Control m) r i * p (clamp r) (e.X i (w (clamp r)))) =ᵐ[volume.restrict (uIoc (0:ℝ) 1)] 0 := by
      rw [uIoc_of_le zero_le_one,Measure.restrict_congr_set Ioc_ae_eq_Icc]
      filter_upwards [Lp.coeFn_zero (Fiber m) 2 controlMeasure] with r hr
      change (0:Control m) r = 0 at hr
      simp
    rw [intervalIntegral.integral_congr_ae_restrict zero] at h0
    simpa using h0.symm

#print axioms frame_adjoint_representation
#print axioms all_frame_normal_piece
end MinimizingSard.Five
