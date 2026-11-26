import LengthMultiplier
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

noncomputable section
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace
namespace MinimizingSard.Five

/-- A Hilbert-space subgradient of the time-integrated Euclidean speed has
unit-ball density and is aligned with the original velocity on the same clock. -/
theorem norming_control_density {α E : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (w : Lp E 2 μ) (B : Lp E 2 μ →L[ℝ] ℝ)
    (support : ∀ v : Lp E 2 μ, (∫ t, ‖w t‖ ∂μ) + B (v-w) ≤ ∫ t, ‖v t‖ ∂μ) :
    ∃ a : Lp E 2 μ, (∀ v : Lp E 2 μ, B v = ∫ t, ⟪a t,v t⟫_ℝ ∂μ) ∧
      ∀ᵐ t ∂μ, ‖a t‖ ≤ 1 ∧ w t = ‖w t‖ • a t := by
  let a := (InnerProductSpace.toDual ℝ (Lp E 2 μ)).symm B
  have rep (v : Lp E 2 μ) : B v = ∫ t, ⟪a t,v t⟫_ℝ ∂μ := by
    rw [← InnerProductSpace.toDual_symm_apply (x := v) (y := B)]
    rfl
  have two : (∫ t, ‖(w+w) t‖ ∂μ) = (∫ t, ‖w t‖ ∂μ) + ∫ t, ‖w t‖ ∂μ := by
    rw [← integral_add ((Lp.memLp w).integrable (by norm_num)).norm ((Lp.memLp w).integrable (by norm_num)).norm]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add w w] with t ht
    rw [ht,Pi.add_apply,← two_smul ℝ,norm_smul]
    simp [two_mul]
  have zero : (∫ t, ‖(0 : Lp E 2 μ) t‖ ∂μ) = 0 := by
    trans ∫ _ : α, (0:ℝ) ∂μ
    · apply integral_congr_ae
      filter_upwards [Lp.coeFn_zero E 2 μ] with t ht
      exact (congrArg norm (show (0 : Lp E 2 μ) t = 0 from ht)).trans norm_zero
    · simp
  have under := support 0
  rw [zero_sub,map_neg,zero] at under
  have over := support (w+w)
  rw [add_sub_cancel_right,two] at over
  have tight : B w = ∫ t, ‖w t‖ ∂μ := by linarith
  have dom (v : Lp E 2 μ) : (∫ t, ⟪a t,v t⟫_ℝ ∂μ) ≤ ∫ t, ‖v t‖ ∂μ := by
    have h := support v
    rw [map_sub,← tight] at h
    rw [← rep]; linarith
  have bound : ∀ᵐ t ∂μ, ‖a t‖ ≤ 1 := by
    have loc : (fun t => ⟪a t,a t⟫_ℝ) ≤ᵐ[μ] (fun t => ‖a t‖) := by
      apply ae_le_of_forall_setIntegral_le (L2.integrable_inner a a) ((Lp.memLp a).integrable (by norm_num)).norm
      intro s hs _
      let h := (Lp.memLp a).indicator hs
      let v := h.toLp (s.indicator a)
      have eq : ⇑v =ᵐ[μ] s.indicator a := h.coeFn_toLp
      have left : (∫ t, ⟪a t,v t⟫_ℝ ∂μ) = ∫ t in s, ⟪a t,a t⟫_ℝ ∂μ := by
        rw [← integral_indicator hs]
        apply integral_congr_ae
        filter_upwards [eq] with t ht
        by_cases mem : t ∈ s <;> simp [ht,mem]
      have right : (∫ t, ‖v t‖ ∂μ) = ∫ t in s, ‖a t‖ ∂μ := by
        rw [← integral_indicator hs]
        apply integral_congr_ae
        filter_upwards [eq] with t ht
        by_cases mem : t ∈ s <;> simp [ht,mem]
      simpa only [← left,← right] using dom v
    filter_upwards [loc] with t ht
    change ⟪a t,a t⟫_ℝ ≤ ‖a t‖ at ht
    rw [real_inner_self_eq_norm_sq] at ht
    by_contra! big
    nlinarith only [ht,mul_pos (sub_pos.mpr big) (zero_lt_one.trans big)]
  have below : (fun t => ⟪a t,w t⟫_ℝ) ≤ᵐ[μ] fun t => ‖w t‖ := bound.mono fun t ht =>
    (real_inner_le_norm _ _).trans (mul_le_of_le_one_left (norm_nonneg _) ht)
  have ieq : (∫ t, ⟪a t,w t⟫_ℝ ∂μ) = ∫ t, ‖w t‖ ∂μ := (rep w).symm.trans tight
  have eq := (integral_eq_iff_of_ae_le (L2.integrable_inner a w)
    ((Lp.memLp w).integrable (by norm_num)).norm below).mp ieq
  refine ⟨a,rep,?_⟩
  filter_upwards [bound,eq] with t ht h
  refine ⟨ht,sub_eq_zero.mp (norm_eq_zero.mp ?_)⟩
  change ⟪a t,w t⟫_ℝ = ‖w t‖ at h
  have sq := norm_sub_sq_real (w t) (‖w t‖ • a t)
  rw [real_inner_smul_right,real_inner_comm,h,norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)] at sq
  have le := mul_le_of_le_one_right (norm_nonneg (w t)) ht
  have lo := (neg_nonpos.mpr (norm_nonneg (w t))).trans (mul_nonneg (norm_nonneg (w t)) (norm_nonneg (a t)))
  nlinarith only [sq,sq_le_sq' lo le,sq_nonneg ‖w t-‖w t‖ • a t‖]

#print axioms norming_control_density

end MinimizingSard.Five
