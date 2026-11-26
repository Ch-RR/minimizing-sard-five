import MeasuredVolterra

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace MinimizingSard.Five
open Volterra
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def TimePrimitive (w : C(Time,E)) (a : E) (v : ℝ → E) : Prop :=
  IntervalIntegrable v volume 0 1 ∧ ∀ t : Time, w t = a + ∫ r in (0:ℝ)..(t:ℝ), v r

omit [FiniteDimensional ℝ E] in
theorem TimePrimitive.at_zero {w : C(Time,E)} {a v} (h : TimePrimitive w a v) : w (clamp 0) = a := by
  simpa [clamp] using h.2 (clamp 0)

omit [FiniteDimensional ℝ E] in
theorem TimePrimitive.dominated {w : C(Time,E)} {a v} (h : TimePrimitive w a v) :
    DominatedPath (fun r => w (clamp r)) := by
  apply dominatedPath_of_primitive _ v h.1
  intro t ht
  rw [h.at_zero,show clamp t = ⟨t,ht⟩ from projIcc_of_mem _ ht]
  exact h.2 _

/-- Differentiate a Bochner primitive in any finite-dimensional real model,
using the scalar Lebesgue differentiation theorem in a finite basis. -/
theorem TimePrimitive.ae_derivative {w : C(Time,E)} {a v} (h : TimePrimitive w a v) :
    ∀ᵐ t ∂volume.restrict (Ioo (0:ℝ) 1), HasDerivAt (fun r => w (clamp r)) (v t) t := by
  let A := (Module.finBasis ℝ E).equivFun.toContinuousLinearEquiv
  let L (i : Fin (Module.finrank ℝ E)) := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (Module.finrank ℝ E) => ℝ) i).comp A.toContinuousLinearMap
  have each (i) : IntervalIntegrable (fun r => L i (v r)) volume 0 1 :=
    ⟨(L i).integrable_comp h.1.1,(L i).integrable_comp h.1.2⟩
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [ae_all_iff.mpr (fun i => (each i).ae_hasDerivAt_integral)] with t dif ht
  have d : HasDerivAt (fun r => A (w (clamp r))) (A (v t)) t := by
    apply hasDerivAt_pi.mpr
    intro i
    have di := (dif i (by rw [uIcc_of_le zero_le_one]; exact Ioo_subset_Icc_self ht) 0 left_mem_uIcc).const_add (L i a)
    apply di.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
    have hr' := Ioo_subset_Icc_self hr
    have sub := h.1.mono_set (show uIcc (0:ℝ) r ⊆ uIcc 0 1 by
      rw [uIcc_of_le hr.1.le,uIcc_of_le zero_le_one]; exact Icc_subset_Icc le_rfl hr.2.le)
    change L i (w (clamp r)) = _
    rw [show clamp r = ⟨r,hr'⟩ from projIcc_of_mem _ hr',h.2 ⟨r,hr'⟩,map_add,(L i).intervalIntegral_comp_comm sub]
  have result := A.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t d
  change HasDerivAt (fun r => A.symm (A (w (clamp r)))) (A.symm (A (v t))) t at result
  simpa only [A.symm_apply_apply] using result

/-- Integration by parts for the pairing of two absolutely continuous paths.
Both paths have true integral primitives, allowing measurable L² controls. -/
theorem time_pairing {w : C(Time,E)} {p : C(Time,E →L[ℝ] ℝ)} {a α v b}
    (hw : TimePrimitive w a v) (hp : TimePrimitive p α b) (f : ℝ → ℝ)
    (iv : IntervalIntegrable f volume 0 1)
    (rule : ∀ᵐ r ∂volume.restrict (Ioo (0:ℝ) 1), b r (w (clamp r)) + p (clamp r) (v r) = f r) :
    ∀ t : Time, p t (w t) = α a + ∫ r in (0:ℝ)..(t:ℝ), f r := by
  let W (r : ℝ) := w (clamp r)
  let P (r : ℝ) := p (clamp r)
  have dom := hp.dominated.prod hw.dominated
  have pair : DominatedPath (fun r => P r (W r)) := by
    apply dom.map_bound _ (‖p‖+‖w‖) (add_nonneg (norm_nonneg p) (norm_nonneg w))
    intro s _ t _ _
    let d := dist (P t,W t) (P s,W s)
    have h₁ : ‖P t-P s‖ ≤ d := by change ‖P t-P s‖ ≤ max (dist (P t) (P s)) _; rw [← dist_eq_norm]; exact le_max_left _ _
    have h₂ : ‖W t-W s‖ ≤ d := by change ‖W t-W s‖ ≤ max _ (dist (W t) (W s)); rw [← dist_eq_norm]; exact le_max_right _ _
    have split : P t (W t)-P s (W s) = (P t-P s) (W t) + P s (W t-W s) := by simp only [ContinuousLinearMap.sub_apply,map_sub]; abel
    rw [dist_eq_norm,split]
    calc _ ≤ ‖(P t-P s) (W t)‖+‖P s (W t-W s)‖ := norm_add_le _ _
         _ ≤ ‖P t-P s‖*‖W t‖+‖P s‖*‖W t-W s‖ := add_le_add ((P t-P s).le_opNorm _) ((P s).le_opNorm _)
         _ ≤ d*‖w‖ + ‖p‖*d := add_le_add (mul_le_mul h₁ (w.norm_coe_le_norm _) (norm_nonneg _) dist_nonneg)
           (mul_le_mul (p.norm_coe_le_norm _) h₂ (norm_nonneg _) (norm_nonneg p))
         _ = (‖p‖+‖w‖)*d := by ring
  have eq := pair.integral f iv (by
    filter_upwards [hp.ae_derivative,hw.ae_derivative,rule] with r pd wd hr
    have d := pd.clm_apply wd
    simpa only [P,W,hr,add_comm] using d)
  intro t
  simpa only [P,W,hp.at_zero,hw.at_zero,show clamp (t:ℝ) = t from projIcc_val zero_le_one t] using eq t t.property

#print axioms TimePrimitive.ae_derivative
#print axioms time_pairing
end MinimizingSard.Five
