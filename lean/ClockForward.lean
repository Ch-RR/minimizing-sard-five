import ArcLengthClock
import CompactPathField

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace MinimizingSard.Five
open Volterra
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem continuousOn_arcClock {ν : ℝ → ℝ} (iv : IntervalIntegrable ν volume 0 1) :
    ContinuousOn (arcClock ν) (Icc 0 1) := by
  simpa only [arcClock,uIcc_of_le zero_le_one] using
    intervalIntegral.continuousOn_primitive_interval' iv (left_mem_uIcc : (0:ℝ) ∈ uIcc 0 1)

/-- Run an ordinary arc at the clock of the measured control. The integral
formula is valid at every time, including the endpoints of all pauses. -/
theorem forward_clock (ν : ℝ → ℝ) (iv : IntervalIntegrable ν volume 0 1) (nn : ∀ t, 0 ≤ ν t)
    (f v : ℝ → E) (cv : ContinuousOn v (Icc 0 (arcClock ν 1)))
    (df : ∀ s ∈ Icc 0 (arcClock ν 1), HasDerivWithinAt f (v s) (Icc 0 (arcClock ν 1)) s) :
    ∀ t ∈ Icc (0:ℝ) 1, f (arcClock ν t) = f 0 + ∫ r in (0:ℝ)..t, ν r • v (arcClock ν r) := by
  let S := arcClock ν
  let L := S 1
  have maps : MapsTo S (Icc 0 1) (Icc 0 L) := image_subset_iff.mp (clock_range ν iv nn).2.subset
  have zero : S 0 = 0 := by simp [S,arcClock]
  have cf := continuousOn_arcClock iv
  have pos : 0 ≤ L := intervalIntegral.integral_nonneg_of_forall zero_le_one nn
  obtain ⟨B,bd⟩ := isCompact_Icc.bddAbove_image cv.norm
  have bound (s) (hs : s ∈ Icc 0 L) : ‖v s‖ ≤ B := bd (mem_image_of_mem _ hs)
  have domS : DominatedPath S := dominatedPath_of_primitive S ν iv (fun t _ => by simp [S,arcClock])
  have dom := domS.map_bound (f ∘ S) B ((norm_nonneg _).trans (bound 0 (left_mem_Icc.mpr pos)))
    (fun a ha b hb _ => by
      simpa only [dist_eq_norm,Function.comp_apply] using
        (convex_Icc (0:ℝ) L).norm_image_sub_le_of_norm_hasDerivWithin_le df bound (maps ha) (maps hb))
  have cs : ContinuousOn (v ∘ S) (Icc 0 1) := cv.comp cf maps
  have vel := iv.smul_continuousOn (by simpa only [uIcc_of_le zero_le_one] using cs)
  have deriv : ∀ᵐ t ∂volume.restrict (Ioo (0:ℝ) 1), HasDerivAt (f ∘ S) (ν t • v (S t)) t := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [iv.ae_hasDerivAt_integral] with t h ht
    have ti := Ioo_subset_Icc_self ht
    have dS : HasDerivAt S (ν t) t := h (by rw [uIcc_of_le zero_le_one]; exact ti) 0 left_mem_uIcc
    exact ((df _ (maps ti)).scomp t dS.hasDerivWithinAt maps).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  simpa only [Function.comp_apply,zero] using dom.integral _ vel deriv

/-- A continuous primitive on the model interval has the prescribed
one-sided derivatives at both ends. -/
theorem time_primitive_derivative (w : C(Time,E)) (b : C(Time,E)) (q : E)
    (eq : ∀ t : Time, w t = q + ∫ r in (0:ℝ)..(t:ℝ), b (clamp r)) :
    ∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt (fun r => w (clamp r)) (b (clamp t)) (Icc 0 1) t := by
  have cb := b.continuous.comp (show Continuous clamp from continuous_projIcc)
  have val (t) (ht : t ∈ Icc (0:ℝ) 1) : w (clamp t) = q + ∫ r in (0:ℝ)..t, b (clamp r) := by
    simpa only [clamp,projIcc_of_mem zero_le_one ht] using eq ⟨t,ht⟩
  intro t ht
  have d := intervalIntegral.integral_hasDerivAt_right (cb.intervalIntegrable 0 t)
    cb.aestronglyMeasurable.stronglyMeasurableAtFilter cb.continuousAt
  exact (d.const_add q).hasDerivWithinAt.congr_of_mem val ht

/-- Integrate a continuous derivative confined to a closed time interval. -/
theorem time_derivative_primitive (w b : C(Time,E))
    (d : ∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt (fun r => w (clamp r)) (b (clamp t)) (Icc 0 1) t) :
    ∀ t : Time, w t = w (clamp 0) + ∫ r in (0:ℝ)..(t:ℝ), b (clamp r) := by
  intro t
  have cb := b.continuous.comp (show Continuous clamp from continuous_projIcc)
  have cf := w.continuous.comp (show Continuous clamp from continuous_projIcc)
  have dif := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le t.property.1 cf.continuousOn
    (fun r hr => (d r ⟨hr.1.le,hr.2.le.trans t.property.2⟩).hasDerivAt
      (Icc_mem_nhds hr.1 (hr.2.trans_le t.property.2))) (cb.intervalIntegrable 0 t)
  simp only [dif,Function.comp_apply,show clamp (t:ℝ) = t from projIcc_val zero_le_one t]
  abel

#print axioms forward_clock
#print axioms time_primitive_derivative
#print axioms time_derivative_primitive
end MinimizingSard.Five
