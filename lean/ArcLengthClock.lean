import IntegralClock
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace MinimizingSard.Five

def arcClock (ν : ℝ → ℝ) (t : ℝ) := ∫ r in (0:ℝ)..t, ν r

private theorem clock_subint {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (hf : IntervalIntegrable f volume 0 1) {a b : ℝ} (ha : 0 ≤ a) (ab : a ≤ b) (hb : b ≤ 1) :
    IntervalIntegrable f volume a b := hf.mono_set (by
  rw [uIcc_of_le ab,uIcc_of_le zero_le_one]; exact Icc_subset_Icc ha hb)

theorem clock_range (ν : ℝ → ℝ) (iv : IntervalIntegrable ν volume 0 1) (nn : ∀ t, 0 ≤ ν t) :
    MonotoneOn (arcClock ν) (Icc 0 1) ∧ arcClock ν '' Icc 0 1 = Icc 0 (arcClock ν 1) := by
  let S := arcClock ν
  have mono : MonotoneOn S (Icc (0:ℝ) 1) := by
    intro a ha b hb ab
    have d := intervalIntegral.integral_add_adjacent_intervals (clock_subint iv le_rfl ha.1 ha.2)
      (clock_subint iv ha.1 ab hb.2)
    have pos := intervalIntegral.integral_nonneg_of_forall (μ := volume) ab nn
    change (∫ r in (0:ℝ)..a, ν r) ≤ ∫ r in (0:ℝ)..b, ν r
    linarith
  have zero : S 0 = 0 := by simp [S,arcClock]
  have cs : ContinuousOn S (Icc (0:ℝ) 1) := by
    simpa only [S,arcClock,uIcc_of_le zero_le_one] using
      (intervalIntegral.continuousOn_primitive_interval' iv (left_mem_uIcc : (0:ℝ) ∈ uIcc 0 1))
  refine ⟨mono,Subset.antisymm ?_ ?_⟩
  · rintro s ⟨t,ht,rfl⟩
    exact ⟨zero ▸ mono (left_mem_Icc.mpr zero_le_one) ht ht.1,mono ht (right_mem_Icc.mpr zero_le_one) ht.2⟩
  · simpa only [zero] using intermediate_value_Icc zero_le_one cs

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Factor a variable-speed integral path through elapsed arclength. The factor
is Lipschitz, even when the speed vanishes on a set of positive measure. -/
theorem clock_factor (ν : ℝ → ℝ) (iv : IntervalIntegrable ν volume 0 1) (nn : ∀ t, 0 ≤ ν t)
    (z v : ℝ → E) (cv : ContinuousOn v (Icc 0 1))
    (eq : ∀ t ∈ Icc (0:ℝ) 1, z t = z 0 + ∫ r in (0:ℝ)..t, ν r • v r) :
    ∃ (y : ℝ → E) (K : ℝ≥0), LipschitzWith K y ∧ (∀ s, y s ∈ z '' Icc 0 1) ∧
      ∀ t ∈ Icc 0 1, y (arcClock ν t) = z t := by
  let S := arcClock ν
  obtain ⟨mono,image⟩ := clock_range ν iv nn
  obtain ⟨B,bound⟩ := isCompact_Icc.bddAbove_image cv.norm
  let K := Real.toNNReal B
  have bd t (ht : t ∈ Icc (0:ℝ) 1) : ‖v t‖ ≤ (K:ℝ) := (bound (mem_image_of_mem _ ht)).trans (Real.le_coe_toNNReal B)
  have vel := iv.smul_continuousOn (by simpa only [uIcc_of_le zero_le_one] using cv)
  have ord (a b : ℝ) (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) (ab : a ≤ b) :
      dist (z b) (z a) ≤ (K:ℝ) * dist (S b) (S a) := by
    rw [dist_eq_norm,eq b hb,eq a ha,add_sub_add_left_eq_sub,
      intervalIntegral.integral_interval_sub_left (clock_subint vel le_rfl hb.1 hb.2) (clock_subint vel le_rfl ha.1 ha.2),
      Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr (mono ha hb ab))]
    change _ ≤ (K:ℝ) * ((∫ r in (0:ℝ)..b, ν r)-(∫ r in (0:ℝ)..a, ν r))
    rw [intervalIntegral.integral_interval_sub_left (clock_subint iv le_rfl hb.1 hb.2) (clock_subint iv le_rfl ha.1 ha.2),
      ← intervalIntegral.integral_const_mul]
    apply (intervalIntegral.norm_integral_le_integral_norm ab).trans
    apply intervalIntegral.integral_mono_on ab (clock_subint vel ha.1 ab hb.2).norm ((clock_subint iv ha.1 ab hb.2).const_mul _)
    intro r hr
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (nn r),mul_comm (K:ℝ)]
    exact mul_le_mul_of_nonneg_left (bd r ⟨ha.1.trans hr.1,hr.2.trans hb.2⟩) (nn r)
  have anyPair (a b : ℝ) (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) :
      dist (z a) (z b) ≤ (K:ℝ)*dist (S a) (S b) := by
    rcases le_total b a with h | h
    · exact ord b a hb ha h
    · simpa only [dist_comm (z b),dist_comm (S b)] using ord a b ha hb h
  let L := S 1
  have pos : 0 ≤ L := intervalIntegral.integral_nonneg_of_forall zero_le_one nn
  have pre (s : Icc 0 L) : ∃ t ∈ Icc (0:ℝ) 1, S t = s := by
    exact (Set.ext_iff.mp image (s:ℝ)).mpr s.property
  choose t ht hit using pre
  let W (s : Icc 0 L) := z (t s)
  have lip : LipschitzWith K W := LipschitzWith.of_dist_le_mul (fun a b => by
    simpa only [hit] using anyPair (t a) (t b) (ht a) (ht b))
  let y := W ∘ projIcc 0 L pos
  refine ⟨y,K,by simpa using lip.comp (LipschitzWith.projIcc pos),fun s => ⟨_,ht _,rfl⟩,?_⟩
  intro a ha
  have sa : S a ∈ Icc 0 L := image ▸ mem_image_of_mem (arcClock ν) ha
  let s : Icc 0 L := ⟨S a,sa⟩
  have h := anyPair (t s) a (ht s) ha
  rw [hit] at h
  change dist (z (t s)) (z a) ≤ (K:ℝ)*dist (S a) (S a) at h
  change z (t (projIcc 0 L pos (S a))) = z a
  rw [projIcc_of_mem pos sa]
  exact dist_le_zero.mp (by simpa only [dist_self,mul_zero] using h)

#print axioms clock_range
#print axioms clock_factor

/-- Removing a nonnegative integrable clock yields a classical autonomous
solution on the entire elapsed-time interval. This includes zero elapsed time
and clocks which are constant on subintervals. -/
theorem autonomous_arc [FiniteDimensional ℝ E] (ν : ℝ → ℝ) (iv : IntervalIntegrable ν volume 0 1)
    (nn : ∀ t, 0 ≤ ν t) (z : ℝ → E) (cz : ContinuousOn z (Icc 0 1)) (X : E → E)
    (cx : ContinuousOn X (z '' Icc 0 1))
    (eq : ∀ t ∈ Icc (0:ℝ) 1, z t = z 0 + ∫ r in (0:ℝ)..t, ν r • X (z r)) :
    ∃ y : ℝ → E, Continuous y ∧ (∀ s, y s ∈ z '' Icc 0 1) ∧
      (∀ t ∈ Icc 0 1, y (arcClock ν t) = z t) ∧
      ∀ s ∈ Icc 0 (arcClock ν 1), HasDerivWithinAt y (X (y s)) (Icc 0 (arcClock ν 1)) s := by
  have cv : ContinuousOn (fun r => X (z r)) (Icc 0 1) := cx.comp cz (mapsTo_image _ _)
  obtain ⟨y,K,ly,im,yz⟩ := clock_factor ν iv nn z _ cv eq
  let S := arcClock ν
  let g := X ∘ y
  have cg : Continuous g := cx.comp_continuous ly.continuous im
  let F (s : ℝ) := ∫ r in (0:ℝ)..s, g r
  have df (s : ℝ) : HasDerivAt F (g s) s := intervalIntegral.integral_hasDerivAt_right
    (cg.intervalIntegrable _ _) cg.aestronglyMeasurable.stronglyMeasurableAtFilter cg.continuousAt
  obtain ⟨B,bound⟩ := isCompact_Icc.bddAbove_image cv.norm
  have bg (s : ℝ) : ‖g s‖ ≤ B := by
    obtain ⟨t,ht,he⟩ := im s
    change ‖X (y s)‖ ≤ B
    rw [← he]
    exact bound (mem_image_of_mem _ ht)
  have ef (a b : ℝ) : dist (F a) (F b) ≤ B * dist a b := by
    rw [dist_eq_norm,Real.dist_eq]
    change ‖(∫ r in (0:ℝ)..a, g r)-(∫ r in (0:ℝ)..b, g r)‖ ≤ _
    rw [intervalIntegral.integral_interval_sub_left (cg.intervalIntegrable _ _) (cg.intervalIntegrable _ _)]
    simpa only [mul_comm B] using (intervalIntegral.norm_integral_le_of_norm_le_const (a := b) (b := a) (fun s _ => bg s))
  have zero : S 0 = 0 := by simp [S,arcClock]
  have dz : DominatedPath S := dominatedPath_of_primitive S ν iv (by intro t _; simp [S,arcClock])
  have dF := dz.map_bound (F ∘ S) B ((norm_nonneg _).trans (bg 0)) (fun a _ b _ _ => ef _ _)
  have dS : ∀ᵐ t ∂volume.restrict (Ioo (0:ℝ) 1), HasDerivAt S (ν t) t := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [iv.ae_hasDerivAt_integral] with t h ht
    exact h (by rw [uIcc_of_le zero_le_one]; exact ⟨ht.1.le,ht.2.le⟩) 0 left_mem_uIcc
  have vel := iv.smul_continuousOn (by simpa only [uIcc_of_le zero_le_one] using cv)
  have ep := dF.integral _ vel (by
    filter_upwards [dS,ae_restrict_mem measurableSet_Ioo] with t ht int
    have val : g (S t) = X (z t) := congrArg X (yz t ⟨int.1.le,int.2.le⟩)
    exact val ▸ (df (S t)).scomp t ht)
  have id (s) (hs : s ∈ Icc 0 (S 1)) : y s = z 0 + F s := by
    obtain ⟨t,ht,h⟩ := (Set.ext_iff.mp (clock_range ν iv nn).2 s).mpr hs
    rw [← h,yz t ht,eq t ht]
    apply congrArg (z 0+·)
    simpa only [Function.comp_apply,zero,F,intervalIntegral.integral_same,zero_add] using (ep t ht).symm
  refine ⟨y,ly.continuous,im,yz,fun s hs => ?_⟩
  exact ((df s).const_add (z 0)).hasDerivWithinAt.congr id (id s hs)

#print axioms autonomous_arc
end
end MinimizingSard.Five
