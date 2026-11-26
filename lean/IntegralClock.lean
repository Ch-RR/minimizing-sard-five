import MovingIntegralEquation
import Mathlib.LinearAlgebra.Dual.Lemmas

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace MinimizingSard.Five

/-- A single integrable function bounds every increment on the time interval. -/
def DominatedPath {E : Type*} [PseudoMetricSpace E] (z : ℝ → E) : Prop :=
  ∃ g : ℝ → ℝ, IntervalIntegrable g volume 0 1 ∧
    ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1, s ≤ t → dist (z t) (z s) ≤ ∫ r in s..t, g r

private theorem sub_int {E : Type*} [NormedAddCommGroup E] {g : ℝ → E}
    (ig : IntervalIntegrable g volume 0 1) {s t : ℝ} (hs : 0 ≤ s) (st : s ≤ t) (ht : t ≤ 1) :
    IntervalIntegrable g volume s t := ig.mono_set (by
  rw [uIcc_of_le st,uIcc_of_le zero_le_one]
  exact Icc_subset_Icc hs ht)

theorem dominatedPath_of_primitive {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (z v : ℝ → E) (iv : IntervalIntegrable v volume 0 1)
    (eq : ∀ t ∈ Icc (0:ℝ) 1, z t = z 0 + ∫ s in (0:ℝ)..t, v s) : DominatedPath z := by
  refine ⟨fun s => ‖v s‖,iv.norm,?_⟩
  intro s hs t ht st
  rw [dist_eq_norm,eq t ht,eq s hs,add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left (sub_int iv le_rfl ht.1 ht.2) (sub_int iv le_rfl hs.1 hs.2)]
  exact intervalIntegral.norm_integral_le_integral_norm st

theorem DominatedPath.map_bound {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    {z : ℝ → E} (hz : DominatedPath z) (f : ℝ → F) (L : ℝ) (pos : 0 ≤ L)
    (bound : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1, s ≤ t →
      dist (f t) (f s) ≤ L*dist (z t) (z s)) : DominatedPath f := by
  obtain ⟨g,ig,dom⟩ := hz
  refine ⟨fun s => L*g s,ig.const_mul L,?_⟩
  intro s hs t ht st
  rw [intervalIntegral.integral_const_mul]
  exact (bound s hs t ht st).trans (mul_le_mul_of_nonneg_left (dom s hs t ht st) pos)

theorem DominatedPath.prod {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    {x : ℝ → E} {y : ℝ → F} (hx : DominatedPath x) (hy : DominatedPath y) :
    DominatedPath (fun t => (x t,y t)) := by
  obtain ⟨g,ig,dg⟩ := hx
  obtain ⟨h,ih,dh⟩ := hy
  refine ⟨fun s => g s+h s,ig.add ih,?_⟩
  intro s hs t ht st
  rw [intervalIntegral.integral_add (sub_int ig hs.1 st ht.2) (sub_int ih hs.1 st ht.2)]
  exact (max_le (le_add_of_nonneg_right (dist_nonneg (x := y t) (y := y s)))
    (le_add_of_nonneg_left (dist_nonneg (x := x t) (y := x s)))).trans
      (add_le_add (dg s hs t ht st) (dh s hs t ht st))

/-- Recover every time endpoint of a finite-dimensional path from its actual
a.e. velocity and the integrable bound on all its increments. -/
theorem DominatedPath.integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {z : ℝ → E} (hz : DominatedPath z) (v : ℝ → E) (iv : IntervalIntegrable v volume 0 1)
    (der : ∀ᵐ t ∂volume.restrict (Ioo (0:ℝ) 1), HasDerivAt z (v t) t) :
    ∀ t ∈ Icc (0:ℝ) 1, z t = z 0 + ∫ s in (0:ℝ)..t, v s := by
  obtain ⟨g,ig,dom⟩ := hz
  rw [ae_restrict_iff' measurableSet_Ioo] at der
  intro t ht
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℝ _).mp
  intro l
  let L := l.toContinuousLinearMap
  have vi := sub_int iv le_rfl ht.1 ht.2
  have integ : IntervalIntegrable (fun s => L (v s)) volume 0 t := ⟨L.integrable_comp vi.1,L.integrable_comp vi.2⟩
  have result := integral_eq_of_dominated_increments (fun s => L (z s)) (fun s => L (v s))
    (fun s => ‖L‖*g s) ht.1 integ ((sub_int ig le_rfl ht.1 ht.2).const_mul _) (by
      intro s hs r hr sr
      rw [← map_sub,← Real.norm_eq_abs,intervalIntegral.integral_const_mul]
      have b := dom s ⟨hs.1,hs.2.trans ht.2⟩ r ⟨hr.1,hr.2.trans ht.2⟩ sr
      rw [dist_eq_norm] at b
      exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left b (norm_nonneg _))) (by
      filter_upwards [der] with s hs inT using L.hasFDerivAt.comp_hasDerivAt s (hs ⟨inT.1,inT.2.trans_le ht.2⟩))
  change L (z t-(z 0+∫ s in (0:ℝ)..t, v s)) = 0
  rw [map_sub,map_add,← L.intervalIntegral_comp_comm vi]
  exact sub_eq_zero.mpr result

#print axioms dominatedPath_of_primitive
#print axioms DominatedPath.integral
end MinimizingSard.Five
