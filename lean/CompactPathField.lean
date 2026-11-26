import HamiltonianFrame
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace MinimizingSard.Five
open Volterra

/-- Extend a field given on an open set, preserving its germ along a whole
compact reference path. -/
theorem compact_smooth_extension {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] {n : ℕ}
    (U K : Set E) (openU : IsOpen U) (compact : IsCompact K) (ne : K.Nonempty) (inside : K ⊆ U)
    (F : E → G) (reg : ContDiffOn ℝ n F U) :
    ∃ (G₁ : E → G) (V : Set E), ContDiff ℝ n G₁ ∧ IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧ EqOn G₁ F V := by
  obtain ⟨b,sup,sb,val⟩ := openU.exists_smooth_support_eq
  obtain ⟨x,hx,min⟩ := compact.exists_isMinOn ne sb.continuous.continuousOn
  have positive : 0 < b x := lt_of_le_of_ne (val (mem_range_self x)).1 (Ne.symm (by
    apply (show x ∈ Function.support b from sup.symm ▸ inside hx)))
  let a := (3:ℝ)/b x
  have pa : 0 < a := div_pos (by norm_num) positive
  have ax : a*b x = 3 := by dsimp [a]; field_simp
  let χ (q : E) := Real.smoothTransition (a*b q-1)
  have sc : ContDiff ℝ n χ := Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul (sb.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)))).sub contDiff_const)
  let V := {q | 2 < a*b q}
  have ov : IsOpen V := isOpen_lt continuous_const (continuous_const.mul sb.continuous)
  have inc : K ⊆ V := fun y hy => (by
    change 2 < a*b y
    linarith only [ax,mul_le_mul_of_nonneg_left (min hy) pa.le])
  have inU : V ⊆ U := by
    intro y hy
    rw [← sup]
    exact fun zero => by change 2 < a*b y at hy; rw [zero,mul_zero] at hy; norm_num at hy
  refine ⟨fun q => χ q • F q, V,contDiff_iff_contDiffAt.mpr ?_,ov,inc,inU,?_⟩
  · intro q
    by_cases hu : q ∈ U
    · exact sc.contDiffAt.smul ((reg q hu).contDiffAt (openU.mem_nhds hu))
    · have zero : b q = 0 := Function.notMem_support.mp (fun h => hu (sup ▸ h))
      have small : ∀ᶠ y in 𝓝 q, a*b y < 1 := (continuous_const.mul sb.continuous).continuousAt.eventually_lt_const (by simp [zero])
      apply (contDiffAt_const (c := (0:G))).congr_of_eventuallyEq
      filter_upwards [small] with y hy
      simp only [χ,Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hy.le),zero_smul]
  · intro q hq
    change 2 < a*b q at hq
    simp only [χ,Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ a*b q-1),one_smul]

/-- Global finite-order superposition on the Banach space of continuous paths. -/
def pathField {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (F : E → G) (c : Continuous F) (z : C(Time,E)) : C(Time,G) :=
  PathCalculus.subst (liftField F c) z

theorem pathField_smooth {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {n : ℕ} (F : E → G) (reg : ContDiff ℝ n F) :
    ContDiff ℝ n (pathField F reg.continuous) :=
  PathCalculus.contDiff_subst_of_spatialOrder n _ (field_order n F reg)

#print axioms compact_smooth_extension
#print axioms pathField_smooth
end MinimizingSard.Five
