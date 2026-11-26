import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.Order.LeftRightNhds

/-! The measure-theoretic flatness step for smooth transverse
coefficients, with a common exceptional set for all coordinate words. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace MinimizingSard.Flatness

abbrev Space (d : ℕ) := Fin d → ℝ

def direction {d : ℕ} (v : Space d) (f : Space d → ℝ) (x : Space d) : ℝ :=
  fderiv ℝ f x v

private theorem smooth_direction {d : ℕ} (v : Space d) {f : Space d → ℝ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (direction v f) :=
  (hf.contDiff_fderiv_apply (m := ∞) (by simp)).comp (contDiff_id.prodMk contDiff_const)

private theorem ae_line_zero (f g : ℝ → ℝ) (hd : ∀ t, HasDerivAt f (g t) t) :
    ∀ᵐ t : ℝ, f t = 0 → g t = 0 := by
  let S := {t | f t = 0}
  filter_upwards [(countable_setOf_isolated_right_within (s := S)).ae_notMem
    (volume : Measure ℝ)] with t hi
  intro ht
  let U := S ∩ Ioi t
  haveI : (𝓝[U] t).NeBot := ⟨fun h => hi ⟨ht,h⟩⟩
  have notin : t ∉ U := fun h => (lt_irrefl t) (show t < t from h.2)
  have lim := (hasDerivWithinAt_iff_tendsto_slope' notin).mp
    (hd t).hasDerivWithinAt
  have vanish : slope f t =ᶠ[𝓝[U] t] (fun _ => (0 : ℝ)) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy' : f y = 0 := hy.1
    simp [slope_def_field,ht,hy']
  exact tendsto_nhds_unique lim (tendsto_const_nhds.congr' vanish.symm)

theorem ae_direction_zero {d : ℕ} (v : Space d) (f : Space d → ℝ) (hf : ContDiff ℝ ∞ f) :
    ∀ᵐ x : Space d, f x = 0 → direction v f x = 0 := by
  let L := (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v)
  let S := {x | f x = 0 → direction v f x = 0}
  have meas : MeasurableSet S := by
    have first := isClosed_eq hf.continuous (continuous_const (y := (0 : ℝ)))
    have second := isClosed_eq (smooth_direction v hf).continuous (continuous_const (y := (0 : ℝ)))
    convert first.measurableSet.compl.union second.measurableSet using 1
    ext x
    simp [S, imp_iff_not_or]
  have along (x : Space d) : ∀ᵐ t : ℝ, x + L t ∈ S := by
    apply ae_line_zero (fun t => f (x + L t))
    intro t
    have inner : HasDerivAt (fun t : ℝ => x + L t) v t := by
      change HasDerivAt (fun k : ℝ => x + k • v) v t
      simpa only [zero_add, one_smul] using
        (hasDerivAt_const t x).add ((hasDerivAt_id' t).smul_const v)
    exact ((hf.differentiable (by simp)) (x + L t)).hasFDerivAt.comp_hasDerivAt t inner
  have prodMeas : MeasurableSet {p : Space d × ℝ | p.1 + L p.2 ∈ S} :=
    (measurable_fst.add (L.continuous.measurable.comp measurable_snd)) meas
  have first : ∀ᵐ x : Space d, ∀ᵐ t : ℝ, x + L t ∈ S := .of_forall along
  obtain ⟨t,ht⟩ := ((Measure.ae_ae_comm prodMeas).mp first).exists
  have hn : volume ((fun x => x + L t) ⁻¹' Sᶜ) = 0 :=
    measure_eq_zero_iff_ae_notMem.mpr (ht.mono (fun _ h => fun hn => hn h))
  rw [measure_preimage_add_right] at hn
  exact (measure_eq_zero_iff_ae_notMem.mp hn).mono (fun _ h => not_not.mp h)

def iteratedDirection {d : ℕ} (f : Space d → ℝ) (v : Fin d → Space d) :
    List (Fin d) → Space d → ℝ
  | [] => f
  | i :: w => direction (v i) (iteratedDirection f v w)

/-- Simultaneous flatness for all orders on the zero set. In particular
the vectors can be the coordinate axes. No regularity of the level set
and no analyticity of the function are assumed. -/
theorem ae_all_orders_zero {d : ℕ} (f : Space d → ℝ) (hf : ContDiff ℝ ∞ f)
    (v : Fin d → Space d) :
    ∀ᵐ x : Space d, f x = 0 → ∀ w, iteratedDirection f v w x = 0 := by
  have smooth (w : List (Fin d)) : ContDiff ℝ ∞ (iteratedDirection f v w) := by
    induction w with
    | nil => exact hf
    | cons i w ih => exact smooth_direction (v i) ih
  have each (w : List (Fin d)) : ∀ᵐ x : Space d, f x = 0 → iteratedDirection f v w x = 0 := by
    induction w with
    | nil => exact .of_forall (fun _ h => h)
    | cons i w ih =>
      filter_upwards [ih, ae_direction_zero (v i) _ (smooth w)] with x prev step
      exact fun hx => step (prev hx)
  filter_upwards [ae_all_iff.mpr each] with x hx using fun h w => hx w h

#print axioms ae_all_orders_zero
end MinimizingSard.Flatness
