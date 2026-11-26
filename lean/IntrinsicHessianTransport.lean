import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! Transporting the scalar second variation across smooth changes of
endpoint coordinates and of controls. -/
noncomputable section
open Filter
open scoped Topology
namespace MinimizingSard.Transport
variable {U V W T : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup T] [NormedSpace ℝ T]

/-- The two terms of the second-order chain rule in Banach coordinates. -/
theorem second_comp (f : U → V) (g : V → W) (x v w : U)
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g (f x)) :
    (fderiv ℝ (fderiv ℝ (g ∘ f)) x v) w =
      fderiv ℝ g (f x) ((fderiv ℝ (fderiv ℝ f) x v) w) +
      (fderiv ℝ (fderiv ℝ g) (f x) (fderiv ℝ f x v)) (fderiv ℝ f x w) := by
  have eq : fderiv ℝ (g ∘ f) =ᶠ[𝓝 x] fun y => (fderiv ℝ g (f y)).comp (fderiv ℝ f y) := by
    filter_upwards [hf.eventually (by decide), hf.continuousAt.tendsto.eventually
      (hg.eventually (by decide))] with y ha hb
    exact fderiv_comp y (hb.differentiableAt (by decide)) (ha.differentiableAt (by decide))
  have a := (hg.fderiv_right (m := 1) (by decide)).differentiableAt (by decide)
  have b := (hf.fderiv_right (m := 1) (by decide)).differentiableAt (by decide)
  have dg := a.hasFDerivAt.comp x (hf.differentiableAt (by decide)).hasFDerivAt
  rw [((dg.clm_comp b.hasFDerivAt).congr_of_eventuallyEq eq).fderiv]
  rfl

/-- In a null direction of the first endpoint variation, the scalar
intrinsic Hessian transforms by first derivatives alone, provided the
transported row annihilates the first endpoint image. -/
theorem intrinsic_second_variation (changeControl : T → U) (endpoint : U → V)
    (changeState : V → W) (x v w : T) (p : W →L[ℝ] ℝ)
    (ha : ContDiffAt ℝ 2 changeControl x)
    (hf : ContDiffAt ℝ 2 endpoint (changeControl x))
    (hg : ContDiffAt ℝ 2 changeState (endpoint (changeControl x)))
    (ker : fderiv ℝ endpoint (changeControl x) (fderiv ℝ changeControl x v) = 0)
    (row : ∀ z, p (fderiv ℝ changeState (endpoint (changeControl x))
      (fderiv ℝ endpoint (changeControl x) z)) = 0) :
    p ((fderiv ℝ (fderiv ℝ (changeState ∘ (endpoint ∘ changeControl))) x v) w) =
      p (fderiv ℝ changeState (endpoint (changeControl x))
        ((fderiv ℝ (fderiv ℝ endpoint) (changeControl x)
          (fderiv ℝ changeControl x v)) (fderiv ℝ changeControl x w))) := by
  rw [second_comp _ _ _ _ _ (hf.comp x ha) hg, second_comp _ _ _ _ _ ha hf,
    fderiv_comp x (hf.differentiableAt (by decide)) (ha.differentiableAt (by decide))]
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply, ker, map_zero,
    ContinuousLinearMap.zero_apply, add_zero, map_add, row, zero_add]

#print axioms intrinsic_second_variation
end MinimizingSard.Transport
