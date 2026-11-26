import TangentFrameMetric
import IntrinsicLength

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
open Volterra
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] [IsManifold 𝓘(ℝ,State) ∞ M] {m : ℕ}

def tangentVelocity (γ : C(Time,M)) (t : ℝ) : Tangent (γ (clamp t)) :=
  deriv (fun r => chartAt State (γ (clamp t)) (γ (clamp r))) t

theorem tangentVelocity_of_chart_deriv (e : Frame M m) (γ : C(Time,M)) (r : ℝ) (v : State)
    (inside : γ (clamp r) ∈ e.chart.source) (vel : HasDerivAt (fun s => e.chart (γ (clamp s))) v r) :
    tangentVelocity γ r = e.tangentMap (γ (clamp r)) v := by
  let y := γ (clamp r)
  let c := chartAt State y
  have d := (transition_smooth (k := 1) e.chart c e.compatible (chart_mem_maximalAtlas y) y inside (mem_chart_source _ _)).differentiableAt (by decide)
  have ct : Continuous (fun s : ℝ => γ (clamp s)) := γ.continuous.comp continuous_projIcc
  have eq : (fun s => c (γ (clamp s))) =ᶠ[𝓝 r] ((c ∘ e.chart.symm) ∘ (fun s => e.chart (γ (clamp s)))) := by
    filter_upwards [ct.continuousAt (e.chart.open_source.mem_nhds inside)] with s hs
    simp [Function.comp_apply,e.chart.left_inv hs]
  exact ((d.hasFDerivAt.comp_hasDerivAt r vel).congr_of_eventuallyEq eq).deriv

open Classical in
def tangentSpeedSq (Δ : (y : M) → Submodule ℝ (Tangent y)) (g : (y : M) → Δ y → ℝ) (γ : C(Time,M)) (r : ℝ) : ℝ :=
  if h : tangentVelocity γ r ∈ Δ (γ (clamp r)) then g _ ⟨_,h⟩ else 0

def tangentLength (Δ : (y : M) → Submodule ℝ (Tangent y)) (g : (y : M) → Δ y → ℝ) (γ : C(Time,M)) : ℝ :=
  ∫ r in (0:ℝ)..1, Real.sqrt (tangentSpeedSq Δ g γ r)

theorem PathHasLength.tangent_metric {Γ : Geometry M m} {Δ : (y : M) → Submodule ℝ (Tangent y)} {g : (y : M) → Δ y → ℝ}
    (metric : ∀ e ∈ Γ.frames, RepresentsMetric e Δ g) {γ : C(Time,M)} {l : ℝ} (path : PathHasLength Γ γ l) :
    (∀ᵐ r ∂volume.restrict (Ioc (0:ℝ) 1), tangentVelocity γ r ∈ Δ (γ (clamp r))) ∧ tangentLength Δ g γ = l := by
  classical
  obtain ⟨U,len,vel⟩ := path.physical_velocity
  have ae : ∀ᵐ r ∂volume.restrict (Ioc (0:ℝ) 1), tangentVelocity γ r ∈ Δ (γ (clamp r)) ∧
      tangentSpeedSq Δ g γ r = speedSq (U r) := by
    filter_upwards [vel] with r ⟨e,he,src,dv⟩
    obtain ⟨A,hA⟩ := metric e he _ src
    have v : tangentVelocity γ r = (A (U r) : Tangent _) := (tangentVelocity_of_chart_deriv e γ r _ src dv).trans (hA (U r)).1.symm
    have mem : tangentVelocity γ r ∈ Δ (γ (clamp r)) := v.symm ▸ (A (U r)).property
    refine ⟨mem,?_⟩
    unfold tangentSpeedSq
    rw [dif_pos mem]
    exact (congrArg (g _) (Subtype.ext v)).trans (hA (U r)).2
  refine ⟨ae.mono (fun _ h => h.1),?_⟩
  rw [len]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le zero_le_one]
  exact ae.mono (fun r h => congrArg Real.sqrt h.2)

#print axioms tangentVelocity_of_chart_deriv
#print axioms PathHasLength.tangent_metric
end MinimizingSard.Five
