import FrameChangeLayers
import SobolevSynthesis

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] [IsManifold 𝓘(ℝ,State) ∞ M] {m : ℕ}
abbrev Tangent (y : M) := TangentSpace 𝓘(ℝ,State) y

/-- The coordinate differential into mathlib's preferred tangent
coordinates at the base point. -/
def Frame.tangentMap (e : Frame M m) (y : M) : State →L[ℝ] Tangent y :=
  fderiv ℝ ((chartAt State y) ∘ e.chart.symm) (e.chart y)

def Frame.tangentSynthesis (e : Frame M m) (y : M) : Fiber m →L[ℝ] Tangent y :=
  (e.tangentMap y).comp (e.coefficient (e.chart y))

theorem Frame.tangentMap_injective (e : Frame M m) {y : M} (hy : y ∈ e.chart.source) :
    Function.Injective (e.tangentMap y) := by
  have h := transition_left e.chart (chartAt State y) e.compatible (chart_mem_maximalAtlas y) y hy (mem_chart_source _ _)
  intro u v eq
  have hu := DFunLike.congr_fun h u
  have hv := DFunLike.congr_fun h v
  exact hu.symm.trans ((congrArg (fderiv ℝ (e.chart ∘ (chartAt State y).symm) ((chartAt State y) y)) eq).trans hv)

theorem Frame.tangentSynthesis_injective (e : Frame M m) {y : M} (hy : y ∈ e.chart.source) :
    Function.Injective (e.tangentSynthesis y) :=
  (e.tangentMap_injective hy).comp (e.coefficient_injective (e.chart.map_source hy))

theorem Frame.tangent_change (e d : Frame M m) {y : M} (ey : y ∈ e.chart.source) (dy : y ∈ d.chart.source)
    (v : State) : d.tangentMap y (fderiv ℝ (d.chart ∘ e.chart.symm) (e.chart y) v) = e.tangentMap y v :=
  DFunLike.congr_fun (transition_chain e.chart d.chart (chartAt State y) e.compatible d.compatible (chart_mem_maximalAtlas y)
    y ey dy (mem_chart_source _ _)) v

/-- This definition mentions one tangent subspace and its squared norm
at each point and does not prescribe transitions between frames. -/
def RepresentsMetric (e : Frame M m) (Δ : (y : M) → Submodule ℝ (Tangent y)) (g : (y : M) → Δ y → ℝ) : Prop :=
  ∀ y ∈ e.chart.source, ∃ L : Fiber m ≃ₗ[ℝ] Δ y, ∀ a, (L a : Tangent y) = e.tangentSynthesis y a ∧ g y (L a) = speedSq a

theorem intrinsic_frames_overlap {Δ : (y : M) → Submodule ℝ (Tangent y)} {g : (y : M) → Δ y → ℝ}
    {e d : Frame M m} (he : RepresentsMetric e Δ g) (hd : RepresentsMetric d Δ g)
    (y : M) (hit : y ∈ e.chart.source ∩ d.chart.source) :
    ∃ T : Fiber m ≃ₗ[ℝ] Fiber m, ∀ u, speedSq (T u) = speedSq u ∧
      fderiv ℝ (d.chart ∘ e.chart.symm) (e.chart y) (e.velocity (e.chart y) u) = d.velocity (d.chart y) (T u) := by
  obtain ⟨A,ha⟩ := he y hit.1
  obtain ⟨B,hb⟩ := hd y hit.2
  refine ⟨A.trans B.symm,fun u => ?_⟩
  let v := B.symm (A u)
  have bv : B v = A u := B.apply_symm_apply _
  refine ⟨(hb v).2.symm.trans ((congrArg (g y) bv).trans (ha u).2),?_⟩
  apply d.tangentMap_injective hit.2
  rw [e.tangent_change d hit.1 hit.2]
  change e.tangentMap y (e.velocity (e.chart y) u) = d.tangentMap y (d.velocity (d.chart y) v)
  rw [← Frame.coefficient_apply,← Frame.coefficient_apply]
  exact (ha u).1.symm.trans ((congrArg Subtype.val bv.symm).trans (hb v).1)

def geometryOfTangentMetric (Δ : (y : M) → Submodule ℝ (Tangent y)) (g : (y : M) → Δ y → ℝ)
    (cover : ∀ y : M, ∃ e : Frame M m, RepresentsMetric e Δ g ∧ y ∈ e.chart.source) : Geometry M m where
  frames := {e | RepresentsMetric e Δ g}
  cover := cover
  overlap := fun _ he _ hd => intrinsic_frames_overlap he hd

/-- Conversely, an arbitrary compatible frame geometry defines one
tangent distribution and one squared norm shared by every frame. -/
theorem Geometry.has_tangent_metric (Γ : Geometry M m) :
    ∃ (Δ : (y : M) → Submodule ℝ (Tangent y)) (g : (y : M) → Δ y → ℝ),
      ∀ e ∈ Γ.frames, RepresentsMetric e Δ g := by
  classical
  choose b hb hit using Γ.cover
  let Δ (y : M) := LinearMap.range ((b y).tangentSynthesis y).toLinearMap
  let A (y : M) : Fiber m ≃ₗ[ℝ] Δ y := LinearEquiv.ofInjective _ ((b y).tangentSynthesis_injective (hit y))
  let g (y : M) (v : Δ y) := speedSq ((A y).symm v)
  refine ⟨Δ,g,?_⟩
  intro e he y ey
  obtain ⟨T,swap⟩ := Γ.overlap e he (b y) (hb y) y ⟨ey,hit y⟩
  refine ⟨T.trans (A y),fun a => ⟨?_,?_⟩⟩
  · change (b y).tangentMap y ((b y).coefficient ((b y).chart y) (T a)) = e.tangentMap y (e.coefficient (e.chart y) a)
    rw [Frame.coefficient_apply,Frame.coefficient_apply,← (swap a).2,e.tangent_change _ ey (hit y)]
  · change speedSq ((A y).symm ((A y) (T a))) = _
    simpa only [LinearEquiv.symm_apply_apply] using (swap a).1

#print axioms Frame.tangent_change
#print axioms intrinsic_frames_overlap
#print axioms geometryOfTangentMetric
#print axioms Geometry.has_tangent_metric
end MinimizingSard.Five
