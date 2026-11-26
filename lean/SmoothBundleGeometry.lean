import FixedSourceCriticalValues
import TangentFrameMetric
import SmoothMetricBasis

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] [IsManifold 𝓘(ℝ,State) ∞ M] {m : ℕ}

/-- Local presentation of a smooth tangent subbundle and a fiber inner
product in arbitrary linear bundle coordinates. The horizontal section
Lie span is tested before orthonormalization. -/
structure BundleCoordinates (m : ℕ) (Δ : (y : M) → Submodule ℝ (Tangent y)) (g : (y : M) → Δ y → ℝ) where
  chart : OpenPartialHomeomorph M State
  compatible : chart ∈ maximalAtlas 𝓘(ℝ,State) ∞ M
  columns : State → Fiber m →L[ℝ] State
  smooth : ContDiffOn ℝ ∞ columns chart.target
  metric : State → FiberMetric m
  metric_smooth : ContDiffOn ℝ ∞ (fun p : State × (Fiber m × Fiber m) => (metric p.1).inner p.2.1 p.2.2) (chart.target ×ˢ univ)
  fiber : ∀ y ∈ chart.source, ∃ L : Fiber m ≃ₗ[ℝ] Δ y, ∀ u,
    (L u : Tangent y) = fderiv ℝ ((chartAt State y) ∘ chart.symm) (chart y) (columns (chart y) u) ∧
      g y (L u) = (metric (chart y)).inner u u
  generating : ∀ z ∈ chart.target,
    Submodule.span ℝ {v | ∃ V, SectionLie (fun p => LinearMap.range (columns p).toLinearMap) z V ∧ V z = v} = ⊤

private theorem sum_metric (G : FiberMetric m) (B : Fin m → Fiber m)
    (hb : ∀ i j, G.inner (B i) (B j) = if i = j then 1 else 0) (u : Fiber m) :
    G.inner (∑ i, u i • B i) (∑ i, u i • B i) = speedSq u := by
  letI := G.toNormedAddCommGroup
  letI := InnerProductSpace.ofCore G
  letI : SeminormedAddCommGroup (Fiber m) := G.toNormedAddCommGroup.toSeminormedAddCommGroup
  change inner ℝ (∑ i, u i • B i) (∑ i, u i • B i) = _
  have dot (i j) : inner ℝ (B i) (B j) = if i = j then 1 else 0 := hb i j
  simp [sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,dot,speedSq,pow_two]

omit [IsManifold 𝓘(ℝ,State) ∞ M] in
theorem BundleCoordinates.orthonormal_frame {Δ : (y : M) → Submodule ℝ (Tangent y)} {g : (y : M) → Δ y → ℝ}
    (b : BundleCoordinates m Δ g) (hm : 0 < m) :
    ∃ e : Frame M m, e.chart = b.chart ∧ RepresentsMetric e Δ g := by
  classical
  obtain ⟨B,reg,indep,dot⟩ := smooth_metric_basis b.chart.target b.metric b.metric_smooth
  let J (z : State) := Fintype.linearCombination ℝ (fun i => B i z)
  have bij (z) : Function.Bijective (J z) :=
    ⟨(indep z).fintypeLinearCombination_injective,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp (indep z).fintypeLinearCombination_injective⟩
  let E (z) := LinearEquiv.ofBijective (J z) (bij z)
  let X (i : Fin m) (z : State) := b.columns z (B i z)
  have sm (i) : ContDiffOn ℝ ∞ (X i) b.chart.target := b.smooth.clm_apply (reg i)
  have inj (z) (hz : z ∈ b.chart.target) : Function.Injective (b.columns z) := by
    obtain ⟨L,hL⟩ := b.fiber (b.chart.symm z) (b.chart.map_target hz)
    rw [b.chart.right_inv hz] at hL
    intro u v eq
    apply L.injective
    apply Subtype.ext
    rw [(hL u).1,(hL v).1,eq]
  have li (z) (hz : z ∈ b.chart.target) : LinearIndependent ℝ (fun i => X i z) :=
    (indep z).map' (b.columns z).toLinearMap (LinearMap.ker_eq_bot.mpr (inj z hz))
  have identity (z u) : (∑ i, u i • X i z) = b.columns z (J z u) := by
    simp [J,Fintype.linearCombination_apply,X,map_sum]
  have spans (z) : LinearMap.range (b.columns z).toLinearMap = Submodule.span ℝ (range (fun i => X i z)) := by
    rw [← Fintype.range_linearCombination]
    ext v
    constructor
    · rintro ⟨u,rfl⟩
      obtain ⟨a,rfl⟩ := (bij z).2 u
      exact ⟨a,identity z a⟩
    · rintro ⟨u,rfl⟩
      exact ⟨J z u,(identity z u).symm⟩
  let e : Frame M m := {
    chart := b.chart
    compatible := b.compatible
    X := X
    smooth := sm
    independent := li
    generating := fun z hz => by
      rw [← section_lie_span_eq_frame_words hm (fun i => (sm i z hz).contDiffAt (b.chart.open_target.mem_nhds hz))
        (li z hz) (Filter.Eventually.of_forall spans)]
      exact b.generating z hz
  }
  refine ⟨e,rfl,?_⟩
  intro y hy
  obtain ⟨L,hL⟩ := b.fiber y hy
  refine ⟨(E (b.chart y)).trans L,fun u => ⟨?_,?_⟩⟩
  · change (L (J (b.chart y) u) : Tangent y) = _
    rw [(hL _).1]
    change _ = e.tangentMap y (e.coefficient (e.chart y) u)
    rw [Frame.coefficient_apply]
    exact congrArg (e.tangentMap y) (identity (b.chart y) u).symm
  · exact (hL _).2.trans (sum_metric _ _ (dot (b.chart y)) u)

def HasBundleCoordinates (m : ℕ) (Δ : (y : M) → Submodule ℝ (Tangent y)) (g : (y : M) → Δ y → ℝ) : Prop :=
  ∀ y : M, ∃ b : BundleCoordinates m Δ g, y ∈ b.chart.source

def bundleGeometry {Δ : (y : M) → Submodule ℝ (Tangent y)} {g : (y : M) → Δ y → ℝ}
    (h : HasBundleCoordinates m Δ g) (hm : 0 < m) : Geometry M m :=
  geometryOfTangentMetric Δ g (fun y => by
    obtain ⟨b,hit⟩ := h y
    obtain ⟨e,chart,he⟩ := b.orthonormal_frame hm
    exact ⟨e,he,chart.symm ▸ hit⟩)

theorem five_dimensional_bundle_minimizing_sard [SecondCountableTopology M] [T2Space M] [ConnectedSpace M]
    [MeasurableSpace M] (m : ℕ) (hm : 0 < m) (h5 : m < 5)
    (Δ : (y : M) → Submodule ℝ (Tangent y)) (g : (y : M) → Δ y → ℝ)
    (geometry : HasBundleCoordinates m Δ g) (x : M) (μ : Measure M) (density : HasSmoothDensity μ) :
    μ (observedMinEndpoints (bundleGeometry geometry hm) x) = 0 :=
  five_dimensional_fixed_source_critical_values m hm h5 _ x μ density

#print axioms BundleCoordinates.orthonormal_frame
#print axioms five_dimensional_bundle_minimizing_sard
end MinimizingSard.Five
