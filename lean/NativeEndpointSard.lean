import HilbertPathManifold
import Mathlib.Geometry.Manifold.MFDeriv.Defs

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
open Volterra
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] [T2Space M] [IsManifold 𝓘(ℝ,State) ∞ M]
variable {m : ℕ} {Γ : Geometry M m} {x : M} {Δ : (y : M) → Submodule ℝ (Tangent y)} {g : (y : M) → Δ y → ℝ}

/-- The native derivative of time-one evaluation, including differentiability and the
exact intrinsic singularity test on every path. -/
theorem native_endpoint_derivative (metric : ∀ e ∈ Γ.frames, RepresentsMetric e Δ g) (γ : HorizontalPaths Γ x) :
    MDifferentiableAt 𝓘(ℝ,PathModel m) 𝓘(ℝ,State) HorizontalPaths.endpoint γ ∧
    (IntrinsicCritical Δ x γ.val ↔ ¬ Function.Surjective (mfderiv 𝓘(ℝ,PathModel m) 𝓘(ℝ,State) HorizontalPaths.endpoint γ)) := by
  let A := (ControlChart.exists_chart γ).choose
  let c := chartAt State γ.endpoint
  obtain ⟨u,hu⟩ := (ControlChart.exists_chart γ).choose_spec
  have enc : A.encode γ = u := A.encode_eq hu
  obtain ⟨p,path,rep,codes⟩ := (show A.Graph γ u from hu)
  obtain ⟨G,dg,_,graph,crit⟩ := intrinsic_critical_full_endpoint metric x γ.val A.partition A.frames p (A.split u)
    A.member path rep codes c (chart_mem_maximalAtlas _) (mem_chart_source _ _)
  let W := writtenInExtChartAt 𝓘(ℝ,PathModel m) 𝓘(ℝ,State) γ HorizontalPaths.endpoint
  have same : W =ᶠ[𝓝 u] G ∘ A.split := by
    filter_upwards [(A.decode_family hu 1 le_rfl).2,A.split.continuous.continuousAt.tendsto graph] with v hv hg
    obtain ⟨β,hβ⟩ := hv
    change c (A.decode v).endpoint = G (A.split v)
    rw [A.decode_eq hβ]
    obtain ⟨z,w,_,cv⟩ := hβ
    exact (congrArg c ((hg.2 _).mp (w.control cv))).trans (c.right_inv hg.1)
  have atU : extChartAt 𝓘(ℝ,PathModel m) γ γ = u := enc
  have dw : DifferentiableAt ℝ W u := (dg.comp u A.split.differentiableAt).congr_of_eventuallyEq same
  have md : MDifferentiableAt 𝓘(ℝ,PathModel m) 𝓘(ℝ,State) HorizontalPaths.endpoint γ := by
    apply (mdifferentiableAt_iff _ _).mpr
    refine ⟨(path_eval_continuous Γ x (clamp 1)).continuousAt,?_⟩
    rw [atU]
    exact dw.differentiableWithinAt
  refine ⟨md,?_⟩
  rw [mfderiv,if_pos md,atU]
  change IntrinsicCritical Δ x γ.val ↔ ¬ Function.Surjective (fderivWithin ℝ W (range (id : PathModel m → PathModel m)) u)
  rw [range_id,fderivWithin_univ,same.fderiv_eq,fderiv_comp u dg A.split.differentiableAt,crit]
  have eqd : fderiv ℝ A.split u = A.split.toContinuousLinearMap := A.split.hasFDerivAt.fderiv
  rw [eqd]
  apply not_congr
  exact ⟨fun h => h.comp A.split.surjective,fun h y => by obtain ⟨w,hw⟩ := h y; exact ⟨A.split w,hw⟩⟩

def nativeMinEndpoints (Γ : Geometry M m) (x : M) : Set M :=
  {y | ∃ γ : HorizontalPaths Γ x, γ.endpoint = y ∧
    ¬ Function.Surjective (mfderiv 𝓘(ℝ,PathModel m) 𝓘(ℝ,State) HorizontalPaths.endpoint γ) ∧
    ∀ β : HorizontalPaths Γ x, β.endpoint = y → γ.metricLength ≤ β.metricLength}

theorem native_endpoints_eq (metric : ∀ e ∈ Γ.frames, RepresentsMetric e Δ g) (x : M) :
    nativeMinEndpoints Γ x = intrinsicMinEndpoints Δ g x := by
  rw [intrinsic_endpoints_eq metric,← observed_endpoints_eq]
  ext y
  change (∃ γ : HorizontalPaths Γ x, _ ∧ _ ∧ _) ↔ ∃ γ : HorizontalPaths Γ x, _ ∧ _ ∧ _
  simp_rw [← (native_endpoint_derivative metric _).2,intrinsic_critical_iff metric]

/-- Fixed-source, five-dimensional minimizing Sard theorem in the native
mathlib Hilbert manifold of actual horizontal Sobolev paths. -/
theorem five_dimensional_native_endpoint_sard [SecondCountableTopology M] [ConnectedSpace M] [MeasurableSpace M]
    (m : ℕ) (hm : 0 < m) (h5 : m < 5) (Δ : (y : M) → Submodule ℝ (Tangent y)) (g : (y : M) → Δ y → ℝ)
    (geometry : HasBundleCoordinates m Δ g) (x : M) (μ : Measure M) (density : HasSmoothDensity μ) :
    μ (nativeMinEndpoints (bundleGeometry geometry hm) x) = 0 := by
  have metric (e) (he : e ∈ (bundleGeometry geometry hm).frames) : RepresentsMetric e Δ g := he
  rw [native_endpoints_eq metric]
  exact five_dimensional_intrinsic_curve_sard m hm h5 Δ g geometry x μ density

#print axioms native_endpoint_derivative
#print axioms native_endpoints_eq
#print axioms five_dimensional_native_endpoint_sard
end MinimizingSard.Five
