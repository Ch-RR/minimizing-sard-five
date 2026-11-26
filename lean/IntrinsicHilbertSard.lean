import NativeEndpointSard

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
open Volterra
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] [T2Space M] [IsManifold 𝓘(ℝ,State) ∞ M]
variable {m : ℕ} {Δ : (y : M) → Submodule ℝ (Tangent y)} {g : (y : M) → Δ y → ℝ}

def fixedHorizontal (Δ : (y : M) → Submodule ℝ (Tangent y)) (x : M) (γ : C(Time,M)) : Prop :=
  γ (clamp 0) = x ∧ IsHorizontalH1 Δ γ

omit [T2Space M] [IsManifold 𝓘(ℝ,State) ∞ M] in
def presentedHorizontal (Γ : Geometry M m) (x : M) (γ : C(Time,M)) : Prop :=
  γ (clamp 0) = x ∧ ∃ l, PathHasLength Γ γ l

theorem path_predicates_eq {Γ : Geometry M m} (metric : ∀ e ∈ Γ.frames, RepresentsMetric e Δ g) (x : M) :
    presentedHorizontal Γ x = fixedHorizontal Δ x := by
  funext γ
  apply propext
  refine and_congr_right (fun _ => ⟨?_,?_⟩)
  · rintro ⟨l,h⟩
    exact ⟨h.chart_sobolev,(h.tangent_metric metric).1⟩
  · intro h
    exact ⟨_,(path_length_iff_intrinsic metric γ _).mpr ⟨h.1,h.2,rfl⟩⟩

/-- Structures transported along equality of the admissibility predicates.
The points on both sides are the very same continuous maps. -/
structure PathAtlas (Q : C(Time,M) → Prop) (m : ℕ) where
  topology : TopologicalSpace (Subtype Q)
  charts : @ChartedSpace (PathModel m) _ (Subtype Q) topology
  smooth : letI := topology; letI := charts; IsManifold 𝓘(ℝ,PathModel m) ∞ (Subtype Q)
  hausdorff : @T2Space (Subtype Q) topology

def controlPathAtlas (Γ : Geometry M m) (x : M) : PathAtlas (presentedHorizontal Γ x) m :=
  ⟨pathTopology Γ x,pathCharted Γ x,pathSmooth Γ x,pathHausdorff Γ x⟩

def intrinsicPathAtlas (geometry : HasBundleCoordinates m Δ g) (hm : 0 < m) (x : M) : PathAtlas (fixedHorizontal Δ x) m :=
  let Γ := bundleGeometry geometry hm
  let eq := path_predicates_eq (Γ := Γ) (g := g) (fun _ h => h) x
  eq ▸ controlPathAtlas Γ x

/-- Critical values of time-one evaluation among global length minimizers.
The length is the time integral of the norm of the tangent velocity. -/
def PathAtlas.minimizingCritical {Q : C(Time,M) → Prop} (A : PathAtlas Q m) (length : C(Time,M) → ℝ) : Set M :=
  letI := A.topology
  letI := A.charts
  let ev := fun γ : Subtype Q => γ.val (clamp 1)
  {y | ∃ γ : Subtype Q, ev γ = y ∧ ¬ Function.Surjective (mfderiv 𝓘(ℝ,PathModel m) 𝓘(ℝ,State) ev γ) ∧
    ∀ β : Subtype Q, ev β = y → length γ.val ≤ length β.val}

omit [T2Space M] [IsManifold 𝓘(ℝ,State) ∞ M] in
theorem PathAtlas.transport_critical {Q R : C(Time,M) → Prop} (h : Q = R) (A : PathAtlas Q m) (length : C(Time,M) → ℝ) :
    (h ▸ A : PathAtlas R m).minimizingCritical length = A.minimizingCritical length := by subst R; rfl

theorem intrinsic_hilbert_endpoints_eq (geometry : HasBundleCoordinates m Δ g) (hm : 0 < m) (x : M) :
    (intrinsicPathAtlas geometry hm x).minimizingCritical (tangentLength Δ g) = intrinsicMinEndpoints Δ g x := by
  let Γ := bundleGeometry geometry hm
  have metric (e) (h : e ∈ Γ.frames) : RepresentsMetric e Δ g := h
  rw [intrinsicPathAtlas,PathAtlas.transport_critical,← native_endpoints_eq metric]
  have cost (γ : HorizontalPaths Γ x) : tangentLength Δ g γ.val = γ.metricLength :=
    (γ.property.2.choose_spec.tangent_metric metric).2
  ext y
  change (∃ γ : HorizontalPaths Γ x, γ.endpoint = y ∧ _ ∧ ∀ β : HorizontalPaths Γ x, β.endpoint = y →
    tangentLength Δ g γ.val ≤ tangentLength Δ g β.val) ↔ ∃ γ : HorizontalPaths Γ x, γ.endpoint = y ∧ _ ∧ _
  simp_rw [cost]
  rfl

/-- Five-dimensional minimizing Sard for the literal fixed-source horizontal H¹
path subtype, native endpoint derivative, and tangent-integral length. -/
theorem five_dimensional_intrinsic_hilbert_sard [SecondCountableTopology M] [ConnectedSpace M] [MeasurableSpace M]
    (m : ℕ) (hm : 0 < m) (h5 : m < 5) (Δ : (y : M) → Submodule ℝ (Tangent y)) (g : (y : M) → Δ y → ℝ)
    (geometry : HasBundleCoordinates m Δ g) (x : M) (μ : Measure M) (density : HasSmoothDensity μ) :
    μ ((intrinsicPathAtlas geometry hm x).minimizingCritical (tangentLength Δ g)) = 0 := by
  rw [intrinsic_hilbert_endpoints_eq geometry hm]
  exact five_dimensional_intrinsic_curve_sard m hm h5 Δ g geometry x μ density

#print axioms path_predicates_eq
#print axioms intrinsic_hilbert_endpoints_eq
#print axioms five_dimensional_intrinsic_hilbert_sard
end MinimizingSard.Five
