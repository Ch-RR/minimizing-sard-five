import CountablePathAtlas
import BilinearMetricCoordinates

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
open Volterra
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] [T2Space M] [IsManifold 𝓘(ℝ,State) ∞ M]
variable {m : ℕ} {Δ : (y : M) → Submodule ℝ (Tangent y)} {g : (y : M) → Δ y → ℝ}

def horizontalDistance (Δ : (y : M) → Submodule ℝ (Tangent y)) (g : (y : M) → Δ y → ℝ) (x y : M) : ℝ :=
  sInf {l | ∃ β : Subtype (fixedHorizontal Δ x), β.val (clamp 1) = y ∧ tangentLength Δ g β.val = l}

omit [T2Space M] [IsManifold 𝓘(ℝ,State) ∞ M] in
theorem length_minimal_iff_distance {x y : M} (γ : Subtype (fixedHorizontal Δ x)) (endAt : γ.val (clamp 1) = y) :
    (∀ β : Subtype (fixedHorizontal Δ x), β.val (clamp 1) = y → tangentLength Δ g γ.val ≤ tangentLength Δ g β.val) ↔
      tangentLength Δ g γ.val = horizontalDistance Δ g x y := by
  let S := {l | ∃ β : Subtype (fixedHorizontal Δ x), β.val (clamp 1) = y ∧ tangentLength Δ g β.val = l}
  have lower : BddBelow S := by
    refine ⟨0,?_⟩
    rintro _ ⟨β,_,rfl⟩
    exact intervalIntegral.integral_nonneg_of_forall zero_le_one (fun r => Real.sqrt_nonneg _)
  have hit : tangentLength Δ g γ.val ∈ S := ⟨γ,endAt,rfl⟩
  change _ ↔ tangentLength Δ g γ.val = sInf S
  constructor
  · intro h
    apply le_antisymm _ (csInf_le lower hit)
    apply le_csInf ⟨_,hit⟩
    rintro _ ⟨β,endβ,rfl⟩
    exact h β endβ
  · intro eq β endβ
    exact eq.trans_le (csInf_le lower ⟨β,endβ,rfl⟩)

def PathAtlas.endpointTest {Q : C(Time,M) → Prop} (A : PathAtlas Q m) (Δ : (y : M) → Submodule ℝ (Tangent y)) (x : M) : Prop :=
  letI := A.topology
  letI := A.charts
  let ev := fun γ : Subtype Q => γ.val (clamp 1)
  ∀ γ : Subtype Q, MDifferentiableAt 𝓘(ℝ,PathModel m) 𝓘(ℝ,State) ev γ ∧
    (IntrinsicCritical Δ x γ.val ↔ ¬ Function.Surjective (mfderiv 𝓘(ℝ,PathModel m) 𝓘(ℝ,State) ev γ))

omit [T2Space M] [IsManifold 𝓘(ℝ,State) ∞ M] in
private theorem test_transport {Q R : C(Time,M) → Prop} (h : Q = R) (A : PathAtlas Q m) (x : M) :
    (h ▸ A : PathAtlas R m).endpointTest Δ x ↔ A.endpointTest Δ x := by subst R; rfl

theorem intrinsic_native_endpoint_derivative (geometry : HasBundleCoordinates m Δ g) (hm : 0 < m) (x : M) :
    (intrinsicPathAtlas geometry hm x).endpointTest Δ x := by
  rw [intrinsicPathAtlas,test_transport]
  intro γ
  exact native_endpoint_derivative (Γ := bundleGeometry geometry hm) (g := g) (fun _ h => h) γ

/-- For every fixed source, the endpoints of length-minimizing critical points
of the unrestricted endpoint map have smooth outer measure zero. -/
theorem five_dimensional_minimizing_sard [SecondCountableTopology M] [ConnectedSpace M] [MeasurableSpace M]
    (m : ℕ) (hm : 0 < m) (h5 : m < 5) (Δ : (y : M) → Submodule ℝ (Tangent y)) (g : (y : M) → Δ y → ℝ)
    (geometry : HasBundleCoordinates m Δ g) (x : M) (μ : Measure M) (density : HasSmoothDensity μ) :
    let A := intrinsicPathAtlas geometry hm x
    letI := A.topology
    letI := A.charts
    let ev := fun γ : Subtype (fixedHorizontal Δ x) => γ.val (clamp 1)
    μ {y | ∃ γ : Subtype (fixedHorizontal Δ x), ev γ = y ∧
      ¬ Function.Surjective (mfderiv 𝓘(ℝ,PathModel m) 𝓘(ℝ,State) ev γ) ∧
      tangentLength Δ g γ.val = horizontalDistance Δ g x y} = 0 := by
  apply Eq.trans _ (five_dimensional_intrinsic_hilbert_sard m hm h5 Δ g geometry x μ density)
  apply congrArg μ
  ext y
  constructor
  · rintro ⟨γ,hy,sing,dist⟩
    exact ⟨γ,hy,sing,(length_minimal_iff_distance γ hy).mpr dist⟩
  · rintro ⟨γ,hy,sing,minimal⟩
    exact ⟨γ,hy,sing,(length_minimal_iff_distance γ hy).mp minimal⟩

/-- The same statement with the geometric metric supplied as an actual positive-definite
inner product on each horizontal fiber. Smoothness is tested on scalar Gram entries. -/
theorem five_dimensional_metric_minimizing_sard [SecondCountableTopology M] [ConnectedSpace M] [MeasurableSpace M]
    (m : ℕ) (hm : 0 < m) (h5 : m < 5) (Δ : (y : M) → Submodule ℝ (Tangent y))
    (g : (y : M) → InnerProductSpace.Core ℝ (Δ y)) (geometry : HasSmoothMetricBasis m Δ g)
    (x : M) (μ : Measure M) (density : HasSmoothDensity μ) :
    let speedSq := fun (y : M) (v : Δ y) => (g y).inner v v
    let A := intrinsicPathAtlas geometry.coordinates hm x
    letI := A.topology
    letI := A.charts
    let ev := fun γ : Subtype (fixedHorizontal Δ x) => γ.val (clamp 1)
    μ {y | ∃ γ : Subtype (fixedHorizontal Δ x), ev γ = y ∧
      ¬ Function.Surjective (mfderiv 𝓘(ℝ,PathModel m) 𝓘(ℝ,State) ev γ) ∧
      tangentLength Δ speedSq γ.val = horizontalDistance Δ speedSq x y} = 0 :=
  five_dimensional_minimizing_sard m hm h5 Δ _ geometry.coordinates x μ density

#print axioms five_dimensional_metric_minimizing_sard
#print axioms length_minimal_iff_distance
#print axioms intrinsic_native_endpoint_derivative
#print axioms five_dimensional_minimizing_sard
end MinimizingSard.Five
