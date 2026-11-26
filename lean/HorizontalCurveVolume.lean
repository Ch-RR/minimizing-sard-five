import IntrinsicLength
import SmoothVolumeSard

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
open Volterra
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] {m : ℕ}

/-- Actual fixed-source horizontal Sobolev curves on the common unit interval. -/
def HorizontalPaths (Γ : Geometry M m) (x : M) :=
  {γ : C(Time,M) // γ (clamp 0) = x ∧ ∃ l, PathHasLength Γ γ l}

def HorizontalPaths.endpoint {Γ : Geometry M m} {x : M} (γ : HorizontalPaths Γ x) : M := γ.val (clamp 1)

def HorizontalPaths.metricLength {Γ : Geometry M m} {x : M} (γ : HorizontalPaths Γ x) : ℝ := γ.property.2.choose

theorem HorizontalPaths.length_in_chart {Γ : Geometry M m} {x : M} (γ : HorizontalPaths Γ x) {l : ℝ}
    (h : PathHasLength Γ γ.val l) : γ.metricLength = l := γ.property.2.choose_spec.unique h

def minimizingCriticalValues (Γ : Geometry M m) (x : M) : Set M :=
  {y | ∃ γ : HorizontalPaths Γ x, γ.endpoint = y ∧ CurveSingular Γ x γ.val ∧
    ∀ β : HorizontalPaths Γ x, β.endpoint = y → γ.metricLength ≤ β.metricLength}

theorem minimizingCriticalValues_eq (Γ : Geometry M m) (x : M) :
    minimizingCriticalValues Γ x = curveMinEndpoints Γ x := by
  ext y
  constructor
  · rintro ⟨γ,hy,sing,minimal⟩
    refine ⟨γ.val,γ.metricLength,γ.property.1,hy,γ.property.2.choose_spec,sing,?_⟩
    intro β d a b hl
    let ξ : HorizontalPaths Γ x := ⟨β,a,d,hl⟩
    exact (minimal ξ b).trans_eq (ξ.length_in_chart hl)
  · rintro ⟨γ,l,a,b,hl,sing,minimal⟩
    let ξ : HorizontalPaths Γ x := ⟨γ,a,l,hl⟩
    refine ⟨ξ,b,sing,?_⟩
    intro β hy
    rw [ξ.length_in_chart hl]
    exact minimal β.val _ β.property.1 hy β.property.2.choose_spec

theorem five_dimensional_horizontal_curve_volume [SecondCountableTopology M] [T2Space M] [ConnectedSpace M]
    [IsManifold 𝓘(ℝ,State) ∞ M] [MeasurableSpace M] (m : ℕ) (hm : 0 < m) (h5 : m < 5)
    (Γ : Geometry M m) (x : M) (μ : Measure M) (density : HasSmoothDensity μ) :
    μ (minimizingCriticalValues Γ x) = 0 := by
  rw [minimizingCriticalValues_eq]
  exact measure_zero_of_chart_null μ density _ (five_dimensional_curve_sard m hm h5 Γ x)

#print axioms HorizontalPaths.length_in_chart
#print axioms minimizingCriticalValues_eq
#print axioms five_dimensional_horizontal_curve_volume
end MinimizingSard.Five
