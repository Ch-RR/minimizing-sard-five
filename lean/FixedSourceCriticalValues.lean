import AnyTimeVariation
import HorizontalCurveVolume

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
open Volterra
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] [T2Space M] {m n : ℕ}

/-- The test on actual curves, using global smooth observations, has no
particular subdivision or selected control chart in its definition. -/
def ObservationCritical (Γ : Geometry M m) (x : M) (γ : C(Time,M)) : Prop :=
  ∃ c : OpenPartialHomeomorph M State, c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M ∧ γ (clamp 1) ∈ c.source ∧
    ∃ η : State →L[ℝ] ℝ, η ≠ 0 ∧ ∀ F : ℝ → C(Time,M), F 0 = γ → ObservationVariation Γ x F →
      DifferentiableAt ℝ (fun t => c (F t (clamp 1))) 0 → η (deriv (fun t => c (F t (clamp 1))) 0) = 0

theorem observationCritical_iff (Γ : Geometry M m) (x : M) (γ : C(Time,M)) :
    ObservationCritical Γ x γ ↔ CurveSingular Γ x γ := by
  unfold ObservationCritical CurveSingular
  simp only [observationVariation_iff]

variable [IsManifold 𝓘(ℝ,State) ∞ M]
theorem observationCritical_iff_full_derivative {Γ : Geometry M m} {x : M} {γ : C(Time,M)}
    {P : TimePartition (n+1)} {e : Fin (n+1) → Frame M m} {p : Fin (n+1) → SobolevData} {u : Fin (n+1) → Control m}
    (he : ∀ i, e i ∈ Γ.frames) (path : SobolevJoins e p x (γ (clamp 1))) (rep : RepresentsPath P e p γ)
    (codes : FrameCodes e p u) : ObservationCritical Γ x γ ↔ Singular e u x (γ (clamp 1)) :=
  (observationCritical_iff _ _ _).trans ((curve_singular_iff_presentation he path rep).trans (sobolev_singular_iff e p u path codes))

theorem global_min_endpoints_eq (Γ : Geometry M m) (x : M) :
    minimizingCriticalValues Γ x = singularMinEndpoints Γ x := by
  rw [minimizingCriticalValues_eq,← sobolev_endpoints_eq]
  apply Subset.antisymm (curveMinEndpoints_subset Γ x)
  rintro y ⟨n,e,p,he,path,sing,minimal⟩
  let P := TimePartition.uniform n
  obtain ⟨γ,src,dst,rep⟩ := path.realize P
  have hpath : SobolevJoins e p x (γ (clamp 1)) := dst.symm ▸ path
  refine ⟨γ,sobolevLength e p,src,dst,⟨n,P,e,p,he,src.symm ▸ hpath,rep,rfl⟩,
    (curve_singular_iff_presentation he hpath rep).mpr (dst.symm ▸ sing),?_⟩
  rintro ξ l a b ⟨k,Q,d,z,hd,walk,_,rfl⟩
  exact minimal k d z hd (a ▸ b ▸ walk)

def observedMinEndpoints (Γ : Geometry M m) (x : M) : Set M :=
  {y | ∃ γ : HorizontalPaths Γ x, γ.endpoint = y ∧ ObservationCritical Γ x γ.val ∧
    ∀ β : HorizontalPaths Γ x, β.endpoint = y → γ.metricLength ≤ β.metricLength}

theorem observed_endpoints_eq (Γ : Geometry M m) (x : M) :
    observedMinEndpoints Γ x = singularMinEndpoints Γ x := by
  rw [← global_min_endpoints_eq]
  unfold observedMinEndpoints minimizingCriticalValues
  simp only [observationCritical_iff]

theorem five_dimensional_fixed_source_critical_values [SecondCountableTopology M] [ConnectedSpace M]
    [MeasurableSpace M] (m : ℕ) (hm : 0 < m) (h5 : m < 5) (Γ : Geometry M m) (x : M)
    (μ : Measure M) (density : HasSmoothDensity μ) : μ (observedMinEndpoints Γ x) = 0 := by
  rw [observed_endpoints_eq]
  exact measure_zero_of_chart_null μ density _ (five_dimensional_frame_sard (M := M) m hm h5 Γ x)

#print axioms observationCritical_iff_full_derivative
#print axioms global_min_endpoints_eq
#print axioms observed_endpoints_eq
#print axioms five_dimensional_fixed_source_critical_values
end MinimizingSard.Five
