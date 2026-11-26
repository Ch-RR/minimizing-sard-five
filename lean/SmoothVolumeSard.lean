import SobolevMinimizingSard
import Mathlib.Topology.Compactness.Lindelof

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff ENNReal
namespace MinimizingSard.Five
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] [MeasurableSpace M]

/-- A smooth positive volume described in local coordinates. The density
formula is required only on Borel sets contained in the chart target. -/
def HasSmoothDensity (μ : Measure M) : Prop :=
  ∀ y : M, ∃ c : OpenPartialHomeomorph M State, c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M ∧ y ∈ c.source ∧
    ∃ ρ : State → ℝ, ContDiffOn ℝ ∞ ρ c.target ∧ (∀ z ∈ c.target, 0 < ρ z) ∧
      ∀ B : Set State, MeasurableSet B → B ⊆ c.target →
        μ (c.source ∩ c ⁻¹' B) = ∫⁻ z in B, ENNReal.ofReal (ρ z) ∂volume

theorem measure_zero_of_chart_null [SecondCountableTopology M] (μ : Measure M) (density : HasSmoothDensity μ)
    (A : Set M) (null : ∀ c : OpenPartialHomeomorph M State, c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M →
      volume (c '' (c.source ∩ A)) = 0) : μ A = 0 := by
  classical
  choose c hc hit ρ _ _ repr using density
  have cover : (univ : Set M) ⊆ ⋃ y, (c y).source := fun y _ => mem_iUnion.mpr ⟨y,hit y⟩
  obtain ⟨S,hS,sub⟩ := isLindelof_univ.elim_countable_subcover (fun y => (c y).source)
    (fun y => (c y).open_source) cover
  haveI := hS.to_subtype
  have part (y : M) : μ ((c y).source ∩ A) = 0 := by
    let C := c y
    let D := C '' (C.source ∩ A)
    let B := toMeasurable volume D ∩ C.target
    have bz : volume B = 0 := measure_mono_null inter_subset_left
      (by rw [measure_toMeasurable]; exact null C (hc y))
    have major : C.source ∩ A ⊆ C.source ∩ C ⁻¹' B := by
      intro v hv
      exact ⟨hv.1,subset_toMeasurable _ _ (mem_image_of_mem C hv),C.map_source hv.1⟩
    apply measure_mono_null major
    rw [repr y B ((measurableSet_toMeasurable _ _).inter C.open_target.measurableSet) inter_subset_right]
    exact setLIntegral_measure_zero _ _ bz
  apply measure_mono_null (t := ⋃ y : S, (c y.val).source ∩ A)
  · intro y hy
    obtain ⟨k,hk⟩ := mem_iUnion.mp (sub (mem_univ y))
    obtain ⟨hs,here⟩ := mem_iUnion.mp hk
    exact mem_iUnion.mpr ⟨⟨k,hs⟩,here,hy⟩
  · exact measure_iUnion_null (fun y => part y.val)

#print axioms measure_zero_of_chart_null
end MinimizingSard.Five
