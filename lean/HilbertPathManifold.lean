import HilbertPathTransitions

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
open Volterra
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] [T2Space M] [IsManifold 𝓘(ℝ,State) ∞ M]
variable {m : ℕ} (Γ : Geometry M m) (x : M)

def pathChartCore : ChartedSpaceCore (PathModel m) (HorizontalPaths Γ x) where
  atlas := range ControlChart.chart
  chartAt γ := (ControlChart.exists_chart γ).choose.chart
  mem_chart_source γ := (ControlChart.exists_chart γ).choose_spec
  chart_mem_atlas _ := mem_range_self _
  open_source := by
    rintro _ _ ⟨A,rfl⟩ ⟨B,rfl⟩
    exact isOpen_iff_mem_nhds.mpr (fun _ h => (A.transition B h).2)
  continuousOn_toFun := by
    rintro _ _ ⟨A,rfl⟩ ⟨B,rfl⟩ u hu
    exact (A.transition B hu).1.continuousAt.continuousWithinAt

instance pathTopology : TopologicalSpace (HorizontalPaths Γ x) := (pathChartCore Γ x).toTopologicalSpace
instance pathCharted : ChartedSpace (PathModel m) (HorizontalPaths Γ x) := (pathChartCore Γ x).toChartedSpace

private theorem atlas_rep {e : OpenPartialHomeomorph (HorizontalPaths Γ x) (PathModel m)}
    (h : e ∈ atlas (PathModel m) (HorizontalPaths Γ x)) : ∃ A : ControlChart Γ x, e.toPartialEquiv = A.chart := by
  change e ∈ ⋃ (a : PartialEquiv _ _) (ha : a ∈ (pathChartCore Γ x).atlas), {(pathChartCore Γ x).openPartialHomeomorph a ha} at h
  simp only [mem_iUnion,mem_singleton_iff] at h
  obtain ⟨_,⟨A,rfl⟩,rfl⟩ := h
  exact ⟨A,rfl⟩

instance pathSmooth : IsManifold 𝓘(ℝ,PathModel m) ∞ (HorizontalPaths Γ x) := by
  apply isManifold_of_contDiffOn
  intro a b ha hb
  obtain ⟨A,ea⟩ := atlas_rep Γ x ha
  obtain ⟨B,eb⟩ := atlas_rep Γ x hb
  intro u hu
  have hit : u ∈ (a.toPartialEquiv.symm.trans b.toPartialEquiv).source := hu.1
  rw [ea,eb] at hit
  have d := (A.transition B hit).1
  change ContDiffWithinAt ℝ ∞ (b.toPartialEquiv ∘ a.toPartialEquiv.symm) _ u
  rw [ea,eb]
  exact d.contDiffWithinAt

theorem path_eval_continuous (t : Time) : Continuous (fun γ : HorizontalPaths Γ x => γ.val t) := by
  apply continuous_iff_continuousAt.mpr
  intro γ
  let A := (ControlChart.exists_chart γ).choose
  obtain ⟨u,hu⟩ := (ControlChart.exists_chart γ).choose_spec
  have enc : A.encode γ = u := A.encode_eq hu
  let a := chartAt (PathModel m) γ
  have de : ContinuousAt (fun v => (A.decode v).val t) u := by
    apply tendsto_def.mpr
    intro V hV
    obtain ⟨U,sub,hU,inside⟩ := mem_nhds_iff.mp hV
    have hit : MapsTo (A.decode u).val {t} U := by
      intro s hs
      exact mem_singleton_iff.mp hs ▸ inside
    exact ((A.decode_family hu 1 le_rfl).1.maps_into {t} isCompact_singleton U hU hit).mono fun _ h => sub (h (mem_singleton t))
  have hc : ContinuousAt A.encode γ := a.continuousAt (mem_chart_source _ _)
  have d := (show ContinuousAt (fun v => (A.decode v).val t) (A.encode γ) from enc.symm ▸ de).comp hc
  apply d.congr_of_eventuallyEq
  filter_upwards [a.open_source.mem_nhds (mem_chart_source _ γ)] with β hβ
  exact congrArg (fun o : HorizontalPaths Γ x => o.val t) (a.left_inv hβ).symm

instance pathHausdorff : T2Space (HorizontalPaths Γ x) :=
  T2Space.of_injective_continuous (f := fun γ : HorizontalPaths Γ x => fun t : Time => γ.val t)
    (fun _ _ h => Subtype.ext (ContinuousMap.ext (congrFun h))) (continuous_pi (path_eval_continuous Γ x))

example : CompleteSpace (PathModel m) := inferInstance
example : InnerProductSpace ℝ (PathModel m) := inferInstance

#print axioms pathSmooth
#print axioms pathHausdorff
end MinimizingSard.Five
