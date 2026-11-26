import ChartSobolevPaths

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
open Volterra
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] {m : ℕ}

def SmoothObservation (H : M → State) : Prop :=
  ∀ c : OpenPartialHomeomorph M State, c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M → ContDiffOn ℝ ∞ (H ∘ c.symm) c.target

theorem smoothObservation_iff_frames (Γ : Geometry M m) (H : M → State) :
    SmoothObservation H ↔ ∀ e ∈ Γ.frames, ContDiffOn ℝ ∞ (H ∘ (e : Frame M m).chart.symm) e.chart.target := by
  refine ⟨fun h e _ => h e.chart e.compatible,?_⟩
  intro h c hc z hz
  let y := c.symm z
  obtain ⟨e,he,ey⟩ := Γ.cover y
  have reg := (compatible_of_mem_maximalAtlas hc e.compatible).1
  change ContDiffOn ℝ ∞ (e.chart ∘ c.symm) ((c.symm.trans e.chart).source ∩ range (𝓘(ℝ,State))) at reg
  have reg' : ContDiffOn ℝ ∞ (e.chart ∘ c.symm) (c.symm.trans e.chart).source := by simpa using reg
  have near := (c.symm.trans e.chart).open_source.mem_nhds (show z ∈ (c.symm.trans e.chart).source from ⟨hz,ey⟩)
  have dh := ((h e he) (e.chart y) (e.chart.map_source ey)).contDiffAt (e.chart.open_target.mem_nhds (e.chart.map_source ey))
  apply ((dh.comp z ((reg' z ⟨hz,ey⟩).contDiffAt near)).congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [near] with w hw
  exact congrArg H (e.chart.left_inv (show c.symm w ∈ e.chart.source from hw.2)).symm

def IsHorizontalH1 (Δ : (y : M) → Submodule ℝ (Tangent y)) (γ : C(Time,M)) : Prop :=
  ChartSobolev γ ∧ ∀ᵐ r ∂volume.restrict (Ioc (0:ℝ) 1), tangentVelocity γ r ∈ Δ (γ (clamp r))

structure IntrinsicVariation (Δ : (y : M) → Submodule ℝ (Tangent y)) (x : M) (F : ℝ → C(Time,M)) : Prop where
  continuous_family : ∀ K : Set Time, IsCompact K → ∀ U : Set M, IsOpen U → MapsTo (F 0) K U →
    ∀ᶠ r in 𝓝 0, MapsTo (F r) K U
  horizontal_family : ∀ᶠ r in 𝓝 0, F r (clamp 0) = x ∧ IsHorizontalH1 Δ (F r)
  differentiable_observations : ∀ H : M → State, SmoothObservation H →
    ∃ z : ℝ → SobolevData, DifferentiableAt ℝ z 0 ∧ ∀ᶠ r in 𝓝 0, ∀ t, ambientPath (z r) t = H (F r t)

def IntrinsicCritical (Δ : (y : M) → Submodule ℝ (Tangent y)) (x : M) (γ : C(Time,M)) : Prop :=
  ∃ c : OpenPartialHomeomorph M State, c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M ∧ γ (clamp 1) ∈ c.source ∧
    ∃ η : State →L[ℝ] ℝ, η ≠ 0 ∧ ∀ F : ℝ → C(Time,M), F 0 = γ → IntrinsicVariation Δ x F →
      DifferentiableAt ℝ (fun r => c (F r (clamp 1))) 0 → η (deriv (fun r => c (F r (clamp 1))) 0) = 0

def intrinsicMinEndpoints (Δ : (y : M) → Submodule ℝ (Tangent y)) (g : (y : M) → Δ y → ℝ) (x : M) : Set M :=
  {y | ∃ γ : C(Time,M), γ (clamp 0) = x ∧ γ (clamp 1) = y ∧ IsHorizontalH1 Δ γ ∧ IntrinsicCritical Δ x γ ∧
    ∀ β : C(Time,M), β (clamp 0) = x → β (clamp 1) = y → IsHorizontalH1 Δ β → tangentLength Δ g γ ≤ tangentLength Δ g β}

variable [T2Space M] [IsManifold 𝓘(ℝ,State) ∞ M]
theorem intrinsic_critical_iff {Γ : Geometry M m} {Δ : (y : M) → Submodule ℝ (Tangent y)} {g : (y : M) → Δ y → ℝ}
    (metric : ∀ e ∈ Γ.frames, RepresentsMetric e Δ g) (x : M) (γ : C(Time,M)) :
    IntrinsicCritical Δ x γ ↔ ObservationCritical Γ x γ := by
  have eq (F : ℝ → C(Time,M)) : IntrinsicVariation Δ x F ↔ ObservationVariation Γ x F := by
    have path (β : C(Time,M)) : IsHorizontalH1 Δ β ↔ ∃ l, PathHasLength Γ β l := by
      refine ⟨fun h => ⟨_,(path_length_iff_intrinsic metric _ _).mpr ⟨h.1,h.2,rfl⟩⟩,?_⟩
      rintro ⟨l,h⟩
      exact ⟨h.chart_sobolev,(h.tangent_metric metric).1⟩
    constructor
    · rintro ⟨ct,hr,obs⟩
      exact ⟨ct,hr.mono (fun r h => ⟨h.1,(path _).mp h.2⟩),fun H h => obs H ((smoothObservation_iff_frames _ _).mpr h)⟩
    · rintro ⟨ct,hr,obs⟩
      exact ⟨ct,hr.mono (fun r h => ⟨h.1,(path _).mpr h.2⟩),fun H h => obs H ((smoothObservation_iff_frames _ _).mp h)⟩
  unfold IntrinsicCritical ObservationCritical
  simp only [eq]

/-- In every valid presentation the chart-independent intrinsic critical
test is exactly non-surjectivity of the whole endpoint Fréchet derivative.
The endpoint germ is constructed from the actual path. -/
theorem intrinsic_critical_full_endpoint {Γ : Geometry M m} {Δ : (y : M) → Submodule ℝ (Tangent y)} {g : (y : M) → Δ y → ℝ}
    (metric : ∀ e ∈ Γ.frames, RepresentsMetric e Δ g) {n : ℕ} (x : M) (γ : C(Time,M))
    (P : TimePartition (n+1)) (e : Fin (n+1) → Frame M m) (p : Fin (n+1) → SobolevData) (u : Fin (n+1) → Control m)
    (he : ∀ i, e i ∈ Γ.frames) (path : SobolevJoins e p x (γ (clamp 1))) (rep : RepresentsPath P e p γ)
    (codes : FrameCodes e p u) (c : OpenPartialHomeomorph M State) (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M)
    (cy : γ (clamp 1) ∈ c.source) :
    ∃ G : (Fin (n+1) → Control m) → State, DifferentiableAt ℝ G u ∧ G u = c (γ (clamp 1)) ∧
      (∀ᶠ v in 𝓝 u, G v ∈ c.target ∧ ∀ b, Joins e v x b ↔ b = c.symm (G v)) ∧
      (IntrinsicCritical Δ x γ ↔ ¬ Function.Surjective (fderiv ℝ G u)) := by
  obtain ⟨_,_,G,_,_,gu,_,_,dG,localG,_⟩ := sobolev_chain_chart e p u x _ path codes c hc cy 1 le_rfl
  have dg := dG.differentiableAt (by decide)
  have graph : ∀ᶠ v in 𝓝 u, G v ∈ c.target ∧ ∀ b, Joins e v x b ↔ b = c.symm (G v) := localG.mono (fun _ h => ⟨h.1,h.2.1⟩)
  refine ⟨G,dg,gu,graph,?_⟩
  rw [intrinsic_critical_iff metric,observationCritical_iff_full_derivative he path rep codes,singular_iff_in_chart e u x _ c hc cy]
  refine ⟨?_,fun bad => ⟨G,_,gu,graph,dg.hasFDerivAt,bad⟩⟩
  rintro ⟨H,D,_,gh,dh,bad⟩
  have same : H =ᶠ[𝓝 u] G := by
    filter_upwards [gh,graph] with v hv gv
    exact c.symm.injOn hv.1 gv.1 ((gv.2 _).mp ((hv.2 _).mpr rfl))
  rwa [← same.fderiv_eq,dh.fderiv]

theorem intrinsic_endpoints_eq {Γ : Geometry M m} {Δ : (y : M) → Submodule ℝ (Tangent y)} {g : (y : M) → Δ y → ℝ}
    (metric : ∀ e ∈ Γ.frames, RepresentsMetric e Δ g) (x : M) :
    intrinsicMinEndpoints Δ g x = singularMinEndpoints Γ x := by
  rw [← observed_endpoints_eq]
  have cost (γ : HorizontalPaths Γ x) : tangentLength Δ g γ.val = γ.metricLength :=
    (γ.property.2.choose_spec.tangent_metric metric).2
  ext y
  constructor
  · rintro ⟨γ,src,dst,hor,crit,minimal⟩
    have path := (path_length_iff_intrinsic metric γ _).mpr ⟨hor.1,hor.2,rfl⟩
    let ξ : HorizontalPaths Γ x := ⟨γ,src,_,path⟩
    refine ⟨ξ,dst,(intrinsic_critical_iff metric _ _).mp crit,?_⟩
    intro β by'
    rw [← cost ξ,← cost β]
    exact minimal β.val β.property.1 by' ⟨β.property.2.choose_spec.chart_sobolev,(β.property.2.choose_spec.tangent_metric metric).1⟩
  · rintro ⟨γ,dst,crit,minimal⟩
    have hor := γ.property.2.choose_spec
    refine ⟨γ.val,γ.property.1,dst,⟨hor.chart_sobolev,(hor.tangent_metric metric).1⟩,(intrinsic_critical_iff metric _ _).mpr crit,?_⟩
    intro β src by' bh
    have path := (path_length_iff_intrinsic metric β _).mpr ⟨bh.1,bh.2,rfl⟩
    let ξ : HorizontalPaths Γ x := ⟨β,src,_,path⟩
    exact (cost γ).trans_le ((minimal ξ by').trans_eq (ξ.length_in_chart path))

/-- The null endpoint set mentions only the actual tangent distribution,
its metric, the source and actual curves on [0,1]. -/
theorem five_dimensional_intrinsic_curve_sard [SecondCountableTopology M] [ConnectedSpace M] [MeasurableSpace M]
    (m : ℕ) (hm : 0 < m) (h5 : m < 5) (Δ : (y : M) → Submodule ℝ (Tangent y)) (g : (y : M) → Δ y → ℝ)
    (smooth_generating : HasBundleCoordinates m Δ g) (x : M) (μ : Measure M) (density : HasSmoothDensity μ) :
    μ (intrinsicMinEndpoints Δ g x) = 0 := by
  let Γ := bundleGeometry smooth_generating hm
  have metric (e) (he : e ∈ Γ.frames) : RepresentsMetric e Δ g := he
  rw [intrinsic_endpoints_eq metric]
  exact measure_zero_of_chart_null μ density _ (five_dimensional_frame_sard (M := M) m hm h5 Γ x)

#print axioms intrinsic_critical_iff
#print axioms intrinsic_critical_full_endpoint
#print axioms intrinsic_endpoints_eq
#print axioms five_dimensional_intrinsic_curve_sard
end MinimizingSard.Five
