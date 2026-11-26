import SmoothBundleGeometry

noncomputable section
open Set Filter IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] {m : ℕ}
variable {Δ : (y : M) → Submodule ℝ (Tangent y)}

private abbrev basisVector (i : Fin m) := Pi.basisFun ℝ (Fin m) i

/-- A local basis of the horizontal tangent spaces, with scalar Gram coefficients
of the specified bilinear metric in that basis. -/
structure MetricBasisChart (m : ℕ) (Δ : (y : M) → Submodule ℝ (Tangent y))
    (g : (y : M) → InnerProductSpace.Core ℝ (Δ y)) where
  chart : OpenPartialHomeomorph M State
  compatible : chart ∈ maximalAtlas 𝓘(ℝ,State) ∞ M
  columns : State → Fiber m →L[ℝ] State
  smooth : ContDiffOn ℝ ∞ columns chart.target
  basis : ∀ y ∈ chart.source, Fiber m ≃ₗ[ℝ] Δ y
  tangent : ∀ y (hy : y ∈ chart.source) u, (basis y hy u : Tangent y) =
    fderiv ℝ ((chartAt State y) ∘ chart.symm) (chart y) (columns (chart y) u)
  gram : Fin m → Fin m → State → ℝ
  smooth_gram : ∀ i j, ContDiffOn ℝ ∞ (gram i j) chart.target
  entries : ∀ y (hy : y ∈ chart.source) i j, (g y).inner (basis y hy (basisVector i)) (basis y hy (basisVector j)) =
    gram i j (chart y)
  generating : ∀ z ∈ chart.target,
    Submodule.span ℝ {v | ∃ V, SectionLie (fun p => LinearMap.range (columns p).toLinearMap) z V ∧ V z = v} = ⊤

private def pullMetric {F : Type*} [AddCommGroup F] [Module ℝ F] (G : InnerProductSpace.Core ℝ F)
    (L : Fiber m ≃ₗ[ℝ] F) : FiberMetric m where
  inner u v := G.inner (L u) (L v)
  conj_inner_symm u v := G.conj_inner_symm _ _
  re_inner_nonneg u := G.re_inner_nonneg _
  add_left u v w := by rw [map_add,G.add_left]
  smul_left u v r := by rw [map_smul,G.smul_left]
  definite u h := L.injective ((G.definite _ h).trans (map_zero L).symm)

private theorem pairing_coordinates (G : FiberMetric m) (u v : Fiber m) :
    G.inner u v = ∑ i, ∑ j, u i * (v j * G.inner (basisVector i) (basisVector j)) := by
  letI := G.toNormedAddCommGroup
  letI := InnerProductSpace.ofCore G
  letI : SeminormedAddCommGroup (Fiber m) := G.toNormedAddCommGroup.toSeminormedAddCommGroup
  have expand (w : Fiber m) : ∑ i, w i • basisVector i = w := (Pi.basisFun ℝ (Fin m)).sum_repr w
  calc
    _ = inner ℝ (∑ i, u i • basisVector i) (∑ j, v j • basisVector j) := by rw [expand,expand]
    _ = _ := by
      rw [sum_inner]
      simp only [inner_sum,real_inner_smul_left,real_inner_smul_right,mul_left_comm]

variable {g : (y : M) → InnerProductSpace.Core ℝ (Δ y)}

theorem MetricBasisChart.to_bundle (b : MetricBasisChart m Δ g) {root : M} (hroot : root ∈ b.chart.source) :
    ∃ d : BundleCoordinates m Δ (fun y v => (g y).inner v v), d.chart = b.chart := by
  classical
  let G (z : State) : FiberMetric m := if hz : z ∈ b.chart.target then
    pullMetric (g (b.chart.symm z)) (b.basis _ (b.chart.map_target hz)) else pullMetric (g root) (b.basis root hroot)
  have atY (y : M) (hy : y ∈ b.chart.source) : G (b.chart y) = pullMetric (g y) (b.basis y hy) := by
    simp only [G,dif_pos (b.chart.map_source hy)]
    exact congrArg (fun s : b.chart.source => pullMetric (g s.val) (b.basis s.val s.property))
      (Subtype.ext (b.chart.left_inv hy) : (⟨_,b.chart.map_target (b.chart.map_source hy)⟩ : b.chart.source) = ⟨y,hy⟩)
  have entries (z : State) (hz : z ∈ b.chart.target) (i j) : (G z).inner (basisVector i) (basisVector j) = b.gram i j z := by
    have eq := b.entries (b.chart.symm z) (b.chart.map_target hz) i j
    simpa only [G,dif_pos hz,pullMetric,b.chart.right_inv hz] using eq
  let O := b.chart.target ×ˢ (univ : Set (Fiber m × Fiber m))
  have cf (i j : Fin m) : ContDiffOn ℝ ∞ (fun p : State × (Fiber m × Fiber m) => p.2.1 i * (p.2.2 j * b.gram i j p.1)) O :=
    (((ContinuousLinearMap.proj i : Fiber m →L[ℝ] ℝ).contDiff.comp (contDiff_fst.comp contDiff_snd)).contDiffOn).mul
      ((((ContinuousLinearMap.proj j : Fiber m →L[ℝ] ℝ).contDiff.comp (contDiff_snd.comp contDiff_snd)).contDiffOn).mul
        ((b.smooth_gram i j).comp contDiffOn_fst (fun _ h => h.1)))
  refine ⟨⟨b.chart,b.compatible,b.columns,b.smooth,G,?_,?_,b.generating⟩,rfl⟩
  · apply (ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ => cf i j))).congr
    intro p hp
    rw [pairing_coordinates]
    simp only [entries _ hp.1]
    rfl
  · intro y hy
    refine ⟨b.basis y hy,fun u => ⟨b.tangent y hy u,?_⟩⟩
    rw [atY]
    rfl

def HasSmoothMetricBasis (m : ℕ) (Δ : (y : M) → Submodule ℝ (Tangent y)) (g : (y : M) → InnerProductSpace.Core ℝ (Δ y)) : Prop :=
  ∀ y : M, ∃ b : MetricBasisChart m Δ g, y ∈ b.chart.source

theorem HasSmoothMetricBasis.coordinates (h : HasSmoothMetricBasis m Δ g) :
    HasBundleCoordinates m Δ (fun y v => (g y).inner v v) := by
  intro y
  obtain ⟨b,hy⟩ := h y
  obtain ⟨d,eq⟩ := b.to_bundle hy
  exact ⟨d,eq.symm ▸ hy⟩

private theorem polarization {F : Type*} [AddCommGroup F] [Module ℝ F] (G : InnerProductSpace.Core ℝ F) (u v : F) :
    G.inner (u+v) (u+v) = G.inner u u + 2 * G.inner u v + G.inner v v := by
  have symm (a b : F) : G.inner a b = G.inner b a := G.conj_inner_symm b a
  have addR (a b c : F) : G.inner a (b+c) = G.inner a b + G.inner a c := by
    rw [symm a,G.add_left,symm b a,symm c a]
  rw [G.add_left,addR,addR,symm v u]
  ring

/-- The scalar Gram coefficient formulation and the joint quadratic-speed
formulation admit exactly the same smooth bundle geometries for a given metric. -/
theorem metric_basis_iff (m : ℕ) (Δ : (y : M) → Submodule ℝ (Tangent y)) (g : (y : M) → InnerProductSpace.Core ℝ (Δ y)) :
    HasSmoothMetricBasis m Δ g ↔ HasBundleCoordinates m Δ (fun y v => (g y).inner v v) := by
  refine ⟨HasSmoothMetricBasis.coordinates,?_⟩
  intro h y
  obtain ⟨b,hit⟩ := h y
  choose L spec using b.fiber
  let gram (i j : Fin m) (z : State) := (b.metric z).inner (basisVector i) (basisVector j)
  have sm (i j) : ContDiffOn ℝ ∞ (gram i j) b.chart.target :=
    b.metric_smooth.comp (contDiffOn_id.prodMk (contDiffOn_const (c := (basisVector i,basisVector j)))) (fun z hz => ⟨hz,mem_univ _⟩)
  have entry (z) (hz : z ∈ b.chart.source) (u v : Fiber m) :
      (g z).inner (L z hz u) (L z hz v) = (b.metric (b.chart z)).inner u v := by
    have eq := (spec z hz (u+v)).2
    change (g z).inner (L z hz (u+v)) (L z hz (u+v)) = _ at eq
    rw [map_add,polarization,polarization] at eq
    have s := (spec z hz u).2
    have t := (spec z hz v).2
    linarith
  exact ⟨⟨b.chart,b.compatible,b.columns,b.smooth,L,fun z hz u => (spec z hz u).1,gram,sm,
    fun z hz i j => entry z hz _ _,b.generating⟩,hit⟩

#print axioms metric_basis_iff
#print axioms MetricBasisChart.to_bundle
#print axioms HasSmoothMetricBasis.coordinates
end MinimizingSard.Five
