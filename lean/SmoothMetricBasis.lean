import FiveDimensionalStatement
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace MinimizingSard.Five
variable {m : ℕ}
abbrev FiberMetric (m : ℕ) := InnerProductSpace.Core ℝ (Fiber m)
private def std (i : Fin m) : Fiber m := (Pi.basisFun ℝ (Fin m)) i

private def gramVector (G : FiberMetric m) (i : Fin m) : Fiber m := by
  letI := G.toNormedAddCommGroup
  letI := InnerProductSpace.ofCore G
  exact InnerProductSpace.gramSchmidt ℝ std i

private def gramUnit (G : FiberMetric m) (i : Fin m) : Fiber m :=
  (Real.sqrt (G.inner (gramVector G i) (gramVector G i)))⁻¹ • gramVector G i

private theorem gram_rec (G : FiberMetric m) (j : Fin m) :
    gramVector G j = std j - ∑ i ∈ Finset.Iio j,
      (G.inner (gramVector G i) (std j) / G.inner (gramVector G i) (gramVector G i)) • gramVector G i := by
  letI := G.toNormedAddCommGroup
  letI := InnerProductSpace.ofCore G
  have h := InnerProductSpace.gramSchmidt_def'' ℝ (std : Fin m → Fiber m) j
  apply eq_sub_of_add_eq
  change _ + _ = std j
  change std j = gramVector G j + ∑ i ∈ Finset.Iio j,
    (G.inner (gramVector G i) (std j) / (Real.sqrt (G.inner (gramVector G i) (gramVector G i)))^2) • gramVector G i at h
  have sq (v : Fiber m) : (Real.sqrt (G.inner v v))^2 = G.inner v v := Real.sq_sqrt (G.re_inner_nonneg v)
  simpa only [sq] using h.symm

private theorem gram_pos (G : FiberMetric m) (i : Fin m) :
    0 < G.inner (gramVector G i) (gramVector G i) := by
  letI := G.toNormedAddCommGroup
  letI := InnerProductSpace.ofCore G
  apply real_inner_self_pos.mpr
  apply InnerProductSpace.gramSchmidt_ne_zero
  exact (Pi.basisFun ℝ (Fin m)).linearIndependent

set_option maxHeartbeats 1200000 in
private theorem gram_orthogonal (G : FiberMetric m) (i j : Fin m) :
    G.inner (gramUnit G i) (gramUnit G j) = if i = j then 1 else 0 := by
  letI := G.toNormedAddCommGroup
  letI := InnerProductSpace.ofCore G
  have on := InnerProductSpace.gramSchmidtNormed_orthonormal (𝕜 := ℝ) (f := std) (Pi.basisFun ℝ (Fin m)).linearIndependent
  letI : SeminormedAddCommGroup (Fiber m) := G.toNormedAddCommGroup.toSeminormedAddCommGroup
  exact (orthonormal_iff_ite (v := InnerProductSpace.gramSchmidtNormed ℝ std) (𝕜 := ℝ)).mp on i j

private theorem gram_basis (G : FiberMetric m) : LinearIndependent ℝ (gramUnit G) := by
  letI := G.toNormedAddCommGroup
  letI := InnerProductSpace.ofCore G
  exact InnerProductSpace.gramSchmidtNormed_linearIndependent (𝕜 := ℝ) (f := std) (Pi.basisFun ℝ (Fin m)).linearIndependent

/-- A smooth varying positive-definite inner product in an arbitrary
local bundle basis has a smooth orthonormal basis. The smoothness refers
to the original fixed coordinate topology on the fibers. -/
theorem smooth_metric_basis (O : Set State) (G : State → FiberMetric m)
    (smooth : ContDiffOn ℝ ∞ (fun p : State × (Fiber m × Fiber m) => (G p.1).inner p.2.1 p.2.2)
      (O ×ˢ univ)) :
    ∃ B : Fin m → State → Fiber m, (∀ i, ContDiffOn ℝ ∞ (B i) O) ∧
      (∀ z, LinearIndependent ℝ (fun i => B i z)) ∧ ∀ z i j, (G z).inner (B i z) (B j z) = if i = j then 1 else 0 := by
  have pairing {A B : State → Fiber m} (ca : ContDiffOn ℝ ∞ A O) (cb : ContDiffOn ℝ ∞ B O) :
      ContDiffOn ℝ ∞ (fun z => (G z).inner (A z) (B z)) O :=
    smooth.comp (contDiffOn_id.prodMk (ca.prodMk cb)) (fun z hz => ⟨hz,mem_univ _⟩)
  have reg (j : Fin m) : ContDiffOn ℝ ∞ (fun z => gramVector (G z) j) O := by
    induction j using WellFoundedLT.induction with
    | ind j ih =>
      simp_rw [gram_rec _ j]
      apply contDiffOn_const.sub
      apply ContDiffOn.sum
      intro i hi
      have prev := ih i (Finset.mem_Iio.mp hi)
      exact ((pairing prev contDiffOn_const).div (pairing prev prev) (fun z _ => (gram_pos (G z) i).ne')).smul prev
  refine ⟨fun i z => gramUnit (G z) i,fun i => ?_,fun z => gram_basis (G z),fun z => gram_orthogonal (G z)⟩
  have pos := fun z => gram_pos (G z) i
  exact (((pairing (reg i) (reg i)).sqrt (fun z _ => (pos z).ne')).inv (fun z _ => (Real.sqrt_pos.mpr (pos z)).ne')).smul (reg i)

#print axioms smooth_metric_basis
end MinimizingSard.Five
