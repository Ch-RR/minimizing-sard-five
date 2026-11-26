import TubeNormalEquation
import ChainAdjoint
import NormalSubdivision

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology
namespace MinimizingSard.Five
open Volterra
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M]

/-- The lifted equations use the speed of the supplied control in its original
time. In particular these equations also prescribe its zero-speed intervals. -/
structure NormalPiece {m : ℕ} (e : Frame M m) (u : Control m) (z : C(Time,Phase)) : Prop where
  inside : ∀ t, (z t).1 ∈ e.chart.target
  align : ∀ᵐ t ∂controlMeasure, u t = Real.sqrt (speedSq (u t)) • normalCoefficients e.X (z (clamp t))
  primitive : ∀ t ∈ Icc (0:ℝ) 1, z (clamp t) = z (clamp 0) +
    ∫ s in (0:ℝ)..t, Real.sqrt (speedSq (u s)) • hamiltonianField e.X (z (clamp s))

/-- A supporter on an arbitrary original segment lifts to a finite chain of
normal pieces. Their covectors match at every joint. The incoming covector
is the pullback by the differential in the original initial state. -/
theorem normal_segment_lift (e : Frame M 2) (u : Control 2) {x y : M}
    (seg : Segment e u x y) (G : State × Control 2 → State)
    (dg : DifferentiableAt ℝ G (e.chart x,u))
    (graph : ∀ᶠ b in 𝓝 (e.chart x,u), b.1 ∈ e.chart.target ∧ G b ∈ e.chart.target ∧
      ∀ y, Segment e b.2 (e.chart.symm b.1) y ↔ y = e.chart.symm (G b))
    (η : State →L[ℝ] ℝ)
    (support : ∀ v, pieceLength u + η (fderiv ℝ G (e.chart x,u) (0,v-u)) ≤ pieceLength v) :
    ∃ n, ∃ R : Control 2 ≃L[ℝ] (Fin n → Control 2), ∃ k : Fin (n+1) → State,
    ∃ p : Fin (n+1) → State →L[ℝ] ℝ, ∃ Z : Fin n → C(Time,Phase),
      k 0 = e.chart x ∧ k (Fin.last n) = e.chart y ∧ p (Fin.last n) = η ∧
      (∀ h, p 0 h = η (fderiv ℝ G (e.chart x,u) (h,0))) ∧
      (∀ v, length (R v) = pieceLength v) ∧
      (∀ v a b, Segment e v a b ↔ Joins (fun _ => e) (R v) a b) ∧
      ∀ i, Z i (clamp 0) = (k i.castSucc,p i.castSucc) ∧
        Z i (clamp 1) = (k i.succ,p i.succ) ∧ NormalPiece e (R u i) (Z i) := by
  classical
  obtain ⟨n,R,k,k0,kn,kt,cost,joins,parts⟩ := segment_reference_tubes e u seg
  choose centers radii P hk tube endk using parts
  let node j := e.chart.symm (k j)
  have coord (j) : e.chart (node j) = k j := e.chart.right_inv (kt j)
  have edge (i : Fin n) : Segment e (R u i) (node i.castSucc) (node i.succ) := by
    simpa only [node,← endk i] using tube_segment e (tube i) (hk i)
  choose H sm hg using fun i => arbitrary_segment_graph e (R u i) _ _ (edge i) 1 (by decide)
  let U := Fin n → Control 2
  let T : State × U →L[ℝ] State × Control 2 := (ContinuousLinearMap.id ℝ State).prodMap R.symm.toContinuousLinearMap
  have base : T (k 0,R u) = (e.chart x,u) := Prod.ext k0 (R.symm_apply_apply u)
  have pull : ∀ᶠ b : State × U in 𝓝 (k 0,R u), b.1 ∈ e.chart.target ∧ G (T b) ∈ e.chart.target ∧
      ∀ y, Joins (fun _ : Fin n => e) b.2 (e.chart.symm b.1) y ↔ y = e.chart.symm (G (T b)) := by
    have tend := T.continuous.tendsto (k 0,R u)
    rw [base] at tend
    filter_upwards [tend graph] with b hb
    refine ⟨hb.1,hb.2.1,fun y => ?_⟩
    have eq := joins (R.symm b.2) (e.chart.symm b.1) y
    rw [R.apply_symm_apply] at eq
    exact eq.symm.trans (hb.2.2 y)
  let C := chainNode H (Fin.last n)
  obtain ⟨_,dC,cGraph⟩ := prescribed_composite_graph (fun _ : Fin n => e) (fun _ => e.chart)
    (R u) node (fun j => e.chart.map_target (kt j)) edge H sm hg
  rw [coord] at dC cGraph
  have same : G ∘ T =ᶠ[𝓝 (k 0,R u)] C := by
    filter_upwards [pull,cGraph] with b h hc
    have eq := (hc.2.2 _).mp ((h.2.2 _).mpr rfl)
    exact (e.chart.right_inv h.2.1).symm.trans ((congrArg e.chart eq).trans (e.chart.right_inv hc.2.1))
  have deriv := ((base.symm ▸ dg.hasFDerivAt).comp (k 0,R u) T.hasFDerivAt).congr_of_eventuallyEq same.symm
  have slope (h : State) (v : U) : fderiv ℝ C (k 0,R u) (h,v) = fderiv ℝ G (e.chart x,u) (h,R.symm v) :=
    by simpa only [base] using DFunLike.congr_fun deriv.fderiv (h,v)
  let F : U → State := fun v => C (k 0,v)
  have inc : HasFDerivAt (fun v : U => (k 0,v)) (ContinuousLinearMap.inr ℝ State U) (R u) :=
    (hasFDerivAt_const _ _).prodMk (hasFDerivAt_id _)
  have dF : ∀ v, fderiv ℝ F (R u) v = fderiv ℝ G (e.chart x,u) (0,R.symm v) := fun v =>
    by simpa only [base] using DFunLike.congr_fun (deriv.comp (R u) inc).fderiv v
  have full : ∀ᶠ v in 𝓝 (R u), F v ∈ e.chart.target ∧
      ∀ y, Joins (fun _ : Fin n => e) v (node 0) y ↔ y = e.chart.symm (F v) := by
    filter_upwards [inc.continuousAt.tendsto cGraph] with v h using h.2
  have fine (v : U) : length (R u) + η (fderiv ℝ F (R u) (v-R u)) ≤ length v := by
    rw [dF,map_sub,R.symm_apply_apply,cost,← R.apply_symm_apply v,cost]
    simpa only [R.symm_apply_apply] using support (R.symm v)
  obtain ⟨p,pn,prev,first,piece⟩ := supported_chain (fun _ : Fin n => e) (fun _ => e.chart)
    (R u) node (fun j => e.chart.map_target (kt j)) edge H sm hg F full η fine
  simp_rw [coord] at prev first piece sm hg
  let Z (i : Fin n) : C(Time,Phase) := (P i (k i.castSucc)).prodMk
    ⟨tubeAdjoint (P i) (k i.castSucc) (p i.succ),(tube_adjoint_endpoints e (tube i) (hk i) _).1⟩
  refine ⟨n,R,k,p,Z,k0,kn,pn,?_,cost,joins,?_⟩
  · intro h
    rw [← first,slope,map_zero]
  · intro i
    have df := (sm i).differentiableAt (by decide)
    have initial := (tube_endpoint_first_variation e (tube i) (hk i) (H i) df (hg i) (p i.succ)).1
    have cov : tubeAdjoint (P i) (k i.castSucc) (p i.succ) (clamp 0) = p i.castSucc :=
      ContinuousLinearMap.ext fun h => (initial h).symm.trans (prev i h).symm
    have orbit := supported_tube_hamiltonian e (tube i) (hk i) (H i) df (hg i) (p i.succ) (piece i)
    exact ⟨Prod.ext ((tube i).initial _ (ball_subset_closedBall (hk i))) cov,
      Prod.ext (endk i) (tube_adjoint_endpoints e (tube i) (hk i) _).2.1,
      ⟨(tube i).chart _ (ball_subset_closedBall (hk i)),orbit.1,orbit.2⟩⟩

#print axioms normal_segment_lift
end MinimizingSard.Five
