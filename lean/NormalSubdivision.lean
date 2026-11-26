import TubeAdjoint
import LengthSubdivision
import SupportedControlDensity

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology
namespace MinimizingSard.Five
open Volterra
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M]

/-- A single input threshold supplies reference tubes over a compact subset
of the frame. The center and radius may vary with the starting coordinate. -/
theorem compact_reference_tubes (e : Frame M 2) (K : Set State) (compact : IsCompact K)
    (inside : K ⊆ e.chart.target) :
    ∃ ε > 0, ∀ k ∈ K, ∀ u : Control 2, ‖u‖ < ε →
      ∃ q r P, k ∈ ball q r ∧ ReferenceTube e q r u P := by
  let V := {b : State × Control 2 | ∃ q r P, b.1 ∈ ball q r ∧ ReferenceTube e q r b.2 P}
  have inc : K ×ˢ {(0 : Control 2)} ⊆ interior V := by
    rintro ⟨k,u⟩ ⟨hk,hu⟩
    change u = 0 at hu
    subst u
    obtain ⟨r,hr,small⟩ := exists_reference_tube e (inside hk)
    apply mem_interior_iff_mem_nhds.mpr
    have nb := (isOpen_ball.prod (isOpen_ball (x := (0 : Control 2)) (ε := r))).mem_nhds
      (show (k,(0 : Control 2)) ∈ ball k r ×ˢ ball 0 r from ⟨mem_ball_self hr,mem_ball_self hr⟩)
    filter_upwards [nb] with b hb
    obtain ⟨P,tube⟩ := small b.2 (by simpa only [mem_ball,dist_zero_right] using hb.2)
    exact ⟨k,r,P,hb.1,tube⟩
  obtain ⟨s,w,_,hw,ks,w0,sw⟩ := generalized_tube_lemma compact isCompact_singleton isOpen_interior inc
  obtain ⟨ε,positive,sub⟩ := Metric.mem_nhds_iff.mp (hw.mem_nhds (w0 (mem_singleton _)))
  refine ⟨ε,positive,?_⟩
  intro k hk u hu
  have ub : u ∈ ball (0 : Control 2) ε := by rwa [mem_ball,dist_zero_right]
  have member : (k,u) ∈ interior V := sw ⟨ks hk,sub ub⟩
  exact (interior_subset : interior V ⊆ V) member

/-- One subdivision works for the whole reference segment. Its bounded linear
change of controls is onto and preserves length and the endpoint relation
for every perturbed input. Each reference piece has its actual two endpoints. -/
theorem segment_reference_tubes (e : Frame M 2) (u : Control 2) {x y : M}
    (seg : Segment e u x y) :
    ∃ n, ∃ R : Control 2 ≃L[ℝ] (Fin n → Control 2), ∃ k : Fin (n+1) → State,
      k 0 = e.chart x ∧ k (Fin.last n) = e.chart y ∧
      (∀ j, k j ∈ e.chart.target) ∧
      (∀ v, length (R v) = pieceLength v) ∧
      (∀ v a b, Segment e v a b ↔ Joins (fun _ => e) (R v) a b) ∧
      ∀ i, ∃ q r P, k i.castSucc ∈ ball q r ∧ ReferenceTube e q r (R u i) P ∧
        P (k i.castSucc) (clamp 1) = k i.succ := by
  obtain ⟨hx,hy,z,cz,mz,start,stop,integ,ode⟩ := seg
  obtain ⟨ε,hε,small⟩ := compact_reference_tubes e (z '' Icc 0 1)
    (isCompact_Icc.image_of_continuousOn cz) (image_subset_iff.mpr mz)
  have pos : 0 < ‖u‖^2+1 := by positivity
  obtain ⟨n,T,mesh⟩ := fine_partition (div_pos (sq_pos_of_pos hε) pos)
  obtain ⟨R,rep,graph⟩ := T.segment_iff_joins e
  let k (j : Fin (n+1)) := z (T.cut j)
  have kt j : k j ∈ e.chart.target := mz (T.cut_mem j)
  refine ⟨n,R,k,by simpa [k,T.first] using start,by simpa [k,T.last] using stop,kt,?_,graph,?_⟩
  · intro v
    rw [T.length_eq_of_rescaling v (R v) (rep v),length_pieces,Fin.sum_univ_one]
  · intro i
    obtain ⟨v,repr,bound,actual⟩ := subsegment e u z cz mz integ ode
      (T.cut_mem i.castSucc).1 (T.duration_pos i) ((T.end_eq i).symm ▸ (T.cut_mem i.succ).2)
    have same : v = R u i := by
      apply Lp.ext
      filter_upwards [repr,rep u i] with s h hs using h.trans hs.symm
    change Segment e v (e.chart.symm (z (T.left i))) (e.chart.symm (z (T.left i+T.duration i))) at actual
    rw [same,T.end_eq] at actual
    change Segment e (R u i) (e.chart.symm (k i.castSucc)) (e.chart.symm (k i.succ)) at actual
    rw [same] at bound
    have mesh' := (lt_div_iff₀ pos).mp (mesh i)
    have smallv : ‖R u i‖ < ε := by nlinarith [sq_nonneg (‖R u i‖-ε),T.duration_pos i]
    obtain ⟨q,r,P,hk,tube⟩ := small (k i.castSucc) ⟨_,T.cut_mem _,rfl⟩ _ smallv
    refine ⟨q,r,P,hk,tube,?_⟩
    obtain ⟨G,_,near⟩ := arbitrary_segment_graph e _ _ _ actual 1 (by decide)
    change ∀ᶠ b in 𝓝 (e.chart (e.chart.symm (k i.castSucc)),R u i), _ at near
    rw [e.chart.right_inv (kt _)] at near
    have eq := ((near.self_of_nhds.2.2 _).mp (tube_segment e tube hk)).trans
      ((near.self_of_nhds.2.2 _).mp actual).symm
    simpa only [e.chart.right_inv (kt _),e.chart.right_inv (tube.chart _ (ball_subset_closedBall hk) _)] using congrArg e.chart eq

#print axioms compact_reference_tubes
#print axioms segment_reference_tubes
end MinimizingSard.Five
