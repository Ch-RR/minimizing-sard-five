import SobolevAtlasOverlap
import FrameMinimizingSard

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
open Volterra
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] {m n : ℕ}
abbrev SobolevData := State × Control 5

/-- A horizontal chart piece with endpoints in the manifold, specified
only by its initial coordinate and ambient weak velocity. -/
def SobolevEdge (e : Frame M m) (p : SobolevData) (x y : M) :=
  x ∈ e.chart.source ∧ y ∈ e.chart.source ∧ p.1 = e.chart x ∧
    ambientPath p (clamp 1) = e.chart y ∧ e.HorizontalSobolev p

def SobolevJoins (e : Fin n → Frame M m) (p : Fin n → SobolevData) (x y : M) :=
  ∃ q : Fin (n+1) → M, q 0 = x ∧ q (Fin.last n) = y ∧ ∀ i, SobolevEdge (e i) (p i) (q i.castSucc) (q i.succ)

def sobolevLength (e : Fin n → Frame M m) (p : Fin n → SobolevData) : ℝ :=
  ∑ i, ∫ r in (0:ℝ)..1, Real.sqrt ((e i).rawSpeedSq (p i) r)

/-- A smooth curve test in the subspace of ambient Sobolev data. It
quantifies over all differentiable variations fixing the initial state,
with variable common nodes and with an unrestricted terminal endpoint. -/
def SobolevSingular (e : Fin n → Frame M m) (p : Fin n → SobolevData) (x y : M) : Prop :=
  ∃ c : OpenPartialHomeomorph M State, c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M ∧ y ∈ c.source ∧
    ∃ η : State →L[ℝ] ℝ, η ≠ 0 ∧ ∀ (Z : ℝ → Fin n → SobolevData) (f : ℝ → State),
      Z 0 = p → f 0 = c y → DifferentiableAt ℝ Z 0 → DifferentiableAt ℝ f 0 →
      (∀ᶠ t in 𝓝 0, f t ∈ c.target ∧ SobolevJoins e (Z t) x (c.symm (f t))) →
      η (deriv f 0) = 0

def FrameCodes (e : Fin n → Frame M m) (p : Fin n → SobolevData) (u : Fin n → Control m) : Prop :=
  ∀ i, (e i).Solves (u i) (p i).1 (ambientPath (p i))

theorem SobolevJoins.control {e : Fin n → Frame M m} {p : Fin n → SobolevData} {u : Fin n → Control m}
    {x y : M} (path : SobolevJoins e p x y) (codes : FrameCodes e p u) : Joins e u x y := by
  obtain ⟨q,first,last,edge⟩ := path
  refine ⟨q,first,last,fun i => ?_⟩
  obtain ⟨a,b,eq,stop,_⟩ := edge i
  exact (segment_iff_frame_path _ _ _ _).mpr ⟨a,b,ambientPath _,eq ▸ codes i,stop⟩

theorem SobolevJoins.has_codes {e : Fin n → Frame M m} {p : Fin n → SobolevData} {x y : M}
    (path : SobolevJoins e p x y) : ∃ u, FrameCodes e p u := by
  obtain ⟨q,_,_,edge⟩ := path
  choose u sol using fun i => ((horizontal_iff_unique_control (e i) (p i)).mp (edge i).2.2.2.2).exists
  exact ⟨u,sol⟩

theorem Joins.sobolev {e : Fin n → Frame M m} {u : Fin n → Control m} {x y : M}
    (path : Joins e u x y) : ∃ p, SobolevJoins e p x y ∧ FrameCodes e p u := by
  obtain ⟨q,first,last,seg⟩ := path
  have edge (i) : ∃ p : SobolevData, SobolevEdge (e i) p (q i.castSucc) (q i.succ) ∧
      (e i).Solves (u i) p.1 (ambientPath p) := by
    obtain ⟨a,b,w,sol,endW⟩ := (segment_iff_frame_path _ _ _ _).mp (seg i)
    obtain ⟨v,eq,uniq⟩ := solve_to_ambient (e i) _ _ _ sol
    let p : SobolevData := ((e i).chart (q i.castSucc),v)
    have hz : (e i).Solves (u i) p.1 (ambientPath p) := eq.symm ▸ sol
    have horizontal : (e i).HorizontalSobolev p := by
      refine ⟨hz.1,?_⟩
      let A : C(Time,Fiber m →L[ℝ] State) := ⟨fun t => (e i).coefficient (w t),
        (e i).coefficient_smooth.continuousOn.comp_continuous w.continuous sol.1⟩
      have prim := ((e i).solve_primitive sol).replace_ae (multiplyVelocity_ae A (u i)).symm
      have atp := ambient_primitive p
      change TimePrimitive (ambientPath ((e i).chart (q i.castSucc),v)) _ _ at atp
      rw [eq] at atp
      have id : multiplyVelocity (Fiber m) State A (u i) = v := prim.velocity_unique atp
      filter_upwards [multiplyVelocity_ae A (u i)] with r hr
      change v r ∈ LinearMap.range ((e i).coefficient (ambientPath ((e i).chart (q i.castSucc),v) (clamp r))).toLinearMap
      rw [eq]; exact ⟨u i r,(hr.symm.trans (congrArg (fun d : Control 5 => d r) id))⟩
    refine ⟨p,⟨a,b,rfl,?_,horizontal⟩,hz⟩
    exact (congrArg (fun z : C(Time,State) => z (clamp 1)) eq).trans endW
  choose p h hp using edge
  exact ⟨p,⟨q,first,last,h⟩,hp⟩

theorem FrameCodes.length_eq {e : Fin n → Frame M m} {p : Fin n → SobolevData} {u : Fin n → Control m}
    (codes : FrameCodes e p u) : sobolevLength e p = length u := by
  apply Finset.sum_congr rfl
  intro i _
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le zero_le_one,Measure.restrict_congr_set Ioc_ae_eq_Icc]
  filter_upwards [(e i).raw_speed_of_control (codes i)] with r h using congrArg Real.sqrt h

#print axioms SobolevJoins.control
#print axioms SobolevJoins.has_codes
#print axioms Joins.sobolev
#print axioms FrameCodes.length_eq
end MinimizingSard.Five
