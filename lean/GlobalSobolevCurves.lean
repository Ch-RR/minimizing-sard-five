import SobolevMinimizingSard
import Mathlib.Topology.LocallyFinite

noncomputable section
open Set Filter MeasureTheory IsManifold Metric
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
open Volterra
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] {m n : ℕ}

/-- Any continuous path has a finite positive-duration subdivision in
the supplied orthonormal-frame cover. The cover may be uncountable. -/
theorem path_frame_subcover (Γ : Geometry M m) (γ : C(Time,M)) :
    ∃ (k : ℕ) (P : TimePartition k) (e : Fin k → Frame M m), (∀ i, e i ∈ Γ.frames) ∧
      ∀ i, ∀ t : Time, (t:ℝ) ∈ Icc (P.left i) (P.cut i.succ) → γ t ∈ (e i).chart.source := by
  let O (b : Γ.frames) := γ ⁻¹' b.val.chart.source
  have cover : (univ : Set Time) ⊆ ⋃ b, O b := by
    intro t _
    obtain ⟨b,h,hit⟩ := Γ.cover (γ t)
    exact mem_iUnion.mpr ⟨⟨b,h⟩,hit⟩
  obtain ⟨δ,dp,balls⟩ := lebesgue_number_lemma_of_metric isCompact_univ
    (fun b : Γ.frames => b.val.chart.open_source.preimage γ.continuous) cover
  obtain ⟨k,P,mesh⟩ := fine_partition dp
  choose e hit using fun i : Fin k => balls (⟨P.left i,P.cut_mem i.castSucc⟩ : Time) (mem_univ _)
  refine ⟨k,P,fun i => (e i).val,fun i => (e i).property,?_⟩
  intro i t ht
  apply hit i
  change |(t:ℝ)-P.left i| < δ
  rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
  exact (sub_le_sub_right ht.2 _).trans_lt (mesh i)

def TimePartition.unitCut (P : TimePartition n) (i : Fin (n+1)) : Time := ⟨P.cut i,P.cut_mem i⟩
def TimePartition.localClock (P : TimePartition n) (i : Fin n) (t : Time) : Time :=
  clamp (((t:ℝ)-P.left i)/P.duration i)
def RepresentsPath (P : TimePartition n) (e : Fin n → Frame M m) (p : Fin n → SobolevData) (γ : C(Time,M)) : Prop :=
  ∀ i, ∀ t : Time, (t:ℝ) ∈ Icc (P.left i) (P.cut i.succ) →
    γ t = (e i).chart.symm (ambientPath (p i) (P.localClock i t))

private theorem covered (P : TimePartition (n+1)) (t : Time) :
    ∃ i, (t:ℝ) ∈ Icc (P.left i) (P.cut i.succ) := by
  by_cases z : (t:ℝ) = 0
  · refine ⟨0,?_,?_⟩
    · simp [TimePartition.left,P.first,z]
    · exact z ▸ (P.cut_mem (0 : Fin (n+1)).succ).1
  · obtain ⟨i,h⟩ := mem_iUnion.mp (P.covers ⟨lt_of_le_of_ne t.2.1 (Ne.symm z),t.2.2⟩)
    exact ⟨i,h.1.le,h.2⟩

theorem RepresentsPath.unique {P : TimePartition (n+1)} {e : Fin (n+1) → Frame M m}
    {p : Fin (n+1) → SobolevData} {γ ξ : C(Time,M)} (h : RepresentsPath P e p γ) (h' : RepresentsPath P e p ξ) : γ = ξ := by
  ext t
  obtain ⟨i,hi⟩ := covered P t
  exact (h i _ hi).trans (h' i _ hi).symm

/-- Glue all ambient Sobolev pieces into an actual continuous path on
the original unit interval with arbitrary prescribed positive durations. -/
theorem SobolevJoins.realize {e : Fin (n+1) → Frame M m} {p : Fin (n+1) → SobolevData} {x y : M}
    (path : SobolevJoins e p x y) (P : TimePartition (n+1)) :
    ∃ γ : C(Time,M), γ (clamp 0) = x ∧ γ (clamp 1) = y ∧ RepresentsPath P e p γ := by
  obtain ⟨q,first,last,edge⟩ := path
  let O (i : Fin (n+1)) : Set Time := (Subtype.val : Time → ℝ) ⁻¹' Icc (P.left i) (P.cut i.succ)
  let F (i : Fin (n+1)) (t : Time) := (e i).chart.symm (ambientPath (p i) (P.localClock i t))
  have cc (i) : Continuous (P.localClock i) :=
    continuous_projIcc.comp ((continuous_subtype_val.sub continuous_const).div_const _)
  have cf (i) : Continuous (F i) := (e i).chart.continuousOn_symm.comp_continuous
    ((ambientPath (p i)).continuous.comp (cc i)) (fun t => (edge i).2.2.2.2.1 _)
  have atL (i : Fin (n+1)) (t : Time) (eq : (t:ℝ) = P.left i) : F i t = q i.castSucc := by
    have clk : P.localClock i t = clamp 0 := by simp [TimePartition.localClock,eq]
    change (e i).chart.symm (ambientPath (p i) (P.localClock i t)) = _
    rw [clk,(ambient_primitive (p i)).at_zero,(edge i).2.2.1,(e i).chart.left_inv (edge i).1]
  have atR (i : Fin (n+1)) (t : Time) (eq : (t:ℝ) = P.cut i.succ) : F i t = q i.succ := by
    have clk : P.localClock i t = clamp 1 := by
      unfold TimePartition.localClock
      rw [eq,show P.cut i.succ-P.left i = P.duration i from rfl,div_self (P.duration_pos i).ne']
    change (e i).chart.symm (ambientPath (p i) (P.localClock i t)) = _
    rw [clk,(edge i).2.2.2.1,(e i).chart.left_inv (edge i).2.1]
  have order (i j : Fin (n+1)) (lt : i < j) (t : Time) (hi : t ∈ O i) (hj : t ∈ O j) : F i t = F j t := by
    have ij : i.succ ≤ j.castSucc := by change i.val+1 ≤ j.val; exact lt
    have cut := P.increasing.monotone ij
    have eq := le_antisymm cut (hj.1.trans hi.2)
    have node := P.increasing.injective eq
    exact (atR i t (le_antisymm hi.2 (eq.symm ▸ hj.1))).trans ((congrArg q node).trans
      (atL j t (le_antisymm (hi.2.trans cut) hj.1)).symm)
  choose i hi using covered P
  let γ (t : Time) := F (i t) t
  have same (j) (t) (ht : t ∈ O j) : γ t = F j t := by
    rcases lt_trichotomy (i t) j with h | h | h
    · exact order _ _ h t (hi t) ht
    · exact congrArg (fun i => F i t) h
    · exact (order _ _ h t ht (hi t)).symm
  have cg : Continuous γ := (locallyFinite_of_finite O).continuous
    (eq_univ_iff_forall.mpr (fun t => mem_iUnion.mpr ⟨i t,hi t⟩))
    (fun j => isClosed_Icc.preimage continuous_subtype_val) (fun j => (cf j).continuousOn.congr (fun t ht => same j t ht))
  let α : C(Time,M) := ⟨γ,cg⟩
  have z : ((clamp 0:Time):ℝ) = 0 := by simp [clamp]
  have one : ((clamp 1:Time):ℝ) = 1 := by simp [clamp]
  have l : P.left (0 : Fin (n+1)) = 0 := P.first
  let j := Fin.last n
  have r : P.cut j.succ = 1 := by simpa [j,Fin.succ_last] using P.last
  refine ⟨α,?_,?_,same⟩
  · exact (same 0 (clamp 0) ⟨by rw [z,l],by rw [z]; exact (P.cut_mem (0 : Fin (n+1)).succ).1⟩).trans ((atL 0 _ (z.trans l.symm)).trans first)
  · exact (same j (clamp 1) ⟨by rw [one]; exact (P.cut_mem j.castSucc).2,by rw [one,r]⟩).trans
      ((atR j _ (one.trans r.symm)).trans (by simpa [j,Fin.succ_last] using last))

#print axioms path_frame_subcover
#print axioms RepresentsPath.unique
#print axioms SobolevJoins.realize
end MinimizingSard.Five
