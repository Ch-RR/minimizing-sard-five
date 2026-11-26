import SobolevTimeCoordinates
import GlobalCurveSard

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
open Volterra
variable {n : ℕ}

@[simp] theorem TimePartition.atTime_zero (P : TimePartition n) (i : Fin n) :
    P.atTime i (clamp 0) = P.unitCut i.castSucc := by apply Subtype.ext; simp [TimePartition.atTime,TimePartition.unitCut,TimePartition.left,clamp]
@[simp] theorem TimePartition.atTime_one (P : TimePartition n) (i : Fin n) :
    P.atTime i (clamp 1) = P.unitCut i.succ := by apply Subtype.ext; simp [TimePartition.atTime,TimePartition.unitCut,clamp]

theorem TimePartition.glueAmbient (P : TimePartition (n+1)) :
    ∃ A : (Fin (n+1) → SobolevData) →L[ℝ] SobolevData, ∀ (p : Fin (n+1) → SobolevData) (f : Time → State),
      (∀ i s, ambientPath (p i) s = f (P.atTime i s)) → ∀ t, ambientPath (A p) t = f t := by
  obtain ⟨R,r,_⟩ := P.coordinates 5
  let fst := (ContinuousLinearMap.fst ℝ State (Control 5)).comp (ContinuousLinearMap.proj (φ := fun _ : Fin (n+1) => SobolevData) 0)
  let snd := ContinuousLinearMap.pi (fun i : Fin (n+1) => (ContinuousLinearMap.snd ℝ State (Control 5)).comp (ContinuousLinearMap.proj i))
  let A := fst.prod (R.symm.toContinuousLinearMap.comp snd)
  refine ⟨A,?_⟩
  intro p f loc
  let U := R.symm (fun i => (p i).2)
  let w := ambientPath ((p 0).1,U)
  have ru : R U = fun i => (p i).2 := R.apply_symm_apply _
  have restrict (i) (s : Time) : ambientPath (w (P.unitCut i.castSucc),(p i).2) s = w (P.atTime i s) := by
    have rep := r U i
    rw [ru] at rep
    have q := ambient_restrict (a := P.left i) (d := P.duration i) (P.cut_mem i.castSucc).1 (P.duration_pos i) ((P.end_eq i).symm ▸ (P.cut_mem i.succ).2)
      U (p i).2 rep (p 0).1 s
    have start : clamp (P.left i) = P.unitCut i.castSucc := projIcc_of_mem _ (P.cut_mem _)
    have endT : clamp (P.left i+P.duration i*s) = P.atTime i s := projIcc_of_mem _ (P.atTime i s).property
    simpa only [w,start,endT] using q
  have first (i) : (p i).1 = f (P.unitCut i.castSucc) := by simpa only [P.atTime_zero,(ambient_primitive (p i)).at_zero] using loc i (clamp 0)
  have node (j : Fin ((n+1)+1)) : w (P.unitCut j) = f (P.unitCut j) := by
    induction j using Fin.induction with
    | zero =>
      have z : P.unitCut 0 = clamp 0 := by apply Subtype.ext; simp [TimePartition.unitCut,P.first,clamp]
      exact (congrArg w z).trans ((ambient_primitive ((p 0).1,U)).at_zero.trans (first 0))
    | succ i ih =>
      have h := restrict i (clamp 1)
      rw [P.atTime_one,ih,← first i] at h
      exact h.symm.trans (by simpa only [P.atTime_one] using loc i (clamp 1))
  intro t
  obtain ⟨i,hi⟩ : ∃ i, (t:ℝ) ∈ Icc (P.left i) (P.cut i.succ) := by
    by_cases z : (t:ℝ) = 0
    · exact ⟨0,by rw [z]; exact ⟨P.first.le,(P.cut_mem (0:Fin (n+1)).succ).1⟩⟩
    · obtain ⟨i,h⟩ := mem_iUnion.mp (P.covers ⟨lt_of_le_of_ne t.2.1 (Ne.symm z),t.2.2⟩)
      exact ⟨i,h.1.le,h.2⟩
  have patch := restrict i (P.localClock i t)
  rw [node,← first i,P.atTime_clock i t hi] at patch
  exact patch.symm.trans (by simpa only [P.atTime_clock i t hi] using loc i (P.localClock i t))

variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] {m : ℕ}

/-- A global smooth observation of a differentiable horizontal path
family varies differentiably in the full ambient Sobolev norm. -/
theorem HorizontalVariation.observe {Γ : Geometry M m} {x : M} {F : ℝ → C(Time,M)}
    (family : HorizontalVariation Γ x F) (H : M → State)
    (smooth : ∀ e ∈ Γ.frames, ContDiffOn ℝ ∞ (H ∘ (e : Frame M m).chart.symm) e.chart.target) :
    ∃ z : ℝ → SobolevData, DifferentiableAt ℝ z 0 ∧ ∀ᶠ r in 𝓝 0, ∀ t, ambientPath (z r) t = H (F r t) := by
  obtain ⟨n,P,e,Z,he,dz,near⟩ := family
  have inside (i) : ∀ s, ambientPath (Z 0 i) s ∈ (e i).chart.target := by
    obtain ⟨_,_,_,edge⟩ := near.self_of_nhds.2.1
    exact (edge i).2.2.2.2.1
  choose T dT term using fun i => sobolev_coordinate_germ (e i).chart.target (e i).chart.open_target
    (H ∘ (e i).chart.symm) (smooth _ (he i)) (Z 0 i) (inside i) 1
  obtain ⟨A,glue⟩ := P.glueAmbient
  let z (r : ℝ) := A (fun i => T i (Z r i))
  have ds (i) : DifferentiableAt ℝ (fun r => Z r i) 0 := ((ContinuousLinearMap.proj i : (Fin (n+1) → SobolevData) →L[ℝ] SobolevData).differentiableAt).comp 0 dz
  refine ⟨z,A.differentiableAt.comp 0 (differentiableAt_pi.mpr (fun i => ((dT i).differentiableAt (by decide)).comp 0 (ds i))),?_⟩
  have each (i) := (ds i).continuousAt.tendsto (term i)
  filter_upwards [near,Filter.eventually_all.mpr each] with r hr tt
  apply glue
  intro i s
  have ref := hr.2.2 i _ (P.atTime_mem i s)
  rw [P.clock_atTime] at ref
  exact ((tt i).2.1 s).2.trans (congrArg H ref.symm)

#print axioms TimePartition.glueAmbient
#print axioms HorizontalVariation.observe
end MinimizingSard.Five
