import TraceAssembly
import NormalCriticalValues

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
open Volterra
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] {m : ℕ}

def scaleCot (a : ℝ) (x : CotPoint M) : CotPoint M := (x.1,a • x.2)

def scalePhase (a : ℝ) : Phase →L[ℝ] Phase :=
  (ContinuousLinearMap.id ℝ State).prodMap (a • ContinuousLinearMap.id ℝ Covector)

theorem scale_view (c : OpenPartialHomeomorph M State) (a : ℝ) (x : CotPoint M) :
    phaseView c (scaleCot a x) = scalePhase a (phaseView c x) := by
  refine Prod.ext (by rfl) ?_
  exact ContinuousLinearMap.ext fun _ => rfl

/-- Homogeneity changes a positive duration into time one by scaling the
initial covector. This fixes the number of parameters independently of length. -/
theorem TraceReach.unit_time (Γ : Geometry M m) {L : ℝ} (pos : 0 < L) {x y : CotPoint M}
    (h : TraceReach Γ L x y) : TraceReach Γ 1 (scaleCot L x) (scaleCot L y) := by
  obtain ⟨f,tr,start,stop⟩ := h
  let τ (s : ℝ) := L*s
  let g (s : ℝ) := scaleCot L (f (τ s))
  have len : MapsTo τ (Icc 0 1) (Icc 0 L) := fun s hs =>
    ⟨mul_nonneg pos.le hs.1,mul_le_of_le_one_right pos.le hs.2⟩
  have ct : Continuous τ := continuous_const.mul continuous_id
  have view (e : Frame M m) : phaseView e.chart ∘ g = scalePhase L ∘ (phaseView e.chart ∘ f) ∘ τ :=
    funext fun t => scale_view e.chart L _
  refine ⟨g,⟨tr.base.comp ct.continuousOn len,?_,?_⟩,by simp [g,τ,start],by simp [g,τ,stop]⟩
  · intro e he s hs hx
    rw [view]
    exact (scalePhase L).continuous.continuousAt.comp_continuousWithinAt
      ((tr.coord e he _ (len hs) hx).comp (f := τ) ct.continuousAt.continuousWithinAt len)
  · intro e he s hs hx
    have st : τ s ∈ Ico 0 L := ⟨mul_nonneg pos.le hs.1,by simpa [τ] using mul_lt_mul_of_pos_left hs.2 pos⟩
    have dt : HasDerivAt τ L s := by simpa only [mul_one] using (hasDerivAt_id s).const_mul L
    have d := (tr.ode e he _ st hx).scomp s dt.hasDerivWithinAt
      (show MapsTo τ (Ici s) (Ici (τ s)) from fun _ h => mul_le_mul_of_nonneg_left h pos.le)
    have dv := (scalePhase L).hasFDerivAt.comp_hasDerivWithinAt s d
    rw [view]
    change HasDerivWithinAt _ (hamiltonianField e.X (phaseView e.chart (scaleCot L (f (τ s))))) _ _
    rw [scale_view]
    convert dv using 1
    let z := phaseView e.chart (f (τ s))
    change hamiltonianField e.X (z.1,L • z.2) = scalePhase L (L • hamiltonianField e.X z)
    rw [hamiltonian_scale]
    exact Prod.ext rfl ((mul_smul L L _))

theorem pieceLength_nonneg {m : ℕ} (u : Control m) : 0 ≤ pieceLength u :=
  integral_nonneg fun _ => norm_nonneg _

variable [IsManifold 𝓘(ℝ,State) ∞ M]

theorem NormalPiece.reaches (Γ : Geometry M m) (e : Frame M m) (he : e ∈ Γ.frames)
    (u : Control m) (z : C(Time,Phase)) (piece : NormalPiece e u z) :
    let pack (v : Phase) := packCov e.chart (e.chart.symm v.1) v.2
    TraceReach Γ (pieceLength u) (pack (z (clamp 0))) (pack (z (clamp 1))) := by
  intro pack
  obtain ⟨f,cf,im,start,stop,ode,_⟩ := piece.arc e u z
  exact ⟨pack ∘ f,HamiltonTrace.of_chart Γ e he _ f cf.continuousOn (fun t _ => im t) ode,
    congrArg pack start,congrArg pack stop⟩

theorem HasNormalLift.reaches (Γ : Geometry M m) (e : Frame M m) (he : e ∈ Γ.frames)
    (u : Control m) (x y : M) (ex : x ∈ e.chart.source) (ey : y ∈ e.chart.source) (ξ η : Covector)
    (lift : HasNormalLift e u x y ξ η) :
    TraceReach Γ (pieceLength u) (packCov e.chart x ξ) (packCov e.chart y η) := by
  obtain ⟨n,R,k,p,Z,k0,kn,p0,pn,cost,_,arcs⟩ := lift
  let q (j : Fin (n+1)) := packCov e.chart (e.chart.symm (k j)) (p j)
  have cell (i : Fin n) : TraceReach Γ (pieceLength (R u i)) (q i.castSucc) (q i.succ) := by
    obtain ⟨left,right,normal⟩ := arcs i
    have reach := normal.reaches Γ e he _ _
    dsimp only at reach
    simpa only [left,right] using reach
  have combined := TraceReach.chain Γ _ (fun i => pieceLength_nonneg (R u i)) q cell
  have len := cost u
  rw [length_pieces] at len
  simpa only [q,k0,kn,p0,pn,e.chart.left_inv ex,e.chart.left_inv ey,len] using combined

#print axioms TraceReach.unit_time
#print axioms NormalPiece.reaches
#print axioms HasNormalLift.reaches
end MinimizingSard.Five
