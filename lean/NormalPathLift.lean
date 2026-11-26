import NormalSegmentLift

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
open Volterra
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M]

/-- The genuine first variation of a chart segment transforms at both its
endpoints. The control coordinates are kept fixed. -/
theorem segment_transition_derivative {m : ℕ} (e : Frame M m) (u : Control m) {x y : M}
    (seg : Segment e u x y) (a b : OpenPartialHomeomorph M State)
    (ha : a ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (hb : b ∈ maximalAtlas 𝓘(ℝ,State) ∞ M)
    (hx : x ∈ a.source) (hy : y ∈ b.source) (F H : State × Control m → State)
    (df : DifferentiableAt ℝ F (e.chart x,u)) (dh : DifferentiableAt ℝ H (a x,u))
    (gf : ∀ᶠ p in 𝓝 (e.chart x,u), p.1 ∈ e.chart.target ∧ F p ∈ e.chart.target ∧
      ∀ v, Segment e p.2 (e.chart.symm p.1) v ↔ v = e.chart.symm (F p))
    (gh : ∀ᶠ p in 𝓝 (a x,u), p.1 ∈ a.target ∧ H p ∈ b.target ∧
      ∀ v, Segment e p.2 (a.symm p.1) v ↔ v = b.symm (H p)) :
    ∀ h v, fderiv ℝ H (a x,u) (fderiv ℝ (a ∘ e.chart.symm) (e.chart x) h,v) =
      fderiv ℝ (b ∘ e.chart.symm) (e.chart y) (fderiv ℝ F (e.chart x,u) (h,v)) := by
  let J := a ∘ e.chart.symm
  let K := b ∘ e.chart.symm
  let p := (e.chart x,u)
  let I (d : State × Control m) := (J d.1,d.2)
  have ip : I p = (a x,u) := by simp [I,p,J,e.chart.left_inv seg.1]
  have fx : F p = e.chart y := by
    have actual := seg
    rw [← e.chart.left_inv seg.1] at actual
    have eq := (gf.self_of_nhds.2.2 y).mp actual
    exact (e.chart.right_inv gf.self_of_nhds.2.1).symm.trans (congrArg e.chart eq.symm)
  have j : DifferentiableAt ℝ J (e.chart x) := (transition_smooth (k := 1) e.chart a e.compatible ha x seg.1 hx).differentiableAt (by decide)
  have k : DifferentiableAt ℝ K (F p) := fx ▸
    (transition_smooth (k := 1) e.chart b e.compatible hb y seg.2.1 hy).differentiableAt (by decide)
  have di := (j.hasFDerivAt.comp p (hasFDerivAt_fst (𝕜 := ℝ) (p := p))).prodMk (hasFDerivAt_snd (𝕜 := ℝ) (p := p))
  have c : ContinuousAt (e.chart.symm ∘ (Prod.fst : State × Control m → State)) p :=
    (e.chart.symm.continuousAt (e.chart.map_source seg.1)).comp (x := p) continuousAt_fst
  have ax : (e.chart.symm ∘ (Prod.fst : State × Control m → State)) p ∈ a.source := by
    simpa [p,e.chart.left_inv seg.1] using hx
  have td : Tendsto I (𝓝 p) (𝓝 (a x,u)) := ip ▸ di.continuousAt.tendsto
  have same : H ∘ I =ᶠ[𝓝 p] K ∘ F := by
    filter_upwards [gf,td gh,c (a.open_source.mem_nhds ax)] with d ge ga inA
    have actual := (ge.2.2 _).mpr rfl
    change e.chart.symm d.1 ∈ a.source at inA
    rw [← a.left_inv inA] at actual
    have eq := (ga.2.2 _).mp actual
    exact (b.right_inv ga.2.1).symm.trans (congrArg b eq.symm)
  have left := ((ip.symm ▸ dh.hasFDerivAt).comp p di).congr_of_eventuallyEq same.symm
  have right := k.hasFDerivAt.comp p df.hasFDerivAt
  intro h v
  have eq := DFunLike.congr_fun (left.unique right) (h,v)
  simpa only [ip,fx,ContinuousLinearMap.comp_apply] using eq

/-- One original segment represented by contiguous clocked Hamiltonian pieces,
with the two boundary covectors specified in its own frame. -/
def HasNormalLift {m : ℕ} (e : Frame M m) (u : Control m) (x y : M) (ξ η : State →L[ℝ] ℝ) : Prop :=
  ∃ n, ∃ R : Control m ≃L[ℝ] (Fin n → Control m), ∃ k : Fin (n+1) → State,
    ∃ p : Fin (n+1) → State →L[ℝ] ℝ, ∃ Z : Fin n → C(Time,Phase),
      k 0 = e.chart x ∧ k (Fin.last n) = e.chart y ∧ p 0 = ξ ∧ p (Fin.last n) = η ∧
      (∀ v, length (R v) = pieceLength v) ∧
      (∀ v a b, Segment e v a b ↔ Joins (fun _ => e) (R v) a b) ∧
      ∀ i, Z i (clamp 0) = (k i.castSucc,p i.castSucc) ∧
        Z i (clamp 1) = (k i.succ,p i.succ) ∧ NormalPiece e (R u i) (Z i)

/-- A single supporting covector produces compatible Hamiltonian lifts on
every chart of the original path, with the cotangent transition at every joint. -/
def SegmentLiftSolver (M : Type*) [TopologicalSpace M] [ChartedSpace State M] (m : ℕ) : Prop :=
  ∀ (e : Frame M m) (u : Control m) (x y : M), Segment e u x y →
    ∀ G : State × Control m → State, DifferentiableAt ℝ G (e.chart x,u) →
    (∀ᶠ b in 𝓝 (e.chart x,u), b.1 ∈ e.chart.target ∧ G b ∈ e.chart.target ∧
      ∀ t, Segment e b.2 (e.chart.symm b.1) t ↔ t = e.chart.symm (G b)) →
    ∀ η : State →L[ℝ] ℝ, (∀ v, pieceLength u + η (fderiv ℝ G (e.chart x,u) (0,v-u)) ≤ pieceLength v) →
      HasNormalLift e u x y (η.comp ((fderiv ℝ G (e.chart x,u)).comp (ContinuousLinearMap.inl ℝ State (Control m)))) η

theorem rank_two_segment_lift_solver : SegmentLiftSolver M 2 := by
  intro e u x y seg G dg gr η sup
  obtain ⟨N,R,k,b,Z,k0,kn,bn,b0,lc,jn,arcs⟩ := normal_segment_lift e u seg G dg gr η sup
  exact ⟨N,R,k,b,Z,k0,kn,ContinuousLinearMap.ext b0,bn,lc,jn,arcs⟩

theorem supported_path_lift_of_segments {m n : ℕ}
    (graphs : ∀ (f : Frame M m) (u : Control m) (a b : M), Segment f u a b → HasSmoothSegmentGraph f 1 (f.chart a,u))
    (solver : SegmentLiftSolver M m) (e : Fin n → Frame M m) (w : Fin n → Control m)
    (q : Fin (n+1) → M) (seg : ∀ i, Segment (e i) (w i) (q i.castSucc) (q i.succ))
    (c : Fin (n+1) → OpenPartialHomeomorph M State) (hq : ∀ j, q j ∈ (c j).source)
    (atlas : ∀ j, c j ∈ maximalAtlas 𝓘(ℝ,State) ∞ M)
    (G : (Fin n → Control m) → State)
    (graph : ∀ᶠ v in 𝓝 w, G v ∈ (c (Fin.last n)).target ∧
      ∀ y, Joins e v (q 0) y ↔ y = (c (Fin.last n)).symm (G v))
    (η : State →L[ℝ] ℝ) (support : ∀ v, length w + η (fderiv ℝ G w (v-w)) ≤ length v) :
    ∃ p : Fin (n+1) → State →L[ℝ] ℝ, p (Fin.last n) = η ∧
      ∀ i, HasNormalLift (e i) (w i) (q i.castSucc) (q i.succ)
        ((p i.castSucc).comp (fderiv ℝ (c i.castSucc ∘ (e i).chart.symm) ((e i).chart (q i.castSucc))))
        ((p i.succ).comp (fderiv ℝ (c i.succ ∘ (e i).chart.symm) ((e i).chart (q i.succ)))) := by
  choose H sm hg using fun i => segment_in_charts_of_graph _ _ _ _ (seg i) 1 (graphs _ _ _ _ (seg i))
    (c i.castSucc) (c i.succ) (atlas _) (atlas _) (hq _) (hq _)
  obtain ⟨p,pn,prev,_,cost⟩ := supported_chain e c w q hq seg H sm hg G graph η support
  refine ⟨p,pn,fun i => ?_⟩
  obtain ⟨F,df,gf⟩ := graphs _ _ _ _ (seg i)
  have trans := segment_transition_derivative _ _ (seg i) _ _ (atlas _) (atlas _) (hq _) (hq _)
    F (H i) (df.differentiableAt (by decide)) ((sm i).differentiableAt (by decide)) gf (hg i)
  let α := (p i.succ).comp (fderiv ℝ (c i.succ ∘ (e i).chart.symm) ((e i).chart (q i.succ)))
  have localCost v : pieceLength (w i) + α (fderiv ℝ F ((e i).chart (q i.castSucc),w i) (0,v-w i)) ≤ pieceLength v := by
    change pieceLength (w i) + p i.succ (fderiv ℝ (c i.succ ∘ (e i).chart.symm) ((e i).chart (q i.succ))
      (fderiv ℝ F ((e i).chart (q i.castSucc),w i) (0,v-w i))) ≤ pieceLength v
    rw [← trans,map_zero]
    exact cost i v
  have lift := solver (e i) (w i) (q i.castSucc) (q i.succ) (seg i) F
    (df.differentiableAt (by decide)) gf α localCost
  have eq : α.comp ((fderiv ℝ F ((e i).chart (q i.castSucc),w i)).comp (ContinuousLinearMap.inl ℝ State (Control m))) =
      (p i.castSucc).comp (fderiv ℝ (c i.castSucc ∘ (e i).chart.symm) ((e i).chart (q i.castSucc))) :=
    ContinuousLinearMap.ext fun h => (congrArg (p i.succ) (trans h 0).symm).trans (prev i _).symm
  rwa [eq] at lift

theorem supported_path_lift {n : ℕ} (e : Fin n → Frame M 2) (w : Fin n → Control 2)
    (q : Fin (n+1) → M) (seg : ∀ i, Segment (e i) (w i) (q i.castSucc) (q i.succ))
    (c : Fin (n+1) → OpenPartialHomeomorph M State) (hq : ∀ j, q j ∈ (c j).source)
    (atlas : ∀ j, c j ∈ maximalAtlas 𝓘(ℝ,State) ∞ M)
    (G : (Fin n → Control 2) → State)
    (graph : ∀ᶠ v in 𝓝 w, G v ∈ (c (Fin.last n)).target ∧
      ∀ y, Joins e v (q 0) y ↔ y = (c (Fin.last n)).symm (G v))
    (η : State →L[ℝ] ℝ) (support : ∀ v, length w + η (fderiv ℝ G w (v-w)) ≤ length v) :
    ∃ p : Fin (n+1) → State →L[ℝ] ℝ, p (Fin.last n) = η ∧
      ∀ i, HasNormalLift (e i) (w i) (q i.castSucc) (q i.succ)
        ((p i.castSucc).comp (fderiv ℝ (c i.castSucc ∘ (e i).chart.symm) ((e i).chart (q i.castSucc))))
        ((p i.succ).comp (fderiv ℝ (c i.succ ∘ (e i).chart.symm) ((e i).chart (q i.succ)))) :=
  supported_path_lift_of_segments (fun f u a b seg => arbitrary_segment_graph f u a b seg 1 (by decide))
    rank_two_segment_lift_solver e w q seg c hq atlas G graph η support

#print axioms segment_transition_derivative
#print axioms supported_path_lift
end MinimizingSard.Five
