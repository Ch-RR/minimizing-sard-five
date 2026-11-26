import NormalTerminal

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] {m : ℕ}

def packPhase (a : OpenPartialHomeomorph M State) (z : Phase) : CotPoint M :=
  packCov a (a.symm z.1) z.2

/-- A local family varies the initial base and covector, realizes the original
controls, and reaches the same intrinsic cotangent endpoint at the fixed duration. -/
def NormalFamily {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] (Γ : Geometry M m)
    (a b : OpenPartialHomeomorph M State) (rel : U → M → M → Prop) (L : ℝ) (w : U)
    (z₀ z₁ : Phase) : Prop :=
  ∃ (F : Phase → Phase) (V : Phase → U), F z₀ = z₁ ∧ V z₀ = w ∧
    DifferentiableAt ℝ F z₀ ∧ DifferentiableAt ℝ V z₀ ∧
    ∀ᶠ s in 𝓝 z₀, s.1 ∈ a.target ∧ (F s).1 ∈ b.target ∧
      rel (V s) (a.symm s.1) (b.symm (F s).1) ∧
      TraceReach Γ L (packPhase a s) (packPhase b (F s))

/-- Differentiate all original control blocks of a finite chart sequence.
The neighboring cotangent endpoints match throughout the same neighborhood. -/
theorem NormalFamily.chain (Γ : Geometry M m) {n : ℕ} (e : Fin n → Frame M m)
    (a : Fin (n+1) → OpenPartialHomeomorph M State) (d : Fin n → ℝ) (pos : ∀ i, 0 ≤ d i)
    (w : Fin n → Control m) (z : Fin (n+1) → Phase) (inside : ∀ j, (z j).1 ∈ (a j).target)
    (pieces : ∀ i, NormalFamily Γ (a i.castSucc) (a i.succ) (Segment (e i)) (d i) (w i)
      (z i.castSucc) (z i.succ)) :
    NormalFamily Γ (a 0) (a (Fin.last n)) (Joins e) (∑ i, d i) w (z 0) (z (Fin.last n)) := by
  choose F V arrive base df dv near using pieces
  let Z : Fin (n+1) → Phase → Phase := Fin.induction (motive := fun _ => Phase → Phase) id
    (fun i prev => F i ∘ prev)
  have roots (j : Fin (n+1)) : Z j (z 0) = z j := by
    induction j using Fin.induction with
    | zero => rfl
    | succ i h => exact (congrArg (F i) h).trans (arrive i)
  have smooth (j : Fin (n+1)) : DifferentiableAt ℝ (Z j) (z 0) := by
    induction j using Fin.induction with
    | zero => exact differentiableAt_id
    | succ i h =>
      change DifferentiableAt ℝ (F i ∘ Z i.castSucc) (z 0)
      exact ((roots i.castSucc).symm ▸ df i).comp (z 0) h
  let B (s : Phase) (i : Fin n) := V i (Z i.castSucc s)
  have dB : DifferentiableAt ℝ B (z 0) := differentiableAt_pi.mpr fun i =>
    ((roots i.castSucc).symm ▸ dv i).comp (z 0) (smooth i.castSucc)
  have edges (i : Fin n) : ∀ᶠ s in 𝓝 (z 0),
      (Z i.castSucc s).1 ∈ (a i.castSucc).target ∧ (Z i.succ s).1 ∈ (a i.succ).target ∧
      Segment (e i) (B s i) ((a i.castSucc).symm (Z i.castSucc s).1) ((a i.succ).symm (Z i.succ s).1) ∧
      TraceReach Γ (d i) (packPhase (a i.castSucc) (Z i.castSucc s)) (packPhase (a i.succ) (Z i.succ s)) := by
    have push := (smooth i.castSucc).continuousAt.tendsto
    rw [roots] at push
    exact push (near i)
  have mem (j : Fin (n+1)) : ∀ᶠ s in 𝓝 (z 0), (Z j s).1 ∈ (a j).target :=
    (smooth j).continuousAt.fst ((a j).open_target.mem_nhds (show (Z j (z 0)).1 ∈ (a j).target by rw [roots]; exact inside j))
  refine ⟨Z (Fin.last n),B,roots _,funext (fun i => (congrArg (V i) (roots i.castSucc)).trans (base i)),smooth _,dB,?_⟩
  filter_upwards [eventually_all.mpr edges,mem 0,mem (Fin.last n)] with s walk h0 hn
  exact ⟨h0,hn,⟨fun j => (a j).symm (Z j s).1,rfl,rfl,fun i => (walk i).2.2.1⟩,
    TraceReach.chain Γ d pos (fun j => packPhase (a j) (Z j s)) (fun i => (walk i).2.2.2)⟩

variable [IsManifold 𝓘(ℝ,State) ∞ M]

theorem packPhase_change (a b : OpenPartialHomeomorph M State)
    (ha : a ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (hb : b ∈ maximalAtlas 𝓘(ℝ,State) ∞ M)
    (s : Phase) (sa : s.1 ∈ a.target) (sb : a.symm s.1 ∈ b.source) :
    packPhase b (phaseChange a b s) = packPhase a s := by
  let x := a.symm s.1
  have ax : x ∈ a.source := a.map_target sa
  have eq := phaseView_pack a b ha hb x ax sb s.2
  have view : phaseView b (packPhase a s) = phaseChange a b s := eq
  rw [← view]
  change packCov b (b.symm (b x)) _ = _
  rw [b.left_inv sb]
  exact pack_phaseView b hb (packPhase a s) sb

#print axioms NormalFamily.chain
#print axioms packPhase_change

omit [ChartedSpace State M] [IsManifold 𝓘(ℝ,State) ∞ M] in
theorem phaseChange_base (a b : OpenPartialHomeomorph M State) (x : M) (ax : x ∈ a.source) (p : Covector) :
    phaseChange a b (a x,p) = (b x,p.comp (chartJac b a x)) := by
  simp only [phaseChange,a.left_inv ax,chartJac]

theorem phaseChange_back (a b : OpenPartialHomeomorph M State)
    (ha : a ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (hb : b ∈ maximalAtlas 𝓘(ℝ,State) ∞ M)
    (y : M) (ay : y ∈ a.source) (by' : y ∈ b.source) (p : Covector) :
    phaseChange b a (b y,p.comp (chartJac b a y)) = (a y,p) := by
  rw [phaseChange_base b a y by']
  refine Prod.ext (by rfl) ?_
  apply ContinuousLinearMap.ext
  intro h
  exact congrArg p (DFunLike.congr_fun (transition_left a b ha hb y ay by') h)

/-- Change the two endpoint charts of a family without changing its controls
or duration. This includes the cotangent transformation in both variables. -/
theorem NormalFamily.rechart {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Γ : Geometry M m) (a b c : OpenPartialHomeomorph M State)
    (ha : a ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (hb : b ∈ maximalAtlas 𝓘(ℝ,State) ∞ M)
    (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (x y : M)
    (ax : x ∈ a.source) (cx : x ∈ c.source) (by' : y ∈ b.source) (cy : y ∈ c.source)
    (p q : Covector) (rel : V → M → M → Prop) (L : ℝ) (w : V)
    (family : NormalFamily Γ c c rel L w (c x,p.comp (chartJac c a x)) (c y,q.comp (chartJac c b y))) :
    NormalFamily Γ a b rel L w (a x,p) (b y,q) := by
  obtain ⟨F,A,out,orig,df,da,near⟩ := family
  let I := phaseChange a c
  let O := phaseChange c b
  let ξ : Phase := (a x,p)
  have ip : I ξ = (c x,p.comp (chartJac c a x)) := phaseChange_base a c x ax p
  have op : O (F (I ξ)) = (b y,q) := by
    rw [ip,out]
    exact phaseChange_back b c hb hc y by' cy q
  rw [← ip] at df da near orig out
  have di : DifferentiableAt ℝ I ξ := (phaseChange_smooth a c ha hc x ax cx p).differentiableAt (by decide)
  have do' : DifferentiableAt ℝ O (F (I ξ)) := by
    rw [out]
    exact (phaseChange_smooth c b hc hb y cy by' _).differentiableAt (by decide)
  let Z := F ∘ I
  have dz : DifferentiableAt ℝ Z ξ := df.comp ξ di
  have cb : ContinuousAt (fun s : Phase => a.symm s.1) ξ :=
    (a.symm.continuousAt (a.map_source ax)).comp (x := ξ) continuousAt_fst
  have cc : ContinuousAt (fun s => c.symm (Z s).1) ξ := by
    have inside : (Z ξ).1 ∈ c.target := (show Z ξ = _ from out).symm ▸ c.map_source cy
    exact (c.symm.continuousAt inside).comp (x := ξ) dz.continuousAt.fst
  have outBase : c.symm (Z ξ).1 = y := by change c.symm (F (I ξ)).1 = y; rw [out]; exact c.left_inv cy
  have inA : ∀ᶠ s in 𝓝 ξ, s.1 ∈ a.target := continuousAt_fst (a.open_target.mem_nhds (a.map_source ax))
  have inC : ∀ᶠ s : Phase in 𝓝 ξ, a.symm s.1 ∈ c.source := cb (c.open_source.mem_nhds (show a.symm (a x) ∈ c.source by rwa [a.left_inv ax]))
  have inB : ∀ᶠ s : Phase in 𝓝 ξ, c.symm (Z s).1 ∈ b.source := cc (b.open_source.mem_nhds (show c.symm (Z ξ).1 ∈ b.source by rwa [outBase]))
  refine ⟨O ∘ Z,A ∘ I,op,orig,do'.comp ξ dz,da.comp ξ di,?_⟩
  filter_upwards [inA,inC,inB,di.continuousAt.tendsto near] with s hs cs bs h
  have pin := packPhase_change a c ha hc s hs cs
  have pout := packPhase_change c b hc hb (Z s) h.2.1 bs
  have xeq : c.symm (I s).1 = a.symm s.1 := c.left_inv cs
  have yeq : b.symm (O (Z s)).1 = c.symm (Z s).1 := b.left_inv bs
  have rc := h.2.2.1
  change rel (A (I s)) (c.symm (I s).1) (c.symm (Z s).1) at rc
  rw [xeq,← yeq] at rc
  refine ⟨hs,b.map_source bs,rc,?_⟩
  change TraceReach Γ L (packPhase a s) (packPhase b (O (Z s)))
  rw [← pin,pout]
  exact h.2.2.2

#print axioms NormalFamily.rechart

end MinimizingSard.Five
