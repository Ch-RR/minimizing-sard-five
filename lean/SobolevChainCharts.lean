import SobolevJoins

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
open Volterra
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] [IsManifold 𝓘(ℝ,State) ∞ M] {m n : ℕ}

set_option maxHeartbeats 1400000 in
/-- In every fixed sequence of frames the whole horizontal nodal subset
admits smooth forward and inverse control coordinates, in the ambient
product W¹,² norm. Common nodes vary and the initial source stays fixed. -/
theorem sobolev_chain_chart (e : Fin n → Frame M m) (p : Fin n → SobolevData) (u : Fin n → Control m)
    (x y : M) (path : SobolevJoins e p x y) (codes : FrameCodes e p u)
    (c : OpenPartialHomeomorph M State) (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (cy : y ∈ c.source)
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ (F : (Fin n → Control m) → Fin n → SobolevData) (R : (Fin n → SobolevData) → Fin n → Control m)
      (G : (Fin n → Control m) → State), F u = p ∧ R p = u ∧ G u = c y ∧
      ContDiffAt ℝ k F u ∧ ContDiffAt ℝ k R p ∧ ContDiffAt ℝ k G u ∧
      (∀ᶠ v in 𝓝 u, G v ∈ c.target ∧
        (∀ z, Joins e v x z ↔ z = c.symm (G v)) ∧ SobolevJoins e (F v) x (c.symm (G v)) ∧ R (F v) = v) ∧
      ∀ᶠ z in 𝓝 p, ∀ b, SobolevJoins e z x b → FrameCodes e z (R z) ∧ F (R z) = z := by
  classical
  obtain ⟨q,rfl,rfl,edge⟩ := path
  have seg (i) : Segment (e i) (u i) (q i.castSucc) (q i.succ) := by
    obtain ⟨a,b,eq,stop,_⟩ := edge i
    exact (segment_iff_frame_path _ _ _ _).mpr ⟨a,b,ambientPath _,eq ▸ codes i,stop⟩
  let b (j : Fin (n+1)) := if j = Fin.last n then c else chartAt State (q j)
  have last : b (Fin.last n) = c := by simp [b]
  have atlas (j) : b j ∈ maximalAtlas 𝓘(ℝ,State) ∞ M := by unfold b; split <;> first | exact hc | exact chart_mem_maximalAtlas _
  have inside (j) : q j ∈ (b j).source := by unfold b; split <;> first | next h => exact h ▸ cy | exact mem_chart_source _ _
  choose H hH graph using fun i => segment_in_charts_of_graph (e i) (u i) _ _ (seg i) k
    (frame_segment_graph _ _ _ _ (seg i) k hk) _ _ (atlas i.castSucc) (atlas i.succ) (inside _) (inside _)
  obtain ⟨nodes,_,whole⟩ := prescribed_composite_graph e b u q inside seg H hH graph
  let states (j : Fin (n+1)) (v : Fin n → Control m) := chainNode H j (b 0 (q 0),v)
  have center (j) : states j u = b j (q j) := nodes j
  have trained (j : Fin (n+1)) : ContDiffAt ℝ k (states j) u := by
    induction j using Fin.induction with
    | zero => exact contDiffAt_const
    | succ i ih =>
      have atI : ContDiffAt ℝ k (H i) (states i.castSucc u,u i) := (center i.castSucc).symm ▸ hH i
      change ContDiffAt ℝ k ((H i) ∘ fun v => (states i.castSucc v,v i)) u
      exact atI.comp u (ih.prodMk (ContinuousLinearMap.proj i : (Fin n → Control m) →L[ℝ] Control m).contDiff.contDiffAt)
  let target (j : Fin (n+1)) (v : Fin n → Control m) := (b j).symm (states j v)
  have root (j) : target j u = q j := by simp [target,center,(b j).left_inv (inside j)]
  let input (i : Fin n) (v : Fin n → Control m) := ((e i).chart (target i.castSucc v),v i)
  have input₀ (i) : input i u = ((p i).1,u i) := by simp only [input,root,(edge i).2.2.1]
  have inputC (i) : ContDiffAt ℝ k (input i) u := by
    have ct := transition_smooth (k := k) (b i.castSucc) (e i).chart (atlas _) (e i).compatible _ (inside _) (seg i).1
    have atI := (center i.castSucc).symm ▸ ct
    exact ((show ContDiffAt ℝ k ((e i).chart ∘ (b i.castSucc).symm) (states i.castSucc u) from atI).comp u (trained _)).prodMk
      (ContinuousLinearMap.proj i : (Fin n → Control m) →L[ℝ] Control m).contDiff.contDiffAt
  have charts (i : Fin n) := sobolev_frame_chart (e i) (p i) (edge i).2.2.2.2 k hk
  choose v F R sol cf cr dF dR forward reverse using charts
  have us (i) : v i = u i := ((horizontal_iff_unique_control _ _).mp (edge i).2.2.2.2).unique (sol i) (codes i)
  have eqv : v = u := funext us
  subst v
  let A (v : Fin n → Control m) (i : Fin n) := F i (input i v)
  let B (z : Fin n → SobolevData) (i : Fin n) := (R i (z i)).2
  have a₀ : A u = p := funext fun i => (congrArg (F i) (input₀ i)).trans (cf i)
  have b₀ : B p = u := funext fun i => congrArg Prod.snd (cr i)
  have dA : ContDiffAt ℝ k A u := contDiffAt_pi.mpr fun i =>
    ((input₀ i).symm ▸ dF i).comp u (inputC i)
  have dB : ContDiffAt ℝ k B p := contDiffAt_pi.mpr fun i =>
    ((dR i).comp p (ContinuousLinearMap.proj i : (Fin n → SobolevData) →L[ℝ] SobolevData).contDiff.contDiffAt).snd
  have links (i : Fin n) : ∀ᶠ v in 𝓝 u, Segment (e i) (v i) (target i.castSucc v) (target i.succ v) := by
    have t : Tendsto (fun v : Fin n → Control m => (states i.castSucc v,v i)) (𝓝 u) (𝓝 (b i.castSucc (q i.castSucc),u i)) :=
      ((center i.castSucc ▸ (trained i.castSucc).continuousAt.tendsto).prodMk_nhds (continuous_apply i).continuousAt.tendsto)
    filter_upwards [t (graph i)] with v h
    exact (h.2.2 _).mpr rfl
  have forw (i : Fin n) : ∀ᶠ v in 𝓝 u, SobolevEdge (e i) (A v i) (target i.castSucc v) (target i.succ v) ∧
      (B (A v)) i = v i ∧ (e i).Solves (v i) (A v i).1 (ambientPath (A v i)) := by
    filter_upwards [(input₀ i ▸ (inputC i).continuousAt.tendsto) (forward i),links i] with v f s
    obtain ⟨a,b,w,ws,wy⟩ := (segment_iff_frame_path _ _ _ _).mp s
    have solution : (e i).Solves (v i) ((e i).chart (target i.castSucc v)) (ambientPath (A v i)) := f.2.1
    have same := (e i).solves_unique _ _ _ _ solution ws
    exact ⟨⟨a,b,f.1,(congrArg (fun f : C(Time,State) => f (clamp 1)) same).trans wy,f.2.2.1⟩,
      congrArg Prod.snd f.2.2.2,f.1.symm ▸ solution⟩
  let G := states (Fin.last n)
  have start (v) : target 0 v = q 0 := (b 0).left_inv (inside 0)
  have endG (v) : target (Fin.last n) v = c.symm (G v) := by simp [target,G,last]
  have whole' : ∀ᶠ v in 𝓝 u, G v ∈ c.target ∧ ∀ z, Joins e v (q 0) z ↔ z = c.symm (G v) := by
    let I (v : Fin n → Control m) := (b 0 (q 0),v)
    have t : Tendsto I (𝓝 u) (𝓝 (b 0 (q 0),u)) := tendsto_const_nhds.prodMk_nhds tendsto_id
    filter_upwards [t whole] with v h
    simpa only [← last,I,G,states,(b 0).left_inv (inside 0)] using h.2
  have fw : ∀ᶠ v in 𝓝 u, G v ∈ c.target ∧ (∀ z, Joins e v (q 0) z ↔ z = c.symm (G v)) ∧
      SobolevJoins e (A v) (q 0) (c.symm (G v)) ∧ B (A v) = v ∧ FrameCodes e (A v) v := by
    filter_upwards [Filter.eventually_all.mpr forw,whole'] with v all h
    exact ⟨h.1,h.2,⟨fun j => target j v,start v,endG v,fun i => (all i).1⟩,
      funext fun i => (all i).2.1,fun i => (all i).2.2⟩
  refine ⟨A,B,G,a₀,b₀,(center _).trans (by rw [last]),dA,dB,trained _,fw.mono (fun _ h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩),?_⟩
  have near (i : Fin n) : ∀ᶠ z : Fin n → SobolevData in 𝓝 p, (e i).HorizontalSobolev (z i) →
      (e i).Solves (B z i) (z i).1 (ambientPath (z i)) := by
    filter_upwards [(continuous_apply i).continuousAt.tendsto (reverse i)] with z h using fun hz => (h hz).2.1
  filter_upwards [Filter.eventually_all.mpr near,(b₀ ▸ dB.continuousAt.tendsto) fw] with z all lifted
  intro t path
  obtain ⟨q',first,_,edges⟩ := path
  have coded : FrameCodes e z (B z) := fun i => all i (edges i).2.2.2.2
  refine ⟨coded,?_⟩
  obtain ⟨r,rf,_,rE⟩ := lifted.2.2.1
  have same (j : Fin (n+1)) : r j = q' j := by
    induction j using Fin.induction with
    | zero => exact rf.trans first.symm
    | succ i ih =>
      obtain ⟨ra,rb,rs,re,_⟩ := rE i
      obtain ⟨qa,qb,qs,qe,_⟩ := edges i
      have a := lifted.2.2.2.2 i
      have b := coded i
      rw [rs,ih,← qs] at a
      have ident := (e i).solves_unique _ _ _ _ a b
      apply (e i).chart.injOn rb qb
      exact re.symm.trans ((congrArg (fun f : C(Time,State) => f (clamp 1)) ident).trans qe)
  funext i
  have eq₁ := (rE i).2.2.1.trans ((congrArg (e i).chart (same i.castSucc)).trans (edges i).2.2.1.symm)
  have a := lifted.2.2.2.2 i
  rw [eq₁] at a
  have ident := (e i).solves_unique _ _ _ _ a (coded i)
  have h := ambient_primitive (A (B z) i)
  rw [ident,eq₁] at h
  exact Prod.ext eq₁ (h.velocity_unique (ambient_primitive (z i)))

#print axioms sobolev_chain_chart
end MinimizingSard.Five
