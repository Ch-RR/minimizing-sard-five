import SegmentPasting

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace MinimizingSard.Five

variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M]
variable {n m k : ℕ}

/-- The node reached by a finite sequence of local endpoint functions. -/
def chainNode {E U : Type*} {n : ℕ} (H : Fin n → E × U → E) : Fin (n+1) → E × (Fin n → U) → E :=
  Fin.induction (motive := fun _ => E × (Fin n → U) → E) Prod.fst
    (fun i prev b => H i (prev b,b.2 i))

/-- Compose all the local graphs as functions of the initial coordinate
and every block control, using the actual existential node relation. -/
theorem prescribed_composite_graph (e : Fin n → Frame M m) (c : Fin (n+1) → OpenPartialHomeomorph M State)
    (u : Fin n → Control m) (q : Fin (n+1) → M) (atQ : ∀ j, q j ∈ (c j).source)
    (seg : ∀ i, Segment (e i) (u i) (q i.castSucc) (q i.succ))
    (H : Fin n → State × Control m → State)
    (smooth : ∀ i, ContDiffAt ℝ k (H i) ((c i.castSucc) (q i.castSucc),u i))
    (graph : ∀ i, ∀ᶠ b in 𝓝 ((c i.castSucc) (q i.castSucc),u i),
      b.1 ∈ (c i.castSucc).target ∧ H i b ∈ (c i.succ).target ∧
      ∀ y, Segment (e i) b.2 ((c i.castSucc).symm b.1) y ↔ y = (c i.succ).symm (H i b)) :
    (∀ j, chainNode H j ((c 0) (q 0),u) = c j (q j)) ∧
    let F := chainNode H (Fin.last n)
    ContDiffAt ℝ k F ((c 0) (q 0),u) ∧
      ∀ᶠ b in 𝓝 ((c 0) (q 0),u), b.1 ∈ (c 0).target ∧ F b ∈ (c (Fin.last n)).target ∧
        ∀ y, Joins e b.2 ((c 0).symm b.1) y ↔ y = (c (Fin.last n)).symm (F b) := by
  let U := State × (Fin n → Control m)
  let p : U := ((c 0) (q 0),u)
  let Z := chainNode H
  have zero (b : U) : Z 0 b = b.1 := rfl
  have next (i : Fin n) (b : U) : Z i.succ b = H i (Z i.castSucc b,b.2 i) := rfl
  have atNode (j) : Z j p = c j (q j) := by
    induction j using Fin.induction with
    | zero => rfl
    | succ i ih =>
      have gr := (graph i).self_of_nhds
      have actual := seg i
      rw [← (c i.castSucc).left_inv (atQ i.castSucc)] at actual
      have endpt := (gr.2.2 _).mp actual
      rw [next,ih]
      change H i ((c i.castSucc) (q i.castSucc),u i) = c i.succ (q i.succ)
      exact ((c i.succ).right_inv gr.2.1).symm.trans (congrArg (c i.succ) endpt.symm)
  have cs (j) : ContDiffAt ℝ k (Z j) p := by
    induction j using Fin.induction with
    | zero => exact contDiffAt_fst
    | succ i ih =>
      have pair := ih.prodMk (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Control m) i).contDiff.comp contDiff_snd).contDiffAt (x := p))
      have d := smooth i
      rw [← atNode i.castSucc] at d
      change ContDiffAt ℝ k (H i ∘ (fun b : U => (Z i.castSucc b,b.2 i))) p
      exact d.comp p pair
  have edges (i : Fin n) : ∀ᶠ b : U in 𝓝 p, Z i.castSucc b ∈ (c i.castSucc).target ∧
      Z i.succ b ∈ (c i.succ).target ∧ ∀ y, Segment (e i) (b.2 i) ((c i.castSucc).symm (Z i.castSucc b)) y ↔
        y = (c i.succ).symm (Z i.succ b) := by
    have push : Tendsto (fun b : U => (Z i.castSucc b,b.2 i)) (𝓝 p) (𝓝 (c i.castSucc (q i.castSucc),u i)) := by
      rw [← atNode i.castSucc]
      exact ((cs i.castSucc).continuousAt.prodMk ((continuous_apply i).comp continuous_snd).continuousAt).tendsto
    exact push (graph i)
  have member (j) : ∀ᶠ b in 𝓝 p, Z j b ∈ (c j).target :=
    (cs j).continuousAt ((c j).open_target.mem_nhds ((atNode j).symm ▸ (c j).map_source (atQ j)))
  refine ⟨atNode,cs _,?_⟩
  filter_upwards [Filter.eventually_all.mpr edges,member 0,member (Fin.last n)] with b hb h0 hn
  refine ⟨h0,hn,?_⟩
  intro y
  constructor
  · rintro ⟨w,ws,we,walk⟩
    have unique (j) : w j = (c j).symm (Z j b) := by
      induction j using Fin.induction with
      | zero => exact ws
      | succ i ih => exact ((hb i).2.2 _).mp (ih ▸ walk i)
    exact we.symm.trans (unique _)
  · rintro rfl
    exact ⟨fun j => (c j).symm (Z j b),rfl,rfl,fun i => ((hb i).2.2 _).mpr rfl⟩

private theorem compose_graphs (e : Fin n → Frame M m) (c : Fin (n+1) → OpenPartialHomeomorph M State)
    (u : Fin n → Control m) (q : Fin (n+1) → M) (atQ : ∀ j, q j ∈ (c j).source)
    (seg : ∀ i, Segment (e i) (u i) (q i.castSucc) (q i.succ))
    (localG : ∀ i, ∃ H : State × Control m → State,
      ContDiffAt ℝ k H ((c i.castSucc) (q i.castSucc),u i) ∧
      ∀ᶠ b in 𝓝 ((c i.castSucc) (q i.castSucc),u i),
        b.1 ∈ (c i.castSucc).target ∧ H b ∈ (c i.succ).target ∧
        ∀ y, Segment (e i) b.2 ((c i.castSucc).symm b.1) y ↔ y = (c i.succ).symm (H b)) :
    ∃ F : State × (Fin n → Control m) → State,
      ContDiffAt ℝ k F ((c 0) (q 0),u) ∧ F ((c 0) (q 0),u) = (c (Fin.last n)) (q (Fin.last n)) ∧
      ∀ᶠ b in 𝓝 ((c 0) (q 0),u), b.1 ∈ (c 0).target ∧ F b ∈ (c (Fin.last n)).target ∧
        ∀ y, Joins e b.2 ((c 0).symm b.1) y ↔ y = (c (Fin.last n)).symm (F b) := by
  choose H smooth graph using localG
  obtain ⟨nodes,df,germ⟩ := prescribed_composite_graph e c u q atQ seg H smooth graph
  exact ⟨_,df,nodes _,germ⟩

theorem fine_partition {δ : ℝ} (hδ : 0 < δ) :
    ∃ n, ∃ P : TimePartition n, ∀ i, P.duration i < δ := by
  obtain ⟨N,hN⟩ := exists_nat_gt δ⁻¹
  have positive : 0 < (N:ℝ) := (inv_pos.mpr hδ).trans hN
  let P : TimePartition N := {
    cut := fun i => (i.val:ℝ)/N
    first := by simp
    last := by simp [positive.ne']
    increasing := fun i j h => div_lt_div_of_pos_right (by exact_mod_cast h) positive
  }
  refine ⟨N,P,fun i => ?_⟩
  change ((i.val+1:ℕ):ℝ)/N - (i.val:ℝ)/N < δ
  push_cast
  rw [← sub_div,add_sub_cancel_left]
  exact (div_lt_iff₀ positive).mpr (by have := (div_lt_iff₀ hδ).mp (show 1/δ < (N:ℝ) by simpa using hN); linarith)

/-- Finite-order smoothness of the exact original rank-two segment graph
at every reference control admitting a trajectory in this chart. -/
theorem arbitrary_segment_graph (e : Frame M 2) (u : Control 2) (x y : M)
    (seg : Segment e u x y) (k : ℕ) (hk : 1 ≤ (k : WithTop ℕ∞)) :
    HasSmoothSegmentGraph e k (e.chart x,u) := by
  obtain ⟨hx,hy,z,cz,mz,start,stop,hi,eq⟩ := seg
  obtain ⟨δ,hδ,small⟩ := arbitrary_reference_pieces e k hk u z cz mz hi eq
  obtain ⟨N,P,mesh⟩ := fine_partition hδ
  obtain ⟨R,rep,graph⟩ := P.segment_iff_joins e
  let q (j : Fin (N+1)) := e.chart.symm (z (P.cut j))
  have cell (j) : z (P.cut j) ∈ e.chart.target := mz (P.cut_mem j)
  have coord (j) : e.chart (q j) = z (P.cut j) := e.chart.right_inv (cell j)
  have piece (i : Fin N) : HasSmoothSegmentGraph e k (e.chart (q i.castSucc),R u i) ∧
      Segment e (R u i) (q i.castSucc) (q i.succ) := by
    obtain ⟨v,hv,gr,seg⟩ := small (P.left i) (P.duration i) (P.cut_mem _).1 (P.duration_pos i)
      (mesh i) ((P.end_eq i).symm ▸ (P.cut_mem i.succ).2)
    have equal : v = R u i := by
      apply Lp.ext
      filter_upwards [hv,rep u i] with s h1 h2 using h1.trans h2.symm
    rw [equal,P.end_eq] at seg
    exact ⟨by rw [coord,← equal]; exact gr,seg⟩
  obtain ⟨F,cs,_,fg⟩ := compose_graphs (fun _ => e) (fun _ => e.chart) (R u) q
    (fun j => e.chart.map_target (cell j)) (fun i => (piece i).2) (fun i => (piece i).1)
  let T (p : State × Control 2) := (p.1,R p.2)
  have ct : ContDiff ℝ k T := contDiff_fst.prodMk (R.contDiff.comp contDiff_snd)
  have initial : e.chart (q 0) = e.chart x := by rw [coord,P.first,start]
  rw [initial] at cs fg
  refine ⟨F ∘ T,cs.comp (e.chart x,u) ct.contDiffAt,?_⟩
  have pull : Tendsto T (𝓝 (e.chart x,u)) (𝓝 (e.chart x,R u)) := ct.continuous.tendsto _
  filter_upwards [pull fg] with b hb
  exact ⟨hb.1,hb.2.1,fun w => (graph b.2 _ w).trans (hb.2.2 w)⟩

open IsManifold
open scoped Manifold ContDiff

theorem transition_smooth (a b : OpenPartialHomeomorph M State)
    (ha : a ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (hb : b ∈ maximalAtlas 𝓘(ℝ,State) ∞ M)
    (p : M) (hp : p ∈ a.source) (hp' : p ∈ b.source) :
    ContDiffAt ℝ k (b ∘ a.symm) (a p) := by
  have inside : a p ∈ (a.symm.trans b).source :=
    ⟨a.map_source hp,show a.symm (a p) ∈ b.source by rw [a.left_inv hp]; exact hp'⟩
  have sm : ContDiffOn ℝ ∞ (b ∘ a.symm) (a.symm.trans b).source := by
    have h := (compatible_of_mem_maximalAtlas ha hb).1
    change ContDiffOn ℝ ∞ (b ∘ a.symm) ((a.symm.trans b).source ∩ range (𝓘(ℝ,State))) at h
    simpa using h
  exact ((sm _ inside).contDiffAt ((a.symm.trans b).open_source.mem_nhds inside)).of_le (mod_cast (le_top : (k : ℕ∞) ≤ ⊤))

theorem segment_in_charts_of_graph (e : Frame M m) (u : Control m) (x y : M)
    (s : Segment e u x y) (k : ℕ) (localGraph : HasSmoothSegmentGraph e k (e.chart x,u))
    (a b : OpenPartialHomeomorph M State)
    (ha : a ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (hb : b ∈ maximalAtlas 𝓘(ℝ,State) ∞ M)
    (hx : x ∈ a.source) (hy : y ∈ b.source) :
    ∃ H : State × Control m → State, ContDiffAt ℝ k H (a x,u) ∧
      ∀ᶠ p in 𝓝 (a x,u), p.1 ∈ a.target ∧ H p ∈ b.target ∧
        ∀ z, Segment e p.2 (a.symm p.1) z ↔ z = b.symm (H p) := by
  obtain ⟨F,cs,gr⟩ := localGraph
  have g := gr.self_of_nhds
  have endpoint : e.chart.symm (F (e.chart x,u)) = y := by
    apply ((g.2.2 y).mp ?_).symm
    simpa only [e.chart.left_inv s.1] using s
  let I (p : State × Control m) := (e.chart (a.symm p.1),p.2)
  have base : I (a x,u) = (e.chart x,u) := by simp [I,a.left_inv hx]
  have ci : ContDiffAt ℝ k I (a x,u) := ((transition_smooth a e.chart ha e.compatible x hx s.1).comp
    (a x,u) contDiffAt_fst).prodMk contDiffAt_snd
  have inner : ContDiffAt ℝ k (F ∘ I) (a x,u) := (base.symm ▸ cs).comp (a x,u) ci
  have val : (F ∘ I) (a x,u) = e.chart y := by
    rw [Function.comp_apply,base,← endpoint,e.chart.right_inv g.2.1]
  have co := transition_smooth (k := k) e.chart b e.compatible hb y s.2.1 hy
  rw [← val] at co
  refine ⟨(b ∘ e.chart.symm) ∘ (F ∘ I),co.comp (a x,u) inner,?_⟩
  have pull := ci.continuousAt.tendsto
  rw [base] at pull
  have first : ContinuousAt (a.symm ∘ (Prod.fst : State × Control m → State)) (a x,u) :=
    (a.symm.continuousAt (a.map_source hx)).comp (x := (a x,u)) continuousAt_fst
  have last : ContinuousAt (e.chart.symm ∘ (F ∘ I)) (a x,u) :=
    (e.chart.symm.continuousAt (val ▸ e.chart.map_source s.2.1)).comp inner.continuousAt
  have firstMem : a.symm (a x) ∈ e.chart.source := (a.left_inv hx).symm ▸ s.1
  have lastMem : e.chart.symm ((F ∘ I) (a x,u)) ∈ b.source := by rw [val,e.chart.left_inv s.2.1]; exact hy
  filter_upwards [pull gr,continuousAt_fst (a.open_target.mem_nhds (a.map_source hx)),
    first (e.chart.open_source.mem_nhds firstMem),last (b.open_source.mem_nhds lastMem)] with p gp ap ip op
  refine ⟨ap,b.map_source op,fun z => ?_⟩
  change Segment e p.2 (a.symm p.1) z ↔ z = b.symm (b (e.chart.symm (F (I p))))
  change e.chart.symm (F (I p)) ∈ b.source at op
  change a.symm p.1 ∈ e.chart.source at ip
  rw [b.left_inv op]
  have eq := gp.2.2 z
  change Segment e p.2 (e.chart.symm (e.chart (a.symm p.1))) z ↔ _ at eq
  rwa [e.chart.left_inv ip] at eq

theorem segment_in_charts (e : Frame M 2) (u : Control 2) (x y : M)
    (s : Segment e u x y) (k : ℕ) (hk : 1 ≤ (k : WithTop ℕ∞))
    (a b : OpenPartialHomeomorph M State)
    (ha : a ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (hb : b ∈ maximalAtlas 𝓘(ℝ,State) ∞ M)
    (hx : x ∈ a.source) (hy : y ∈ b.source) :
    ∃ H : State × Control 2 → State, ContDiffAt ℝ k H (a x,u) ∧
      ∀ᶠ p in 𝓝 (a x,u), p.1 ∈ a.target ∧ H p ∈ b.target ∧
        ∀ z, Segment e p.2 (a.symm p.1) z ↔ z = b.symm (H p) :=
  segment_in_charts_of_graph e u x y s k (arbitrary_segment_graph e u x y s k hk) a b ha hb hx hy

/-- In the original fixed-source path relation, the endpoint in any smooth target
chart is a locally single-valued graph of all the independent controls.
Its actual differential tests the original geometric singularity predicate. -/
theorem path_endpoint_of_segment_graphs [IsManifold 𝓘(ℝ, State) ∞ M]
    (e : Fin n → Frame M m) (u : Fin n → Control m)
    (x y : M) (path : Joins e u x y) (c : OpenPartialHomeomorph M State)
    (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (hy : y ∈ c.source)
    (k : ℕ) (hk : 1 ≤ (k : WithTop ℕ∞))
    (localGraph : ∀ (d : Frame M m) (v : Control m) (s t : M), Segment d v s t → HasSmoothSegmentGraph d k (d.chart s,v)) :
    ∃ E : (Fin n → Control m) → State, E u = c y ∧ ContDiffAt ℝ k E u ∧
      (∀ᶠ v in 𝓝 u, E v ∈ c.target ∧ ∀ z, Joins e v x z ↔ z = c.symm (E v)) ∧
      (Singular e u x y ↔ ¬ Function.Surjective (fderiv ℝ E u)) := by
  classical
  obtain ⟨q,rfl,rfl,seg⟩ := path
  let charts (j : Fin (n+1)) := if j = Fin.last n then c else chartAt State (q j)
  have last : charts (Fin.last n) = c := by simp [charts]
  have atlas (j) : charts j ∈ maximalAtlas 𝓘(ℝ,State) ∞ M := by
    unfold charts
    split <;> first | exact hc | exact chart_mem_maximalAtlas _
  have atQ (j) : q j ∈ (charts j).source := by
    unfold charts
    split
    · next h => exact h ▸ hy
    · exact mem_chart_source _ _
  obtain ⟨F,cs,value,gr⟩ := compose_graphs e charts u q atQ seg
    (fun i => segment_in_charts_of_graph _ _ _ _ (seg i) k (localGraph _ _ _ _ (seg i)) _ _ (atlas _) (atlas _) (atQ _) (atQ _))
  let A := fun v : Fin n → Control m => (charts 0 (q 0),v)
  have sm : ContDiffAt ℝ k A u := contDiffAt_const.prodMk contDiffAt_id
  let E := F ∘ A
  have de : ContDiffAt ℝ k E u := cs.comp u sm
  rw [last] at value gr
  have graph : ∀ᶠ v in 𝓝 u, E v ∈ c.target ∧ ∀ z, Joins e v (q 0) z ↔ z = c.symm (E v) := by
    filter_upwards [sm.continuousAt.tendsto gr] with v h
    exact ⟨h.2.1,by simpa only [A,E,Function.comp_apply,(charts 0).left_inv (atQ 0)] using h.2.2⟩
  refine ⟨E,value,de,graph,?_⟩
  rw [singular_iff_in_chart e u _ _ c hc hy]
  constructor
  · rintro ⟨G,D,_,gg,dg,defect⟩
    have same : G =ᶠ[𝓝 u] E := by
      filter_upwards [graph,gg] with v he hg
      have endEq := (he.2 _).mp ((hg.2 _).mpr rfl)
      simpa only [c.right_inv hg.1,c.right_inv he.1] using congrArg c endEq
    rwa [← same.fderiv_eq,dg.fderiv]
  · exact fun defect => ⟨E,_,value,graph,(de.differentiableAt hk).hasFDerivAt,defect⟩

theorem path_endpoint_and_singularity [IsManifold 𝓘(ℝ, State) ∞ M]
    (e : Fin n → Frame M 2) (u : Fin n → Control 2)
    (x y : M) (path : Joins e u x y) (c : OpenPartialHomeomorph M State)
    (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (hy : y ∈ c.source)
    (k : ℕ) (hk : 1 ≤ (k : WithTop ℕ∞)) :
    ∃ E : (Fin n → Control 2) → State, E u = c y ∧ ContDiffAt ℝ k E u ∧
      (∀ᶠ v in 𝓝 u, E v ∈ c.target ∧ ∀ z, Joins e v x z ↔ z = c.symm (E v)) ∧
      (Singular e u x y ↔ ¬ Function.Surjective (fderiv ℝ E u)) :=
  path_endpoint_of_segment_graphs e u x y path c hc hy k hk (fun d v s t h => arbitrary_segment_graph d v s t h k hk)

#print axioms prescribed_composite_graph
#print axioms arbitrary_segment_graph
#print axioms path_endpoint_and_singularity

/-- With every preceding block fixed, the whole endpoint is locally equal
to the endpoint of the final segment for all its control variations. -/
theorem last_slice_agrees (e : Fin (n+1) → Frame M m) (u : Fin (n+1) → Control m)
    (q : Fin ((n+1)+1) → M) (seg : ∀ i, Segment (e i) (u i) (q i.castSucc) (q i.succ))
    (c : OpenPartialHomeomorph M State) (F : (Fin (n+1) → Control m) → State)
    (graph : ∀ᶠ b in 𝓝 u, F b ∈ c.target ∧ ∀ y, Joins e b (q 0) y ↔ y = c.symm (F b))
    (G : Control m → State)
    (localGraph : ∀ᶠ v in 𝓝 (u (Fin.last n)), G v ∈ c.target ∧ ∀ y,
      Segment (e (Fin.last n)) v (q (Fin.last n).castSucc) y ↔ y = c.symm (G v)) :
    (fun v => F (Function.update u (Fin.last n) v)) =ᶠ[𝓝 (u (Fin.last n))] G := by
  let j := Fin.last n
  have push : Tendsto (Function.update u j) (𝓝 (u j)) (𝓝 u) := by
    simpa using (continuous_const.update j continuous_id : Continuous (Function.update u j)).tendsto (u j)
  filter_upwards [push graph,localGraph] with v full tail
  let y := c.symm (G v)
  have lastSeg := (tail.2 y).mpr rfl
  let nodes : Fin ((n+1)+1) → M := Fin.snoc (fun i => q i.castSucc) y
  have join : Joins e (Function.update u j v) (q 0) y := by
    refine ⟨nodes,by simp [nodes],by simp [nodes],?_⟩
    intro i
    refine Fin.lastCases ?_ (fun l => ?_) i
    · simpa [nodes,j,Fin.succ_last] using lastSeg
    · have ne : l.castSucc ≠ j := Fin.ne_last_of_lt (Fin.castSucc_lt_last l)
      simpa [nodes,Function.update_of_ne ne,← Fin.castSucc_succ] using seg l.castSucc
  have eq := congrArg c ((full.2 y).mp join)
  change c (c.symm (G v)) = c (c.symm (F (Function.update u j v))) at eq
  simpa only [c.right_inv tail.1,c.right_inv full.1] using eq.symm

/-- Freeze the original controls before the last piece. For any representative
of the whole endpoint, its restriction to this affine slice agrees locally
with the genuine last-segment endpoint, including its full second derivative. -/
theorem terminal_endpoint_restriction (e : Fin (n+1) → Frame M 2) (u : Fin (n+1) → Control 2)
    (q : Fin ((n+1)+1) → M) (seg : ∀ i, Segment (e i) (u i) (q i.castSucc) (q i.succ))
    (c : OpenPartialHomeomorph M State) (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M)
    (hy : q (Fin.last (n+1)) ∈ c.source) (F : (Fin (n+1) → Control 2) → State)
    (graph : ∀ᶠ b in 𝓝 u, F b ∈ c.target ∧ ∀ y, Joins e b (q 0) y ↔ y = c.symm (F b)) :
    let j := Fin.last n
    let H := fun v => F (Function.update u j v)
    ∃ G : Control 2 → State, ContDiffAt ℝ 2 G (u j) ∧
      (∀ᶠ v in 𝓝 (u j), G v ∈ c.target ∧ ∀ y, Segment (e j) v (q j.castSucc) y ↔ y = c.symm (G v)) ∧
      H =ᶠ[𝓝 (u j)] G ∧ fderiv ℝ (fderiv ℝ H) (u j) = fderiv ℝ (fderiv ℝ G) (u j) := by
  let j := Fin.last n
  let a := (e j).chart
  obtain ⟨g,cg,gg⟩ := segment_in_charts _ _ _ _ (seg j) 2 (by decide) a c (e j).compatible hc (seg j).1 hy
  let G := fun v : Control 2 => g (a (q j.castSucc),v)
  have incl : ContDiffAt ℝ 2 (fun v : Control 2 => (a (q j.castSucc),v)) (u j) :=
    contDiffAt_const.prodMk contDiffAt_id
  have localGraph : ∀ᶠ v in 𝓝 (u j), G v ∈ c.target ∧
      ∀ y, Segment (e j) v (q j.castSucc) y ↔ y = c.symm (G v) := by
    filter_upwards [incl.continuousAt.tendsto gg] with v hv
    exact ⟨hv.2.1,by simpa only [a.left_inv (seg j).1] using hv.2.2⟩
  have same := last_slice_agrees e u q seg c F graph G localGraph
  exact ⟨G,cg.comp (u j) incl,localGraph,same,(same.fderiv (𝕜 := ℝ)).fderiv_eq⟩

#print axioms terminal_endpoint_restriction
end MinimizingSard.Five
