import WordAxisConnectors
import WordFlowBox

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M]
private abbrev ShortIndex := Fin 3 ⊕ (Fin 3 × Fin 3)
private def shortWord : ShortIndex → BracketWord 3
  | .inl i => .field i
  | .inr (i,j) => .bracket (.field i) (.field j)
private theorem pos_word (w : BracketWord 3) : 0 < w.order := by
  induction w with
  | field => exact Nat.one_pos
  | bracket a b ha hb => change 0 < a.order+b.order; omega
private theorem word_one (w : BracketWord 3) (hw : w.order ≤ 1) : ∃ i, w = .field i := by
  cases w with
  | field i => exact ⟨i,rfl⟩
  | bracket a b =>
    have := pos_word a
    have := pos_word b
    change a.order+b.order ≤ 1 at hw
    omega
private theorem short_complete (w : BracketWord 3) (hw : w.order ≤ 2) : ∃ i, shortWord i = w := by
  cases w with
  | field i => exact ⟨.inl i,rfl⟩
  | bracket a b =>
    have := pos_word a
    have := pos_word b
    change a.order+b.order ≤ 2 at hw
    obtain ⟨i,rfl⟩ := word_one a (by omega)
    obtain ⟨j,rfl⟩ := word_one b (by omega)
    exact ⟨.inr (i,j),rfl⟩

private def Rectifies (b : Frame M 3) (w : BracketWord 3) (l : Fin 5) (a : OpenPartialHomeomorph M State) :=
  ∀ z ∈ a.source, z ∈ b.chart.source ∧
    fderiv ℝ (a ∘ b.chart.symm) (b.chart z) (w.eval b.X (b.chart z)) = Pi.single l 1

private theorem select_charts (Γ : Geometry M 3) (c : OpenPartialHomeomorph M State)
    (T : Set Γ.frames) (count : T.Countable) :
    ∃ S : Set (OpenPartialHomeomorph M State), S.Countable ∧
      (∀ a ∈ S, a ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) ∧
      ∀ b ∈ T, ∀ i : ShortIndex × Fin 5, ∀ y ∈ c.source,
        (∃ a ∈ maximalAtlas 𝓘(ℝ,State) ∞ M, y ∈ a.source ∧ Rectifies b.val (shortWord i.1) i.2 a) →
        ∃ a ∈ S, y ∈ a.source ∧ Rectifies b.val (shortWord i.1) i.2 a := by
  classical
  letI : Countable T := count.to_subtype
  let C (b : T) (i : ShortIndex × Fin 5) := {a : OpenPartialHomeomorph M State //
    a ∈ maximalAtlas 𝓘(ℝ,State) ∞ M ∧ Rectifies b.val.val (shortWord i.1) i.2 a}
  let V (b : T) (i : ShortIndex × Fin 5) (a : C b i) := (c.symm.trans a.val).source
  have sub (b : T) (i : ShortIndex × Fin 5) : ∃ R : Set (C b i), R.Countable ∧
      (⋃ a, V b i a) ⊆ ⋃ a ∈ R, V b i a :=
    (IsLindelof.of_coe : IsLindelof (⋃ a, V b i a)).elim_countable_subcover
      (V b i) (fun a => (c.symm.trans a.val).open_source) (Subset.rfl)
  choose R cr cov using sub
  let S := ⋃ b : T, ⋃ i : ShortIndex × Fin 5, Subtype.val '' R b i
  refine ⟨S,countable_iUnion (fun b => countable_iUnion fun i => (cr b i).image _),?_,?_⟩
  · intro a ha
    obtain ⟨b,ha⟩ := mem_iUnion.mp ha
    obtain ⟨i,r,_,rfl⟩ := mem_iUnion.mp ha
    exact r.property.1
  · intro b bt i y cy localBox
    obtain ⟨a,ha,ay,rect⟩ := localBox
    let b' : T := ⟨b,bt⟩
    let a' : C b' i := ⟨a,ha,rect⟩
    have hit : c y ∈ V b' i a' := ⟨c.map_source cy,by change c.symm (c y) ∈ a.source; rwa [c.left_inv cy]⟩
    obtain ⟨r,hr⟩ := mem_iUnion.mp (cov b' i (mem_iUnion.mpr ⟨a',hit⟩))
    obtain ⟨rt,inside⟩ := mem_iUnion.mp hr
    exact ⟨r.val,mem_iUnion.mpr ⟨b',mem_iUnion.mpr ⟨i,⟨r,rt,rfl⟩⟩⟩,
      (c.left_inv cy) ▸ (show c.symm (c y) ∈ r.val.source from inside.2),r.property.2⟩


variable [IsManifold 𝓘(ℝ,State) ∞ M]
/-- The same countable family of charts supplies, at almost every endpoint,
a square-root direction transverse to any prescribed three-dimensional
space, together with cubic-root connectors in all directions. -/
theorem ae_rank_three_axes (Γ : Geometry M 3) (c : OpenPartialHomeomorph M State)
    (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) :
    ∃ S : Set (OpenPartialHomeomorph M State), S.Countable ∧
      (∀ a ∈ S, a ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) ∧ ∀ᵐ z : State, z ∈ c.target →
        let y := c.symm z
        ∀ W : Submodule ℝ State, Module.finrank ℝ W = 3 →
        ∃ a ∈ S, y ∈ a.source ∧ ∃ l : Fin 5,
          Pi.single l 1 ∉ W.map (fderiv ℝ (a ∘ c.symm) z).toLinearMap ∧
          AxisConnectors Γ a (a y) (Pi.single l 1) ∧ ShortConnectors Γ a (a y) (1/3) := by
  classical
  let U (e : Γ.frames) := (c.symm.trans e.val.chart).source
  have covers (q) (hq : q ∈ c.target) : q ∈ ⋃ e, U e := by
    obtain ⟨e,he,inside⟩ := Γ.cover (c.symm q)
    exact mem_iUnion.mpr ⟨⟨e,he⟩,hq,inside⟩
  obtain ⟨T,count,cov⟩ := (IsLindelof.of_coe : IsLindelof c.target).elim_countable_subcover
    U (fun e => (c.symm.trans e.val.chart).open_source) covers
  obtain ⟨S,sc,atlas,cover⟩ := select_charts Γ c T count
  refine ⟨S,sc,atlas,?_⟩
  letI : Countable T := count.to_subtype
  have good (b : Γ.frames) : ∀ᵐ z : State, z ∈ U b →
      4 ≤ Module.finrank ℝ (wordLayer b.val.X (b.val.chart (c.symm z)) 2) ∧
      ShortConnectors Γ b.val.chart (b.val.chart (c.symm z)) (1/3) := by
    exact ae_chart_overlap b.val.chart c b.val.compatible hc
      (fun p => 4 ≤ Module.finrank ℝ (wordLayer b.val.X p 2) ∧ ShortConnectors Γ b.val.chart p (1/3))
      (ae_rank_three_connectors b.val b.property)
  filter_upwards [ae_all_iff.mpr (fun b : T => good b.val)] with z all
  intro hq y W dim
  obtain ⟨b,hit⟩ := mem_iUnion.mp (cov hq)
  obtain ⟨bt,inside⟩ := mem_iUnion.mp hit
  have ey : y ∈ b.val.chart.source := inside.2
  have cy : y ∈ c.source := c.map_target hq
  have zy : c y = z := c.right_inv hq
  obtain ⟨growth,repair⟩ := all ⟨b,bt⟩ inside
  let D := fderiv ℝ (c ∘ b.val.chart.symm) (b.val.chart y)
  obtain ⟨B,eqB⟩ := ContinuousLinearMap.IsInvertible.of_inverse
    (transition_left c b.val.chart hc b.val.compatible y cy ey)
    (transition_left b.val.chart c b.val.compatible hc y ey cy)
  have outside : ∃ w : BracketWord 3, w.order ≤ 2 ∧ D (w.eval b.val.X (b.val.chart y)) ∉ W := by
    by_contra! fail
    have sub : (wordLayer b.val.X (b.val.chart y) 2).map B.toLinearEquiv.toLinearMap ≤ W := by
      apply Submodule.map_le_iff_le_comap.mpr
      apply Submodule.span_le.mpr
      rintro _ ⟨w,ord,rfl⟩
      change B _ ∈ W
      exact (show B (w.eval b.val.X (b.val.chart y)) = D _ from DFunLike.congr_fun eqB _).symm ▸ fail w ord
    have le := Submodule.finrank_mono sub
    rw [B.toLinearEquiv.finrank_map_eq,dim] at le
    change 4 ≤ Module.finrank ℝ (wordLayer b.val.X (b.val.chart y) 2) at growth
    omega
  obtain ⟨w,ord,out⟩ := outside
  obtain ⟨i,rfl⟩ := short_complete w ord
  let w := shortWord i
  let f := b.val
  let v := w.eval f.X (f.chart y)
  have nz : v ≠ 0 := by intro zz; apply out; change D v ∈ W; rw [zz,map_zero]; exact W.zero_mem
  obtain ⟨a₀,l,h₀,y₀,r₀⟩ := frame_word_straightening f w y ey nz
  obtain ⟨a,mem,ay,rect⟩ := cover b bt (i,l) y cy ⟨a₀,h₀,y₀,r₀⟩
  have ha := atlas a mem
  let P := fderiv ℝ (a ∘ c.symm) (c y)
  have chain := transition_chain f.chart c a f.compatible hc ha y ey cy ay
  have maps : P (D v) = Pi.single l 1 := (DFunLike.congr_fun chain v).trans (rect y ay).2
  obtain ⟨A,eqA⟩ := ContinuousLinearMap.IsInvertible.of_inverse
    (transition_left a c ha hc y ay cy) (transition_left c a hc ha y cy ay)
  refine ⟨a,mem,ay,l,?_,?_,transfer_connectors a f.chart ha f.compatible y ay ey _ (by norm_num) repair⟩
  · rw [← zy,← maps]
    rintro ⟨h,hw,eq⟩
    have same : A h = A (D v) := (DFunLike.congr_fun eqA h).trans (eq.trans (DFunLike.congr_fun eqA (D v)).symm)
    exact out (A.injective same ▸ hw)
  · obtain ⟨R,order,lead⟩ := bracket_repair_word_of_profiles f (all_frame_generator_profiles f) b.property
      (f.chart.map_source ey) w (ord.trans (by decide))
    apply word_axis_connectors a f.chart ha f.compatible y ay ey _ R (order ▸ ord) _ repair
    have push : Tendsto (f.chart ∘ a.symm) (𝓝 (a y)) (𝓝 (f.chart y)) := by
      simpa only [Function.comp_apply,a.left_inv ay] using
        (transition_smooth (k := 1) a f.chart ha f.compatible y ay ey).continuousAt.tendsto
    filter_upwards [a.open_target.mem_nhds (a.map_source ay),push lead] with z hz value
    let t := a.symm z
    obtain ⟨fy,axis⟩ := rect t (a.map_target hz)
    have inv := transition_left f.chart a f.compatible ha t fy (a.map_target hz)
    have id := DFunLike.congr_fun inv (w.eval f.X (f.chart t))
    change fderiv ℝ (f.chart ∘ a.symm) (a t) (fderiv ℝ (a ∘ f.chart.symm) (f.chart t) _) = _ at id
    rw [axis,show a t = z from a.right_inv hz] at id
    exact id.trans value.symm

#print axioms ae_rank_three_axes
end MinimizingSard.Five
