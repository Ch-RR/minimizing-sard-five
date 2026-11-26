import SmoothShortFlow
import FrameChangeLayers

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology ContDiff Manifold
namespace MinimizingSard.Five

private theorem flow_parameter (V : State → State) (hV : ContDiff ℝ ∞ V) (q : State) (nz : V q ≠ 0) :
    ∃ (l : Fin 5) (P : State → State) (E : State ≃L[ℝ] State), P 0 = q ∧ HasFDerivAt P E.toContinuousLinearMap 0 ∧
      ∀ᶠ z in 𝓝 0, ContDiffAt ℝ ∞ P z ∧ fderiv ℝ P z (Pi.single l 1) = V (P z) := by
  classical
  have ex : ∃ l, V q l ≠ 0 := by
    by_contra! all
    exact nz (funext all)
  obtain ⟨l,vl⟩ := ex
  let u : State := Pi.single l 1
  let L := (ContinuousLinearMap.proj l : State →L[ℝ] ℝ)
  have lu : L u = 1 := by simp [L,u]
  let R := (ContinuousLinearMap.id ℝ State) - L.smulRight u
  have ru : R u = 0 := by change u - L u • u = 0; simp [lu]
  let g (z : State) := (q+R z,L z)
  have cg : ContDiff ℝ ∞ g := (contDiff_const.add R.contDiff).prodMk L.contDiff
  have g0 : g 0 = (q,0) := by simp [g]
  obtain ⟨f,flow⟩ := smooth_short_flow V hV q
  have push : Tendsto g (𝓝 0) (𝓝 (q,0)) := g0 ▸ cg.continuous.tendsto 0
  let P := f ∘ g
  have p0 : P 0 = q := by simpa only [P,Function.comp_apply,g0] using flow.self_of_nhds.2.1
  have near : ∀ᶠ z in 𝓝 0, ContDiffAt ℝ ∞ P z ∧ fderiv ℝ P z u = V (P z) := by
    filter_upwards [push flow] with z hz
    obtain ⟨cf,_,ode⟩ := (show ContDiffAt ℝ ∞ f (g z) ∧ _ ∧ _ from hz)
    have cp : ContDiffAt ℝ ∞ P z := cf.comp z cg.contDiffAt
    refine ⟨cp,?_⟩
    let line (s : ℝ) := z+s • u
    have dz : HasDerivAt line u 0 := by
      simpa [line] using ((hasDerivAt_id (0:ℝ)).smul_const u).const_add z
    have at0 : line 0 = z := by simp [line]
    have D := ((at0.symm ▸ cp : ContDiffAt ℝ ∞ P (line 0)).differentiableAt (by decide)).hasFDerivAt.comp_hasDerivAt 0 dz
    have hd : HasDerivAt (P ∘ line) (V (P z)) 0 := by
      have s0 : L z + (0:ℝ) = L z := add_zero _
      have ht : HasDerivAt (fun s : ℝ => f (q+R z,s)) (V (P z)) (L z+0) := s0.symm ▸ ode
      have shift := ht.scomp 0 ((hasDerivAt_id (0:ℝ)).const_add (L z))
      apply (by simpa only [one_smul] using shift : HasDerivAt ((fun s => f (q+R z,s)) ∘ (fun s => L z+s)) (V (P z)) 0).congr_of_eventuallyEq
      exact .of_forall fun s => by simp [P,g,line,ru,lu]
    simpa only [at0] using D.unique hd
  let D := fderiv ℝ P 0
  have reg := near.self_of_nhds.1
  have col : D u = V q := p0 ▸ near.self_of_nhds.2
  have fixed (h : State) (lh : L h = 0) : D h = h := by
    let line (s : ℝ) := s • h
    have dz : HasDerivAt line h 0 := by simpa [line] using (hasDerivAt_id (0:ℝ)).smul_const h
    have lin0 : line 0 = 0 := zero_smul _ _
    have Dlin := ((lin0.symm ▸ reg : ContDiffAt ℝ ∞ P (line 0)).differentiableAt (by decide)).hasFDerivAt.comp_hasDerivAt 0 dz
    have rh : R h = h := by change h - L h • u = h; simp [lh]
    have lim : Tendsto (g ∘ line) (𝓝 0) (𝓝 (q,0)) := push.comp (lin0 ▸ dz.continuousAt.tendsto)
    have eq : (P ∘ line) =ᶠ[𝓝 0] (fun s : ℝ => q+s • h) := by
      filter_upwards [lim flow] with s hs
      have init := (show ContDiffAt ℝ ∞ f (g (line s)) ∧ _ ∧ _ from hs).2.1
      simpa [P,line,g,rh,lh] using init
    exact (by simpa only [lin0] using Dlin.unique ((dz.const_add q).congr_of_eventuallyEq eq))
  have inj : Function.Injective D := by
    apply (LinearMap.ker_eq_bot (f := D.toLinearMap)).mp
    apply eq_bot_iff.mpr
    intro h hh
    have dh : D h = 0 := hh
    have lr : L (R h) = 0 := by change L (h-L h • u) = 0; simp [lu]
    have dec : R h + L h • u = h := sub_add_cancel _ _
    have d := congrArg D dec
    rw [map_add,map_smul,dh,col,fixed _ lr] at d
    have a := congrArg L d
    rw [map_add,map_smul,lr,map_zero,zero_add,smul_eq_mul] at a
    have zero : L h = 0 := (mul_eq_zero.mp a).resolve_right vl
    change h = 0
    exact (fixed h zero).symm.trans dh
  let E := (LinearEquiv.ofBijective D.toLinearMap ⟨inj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp inj⟩).toContinuousLinearEquiv
  exact ⟨l,P,E,p0,(reg.differentiableAt (by decide)).hasFDerivAt,near⟩


/-- A local smooth coordinate change taking a nonzero smooth field to a
constant coordinate vector throughout its open source. -/
theorem euclidean_word_flowbox (Y : State → State) (U : Set State) (op : IsOpen U)
    (q : State) (inside : q ∈ U) (smooth : ContDiffOn ℝ ∞ Y U) (nz : Y q ≠ 0) :
    ∃ (A : OpenPartialHomeomorph State State) (l : Fin 5), q ∈ A.source ∧ A.source ⊆ U ∧
      ContDiffOn ℝ ∞ A A.source ∧ ContDiffOn ℝ ∞ A.symm A.target ∧
      ∀ z ∈ A.source, fderiv ℝ A z (Y z) = Pi.single l 1 := by
  obtain ⟨V,cv,agree⟩ := smooth_germ_extension op inside Y smooth
  obtain ⟨l,P,E,p0,d,near⟩ := flow_parameter V cv q (by rwa [agree.self_of_nhds])
  obtain ⟨T,te,mem,ci⟩ := smooth_inverse_neighborhood P 0 E (near.mono fun _ h => h.1) d
  have eqT : T 0 = q := by rw [te,p0]
  have tq : q ∈ T.target := eqT ▸ T.map_source mem
  have inv0 : T.symm q = 0 := eqT ▸ T.left_inv mem
  have lim : Tendsto T.symm (𝓝 q) (𝓝 0) := by simpa only [inv0] using (T.symm.continuousAt tq).tendsto
  have ci' : ∀ᶠ z in 𝓝 q, ContDiffAt ℝ ∞ T.symm z := p0 ▸ ci
  have good : ∀ᶠ z in 𝓝 q, z ∈ U ∧ V z = Y z ∧ ContDiffAt ℝ ∞ T.symm z ∧
      ContDiffAt ℝ ∞ P (T.symm z) ∧ fderiv ℝ P (T.symm z) (Pi.single l 1) = V (P (T.symm z)) :=
    (show ∀ᶠ z in 𝓝 q, z ∈ U from op.mem_nhds inside).and (agree.and (ci'.and (lim near)))
  obtain ⟨r,rp,ball⟩ := Metric.mem_nhds_iff.mp good
  let A := T.symm.restr (Metric.ball q r)
  have src : A.source = T.target ∩ Metric.ball q r := T.symm.restr_source' _ Metric.isOpen_ball
  refine ⟨A,l,src.symm ▸ ⟨tq,Metric.mem_ball_self rp⟩,fun z hz => (ball ((src ▸ hz).2)).1,?_,?_,?_⟩
  · intro z hz
    exact (ball ((src ▸ hz).2)).2.2.1.contDiffWithinAt
  · intro p hp
    have az : A.symm p ∈ A.source := A.map_target hp
    have hi := (ball ((src ▸ az).2)).2.2.2.1
    have id : T.symm (A.symm p) = p := A.right_inv hp
    rw [id] at hi
    change ContDiffWithinAt ℝ ∞ (T : State → State) _ p
    rw [te]; exact hi.contDiffWithinAt
  · intro z hz
    obtain ⟨tz,br⟩ := (show z ∈ T.target ∩ Metric.ball q r from src ▸ hz)
    obtain ⟨_,ag,inv,reg,col⟩ := ball br
    let p := T.symm z
    have pz : P p = z := by rw [← te]; exact T.right_inv tz
    have germ : (T.symm ∘ P) =ᶠ[𝓝 p] id := by
      filter_upwards [T.open_source.mem_nhds (T.map_target tz)] with w hw
      exact (te ▸ T.left_inv hw)
    have chain := germ.fderiv_eq (𝕜 := ℝ)
    rw [fderiv_comp p (pz.symm ▸ (inv.differentiableAt (by decide))) (reg.differentiableAt (by decide)),pz,fderiv_id] at chain
    have applied := DFunLike.congr_fun chain (Pi.single l 1)
    change fderiv ℝ T.symm z (fderiv ℝ P p (Pi.single l 1)) = Pi.single l 1 at applied
    rw [col,pz,ag] at applied
    exact applied

#print axioms euclidean_word_flowbox

variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M]
open OpenPartialHomeomorph in
private theorem compose_chart {m : ℕ} (b : Frame M m) (A : OpenPartialHomeomorph State State)
    (ca : ContDiffOn ℝ ∞ A A.source) (ci : ContDiffOn ℝ ∞ A.symm A.target) :
    b.chart.trans A ∈ maximalAtlas 𝓘(ℝ,State) ∞ M := by
  let G := contDiffGroupoid ∞ 𝓘(ℝ,State)
  have ag : A ∈ G := by
    change A ∈ contDiffGroupoid ∞ 𝓘(ℝ,State)
    rw [contDiffGroupoid,mem_groupoid_of_pregroupoid,contDiffPregroupoid]
    constructor
    · simpa using ca
    · simpa using ci
  intro c hc
  obtain ⟨bc,cb⟩ := b.compatible c hc
  constructor
  · rw [trans_symm_eq_symm_trans_symm,trans_assoc]
    exact G.trans (G.symm ag) bc
  · rw [← trans_assoc]
    exact G.trans cb ag

/-- The five reference fields admit genuine smooth straightening charts at
all their nonzero points for the original rank-two geometry. -/
theorem frame_word_straightening {m : ℕ} (b : Frame M m) (word : BracketWord m) (y : M)
    (by' : y ∈ b.chart.source) (nz : word.eval b.X (b.chart y) ≠ 0) :
    ∃ (a : OpenPartialHomeomorph M State) (l : Fin 5), a ∈ maximalAtlas 𝓘(ℝ,State) ∞ M ∧ y ∈ a.source ∧
      ∀ z ∈ a.source, z ∈ b.chart.source ∧
        fderiv ℝ (a ∘ b.chart.symm) (b.chart z) (word.eval b.X (b.chart z)) = Pi.single l 1 := by
  let W := word.eval b.X
  have reg (w : BracketWord m) : ContDiffOn ℝ ∞ (w.eval b.X) b.chart.target := by
    induction w with
    | field j => exact b.smooth j
    | bracket a c ha hc =>
      intro z hz
      exact (((ha z hz).contDiffAt (b.chart.open_target.mem_nhds hz)).lieBracket_vectorField
        ((hc z hz).contDiffAt (b.chart.open_target.mem_nhds hz)) (by simp)).contDiffWithinAt
  obtain ⟨A,l,inside,_,ca,ci,straight⟩ := euclidean_word_flowbox W b.chart.target b.chart.open_target
    (b.chart y) (b.chart.map_source by') (reg _) nz
  refine ⟨b.chart.trans A,l,compose_chart b A ca ci,⟨by',inside⟩,?_⟩
  intro z hz
  refine ⟨hz.1,?_⟩
  have eq : ((b.chart.trans A) ∘ b.chart.symm) =ᶠ[𝓝 (b.chart z)] (A : State → State) := by
    filter_upwards [b.chart.open_target.mem_nhds (b.chart.map_source hz.1)] with p hp
    exact congrArg A (b.chart.right_inv hp)
  rw [eq.fderiv_eq]; exact straight _ hz.2

#print axioms frame_word_straightening

theorem local_word_straightening (Γ : Geometry M 2) : LocalWordStraightening Γ := by
  intro b _ i y inside nz
  obtain ⟨a,l,ha,ay,rect⟩ := frame_word_straightening b (thirdWord i) y inside nz
  exact ⟨a,ha,ay,fun z hz => ⟨(rect z hz).1,l,(rect z hz).2⟩⟩

#print axioms local_word_straightening

/-- Unconditional rank-three endpoint differential branch for the original
five-dimensional rank-two controls and the original length. -/
theorem ae_corank_two_length_multiplier [IsManifold 𝓘(ℝ,State) ∞ M] (Γ : Geometry M 2)
    (x : M) (c : OpenPartialHomeomorph M State) (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) :
    ∀ᵐ q : State, q ∈ c.target → ∀ {n : ℕ} (d : Fin (n+1) → Frame M 2)
      (w : Fin (n+1) → Control 2) (G : (Fin (n+1) → Control 2) → State),
      let y := c.symm q
      x ≠ y → (∀ j, d j ∈ Γ.frames) → Joins d w x y →
      (∀ (k : ℕ) (r : Fin (k+1) → Frame M 2) (b : Fin (k+1) → Control 2),
        (∀ j, r j ∈ Γ.frames) → Joins r b x y → length w ≤ length b) →
      (∀ᶠ v in 𝓝 w, G v ∈ c.target ∧ ∀ z, Joins d v x z ↔ z = c.symm (G v)) →
      Module.finrank ℝ (LinearMap.range (fderiv ℝ G w).toLinearMap) = 3 →
      HasCostMultiplier length (fderiv ℝ G w) w :=
  ae_corank_two_of_local_straightening Γ (local_word_straightening Γ) x c hc

#print axioms ae_corank_two_length_multiplier

end MinimizingSard.Five
