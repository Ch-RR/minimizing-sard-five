import TerminalMovingEndpoint
import PulseExistence

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace MinimizingSard.Five
open Volterra PulseGeometry

variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M]

private def splitTime (d : ℝ) (hd : 0 < d) (h1 : d < 1) : TimePartition 2 where
  cut := ![0,1-d,1]
  first := rfl
  last := rfl
  increasing := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact sub_pos.mpr h1 | exact sub_lt_self _ hd | exact zero_lt_one | (exfalso; revert hij; decide)

/-- Pastes an arbitrary normalized last-interval variation after the fixed
prefix, as a bounded linear injection into the original segment control. -/
theorem terminal_control_injection (e : Frame M 2) (w pre u : Control 2) (d : ℝ)
    (hd : 0 < d) (h1 : d < 1)
    (pRep : ∀ᵐ s ∂volume.restrict (Icc (0:ℝ) 1), pre s = (1-d) • w ((1-d)*s))
    (uRep : ∀ᵐ s ∂volume.restrict (Icc (0:ℝ) 1), u s = d • w ((1-d)+d*s)) :
    ∃ J : Control 2 →L[ℝ] Control 2, Function.Injective J ∧
      (∀ h, ∀ᵐ t ∂volume.restrict (Ioc (0:ℝ) (1-d)), (w+J h) t = w t) ∧
      (∀ h, ∀ᵐ t ∂volume.restrict (Ioc (1-d) 1), J h t = d⁻¹ • h ((t-(1-d))/d)) ∧
      ∀ h (x k y : M), Segment e pre x k → Segment e (u+h) k y → Segment e (w+J h) x y := by
  let P := splitTime d hd h1
  obtain ⟨D,rep,rel⟩ := P.segment_iff_joins e
  obtain ⟨C,repC,back⟩ := P.coordinates 2
  have same (z : Control 2) (i : Fin 2) : C z i = D z i := by
    apply Lp.ext
    filter_upwards [repC z i,rep z i] with s hc hd using hc.trans hd.symm
  have d0 : P.duration 0 = 1-d := sub_zero _
  have d2 : P.duration 1 = d := by change 1-(1-d) = d; ring
  have left0 : P.left 0 = 0 := rfl
  have left1 : P.left 1 = 1-d := rfl
  have cut0 : P.block 0 = Ioc 0 (1-d) := rfl
  have cut1 : P.block 1 = Ioc (1-d) 1 := rfl
  have root0 : D w 0 = pre := by
    apply Lp.ext
    filter_upwards [rep w 0,pRep] with s hh hp
    simpa only [d0,left0,zero_add,← hp] using hh
  have root1 : D w 1 = u := by
    apply Lp.ext
    filter_upwards [rep w 1,uRep] with s hh hp
    simpa only [d2,left1,← hp] using hh
  let one := ContinuousLinearMap.single ℝ (fun _ : Fin 2 => Control 2) 1
  let J := D.symm.toContinuousLinearMap.comp one
  have coords (h : Control 2) : D (J h) = Pi.single 1 h := D.apply_symm_apply _
  have c0 (h : Control 2) : D (w+J h) 0 = pre := by simp [map_add,coords,root0]
  have c1 (h : Control 2) : D (w+J h) 1 = u+h := by simp [map_add,coords,root1]
  refine ⟨J,?_,?_,?_,?_⟩
  · intro h l eq
    have := congrArg (fun z : Control 2 => D z 1) eq
    simpa only [coords,Pi.single_eq_same] using this
  · intro h
    have a := back (w+J h) 0
    have b := back w 0
    rw [cut0,same,c0] at a
    rw [cut0,same,root0] at b
    filter_upwards [a,b] with t ha hb using ha.trans hb.symm
  · intro h
    have b := back (J h) 1
    simpa only [cut1,d2,left1,same,coords,Pi.single_eq_same] using b
  · intro h x k y before afterSeg
    apply (rel _ _ _).mpr
    refine ⟨![x,k,y],rfl,rfl,?_⟩
    intro i
    fin_cases i
    · change Segment e (D (w+J h) 0) x k
      rwa [c0]
    · change Segment e (D (w+J h) 1) k y
      rwa [c1]

#print axioms terminal_control_injection

private theorem attach_last {n : ℕ} (e : Fin (n+1) → Frame M 2)
    (w : Fin (n+1) → Control 2) (q : Fin (n+2) → M)
    (pieces : ∀ i, Segment (e i) (w i) (q i.castSucc) (q i.succ))
    (z : Fin (n+1) → Control 2) (y : M)
    (fixed : ∀ i : Fin n, z i.castSucc = w i.castSucc)
    (last : Segment (e (Fin.last n)) (z (Fin.last n)) (q (Fin.last n).castSucc) y) :
    Joins e z (q 0) y := by
  let nodes : Fin (n+2) → M := Fin.snoc (fun i => q i.castSucc) y
  refine ⟨nodes,by simp [nodes],by simp [nodes],?_⟩
  intro i
  refine Fin.lastCases ?_ (fun l => ?_) i
  · simpa [nodes,Fin.succ_last] using last
  · simpa [nodes,fixed,← Fin.castSucc_succ] using pieces l.castSucc

private theorem linear_cast {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (R : U ≃ₗᵢ[ℝ] V) {p : V → Prop}
    (h : ∀ᶠ v in 𝓝 0, p v) : ∀ᶠ u in 𝓝 0, p (R u) :=
  (show Tendsto R (𝓝 0) (𝓝 0) from R.map_zero ▸ R.continuous.tendsto 0) h

private theorem affine_derivatives {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (F : V → State) (w : V) (I : U →L[ℝ] V)
    (cf : ContDiffAt ℝ 2 F w) :
    let B := fun v => F (w + I v)
    fderiv ℝ B 0 = (fderiv ℝ F w).comp I ∧
      ∀ h l, fderiv ℝ (fderiv ℝ B) 0 h l = fderiv ℝ (fderiv ℝ F) w (I h) (I l) := by
  let g (v : U) := w + I v
  have cg : ContDiff ℝ 2 g := contDiff_const.add I.contDiff
  have dg (v : U) : fderiv ℝ g v = I := (I.hasFDerivAt.const_add w).fderiv
  have g0 : g 0 = w := by simp [g]
  have d2 : fderiv ℝ (fderiv ℝ g) (0 : U) = 0 := by
    rw [show fderiv ℝ g = fun _ => I from funext dg]
    exact fderiv_const_apply _
  have f0 : ContDiffAt ℝ 2 F (g 0) := g0.symm ▸ cf
  refine ⟨?_,?_⟩
  · exact (fderiv_comp 0 (f0.differentiableAt (by decide)) (cg.differentiable (by decide) 0)).trans (by rw [dg,g0])
  · intro h l
    have z := Transport.second_comp g F 0 h l cg.contDiffAt f0
    simpa only [dg 0,g0,d2,ContinuousLinearMap.zero_apply,map_zero,zero_add] using z

/-- Restriction of the actual whole path endpoint in its designated chart.
Both derivatives refer to the full input at the original control. -/
def WholeJet {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] (F : U → State)
    (w : U) (I : Controls →L[ℝ] U) (ψ : State → State) (A : Controls → State) (k : State) : Prop :=
  (fun h => F (w+I h)) =ᶠ[𝓝 0] ψ ∘ A ∧
  (∀ h, fderiv ℝ F w (I h) = fderiv ℝ ψ k (fderiv ℝ A 0 h)) ∧
  ∀ h l, fderiv ℝ (fderiv ℝ F) w (I h) (I l) =
    fderiv ℝ ψ k (fderiv ℝ (fderiv ℝ A) 0 h l) +
    fderiv ℝ (fderiv ℝ ψ) k (fderiv ℝ A 0 h) (fderiv ℝ A 0 l)

private theorem whole_jet_of_germ {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (F : U → State) (w : U) (I : Controls →L[ℝ] U) (ψ : State → State) (A : Controls → State)
    (k : State) (a0 : A 0 = k) (ca : ContDiffAt ℝ 2 A 0) (cf : ContDiffAt ℝ 2 F w)
    (cp : ContDiffAt ℝ 2 ψ k) (same : (fun h => F (w+I h)) =ᶠ[𝓝 0] ψ ∘ A) :
    WholeJet F w I ψ A k := by
  obtain ⟨d1,d2⟩ := affine_derivatives F w I cf
  have first := same.fderiv_eq (𝕜 := ℝ)
  rw [d1,fderiv_comp 0 ((a0.symm ▸ cp).differentiableAt (by decide)) (ca.differentiableAt (by decide)),a0] at first
  refine ⟨same,fun h => congrArg (fun L : Controls →L[ℝ] State => L h) first,?_⟩
  intro h l
  have z := Transport.second_comp A ψ 0 h l ca (a0.symm ▸ cp)
  rw [← (same.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ),a0,d2] at z
  exact z

open IsManifold
open scoped Manifold ContDiff

theorem transition_left [IsManifold 𝓘(ℝ, State) ∞ M] (a b : OpenPartialHomeomorph M State)
    (ha : a ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (hb : b ∈ maximalAtlas 𝓘(ℝ,State) ∞ M)
    (y : M) (ay : y ∈ a.source) (by' : y ∈ b.source) :
    (fderiv ℝ (a ∘ b.symm) (b y)).comp (fderiv ℝ (b ∘ a.symm) (a y)) =
      ContinuousLinearMap.id ℝ State := by
  have mem : a y ∈ (a.symm.trans b).source :=
    ⟨a.map_source ay, by change a.symm (a y) ∈ b.source; rwa [a.left_inv ay]⟩
  have same : ((a ∘ b.symm) ∘ (b ∘ a.symm)) =ᶠ[𝓝 (a y)] id := by
    filter_upwards [(a.symm.trans b).open_source.mem_nhds mem] with z hz
    exact (a.symm.trans b).left_inv hz
  have forward := (transition_smooth (k := 1) a b ha hb y ay by').differentiableAt (by decide)
  have reverse := (transition_smooth (k := 1) b a hb ha y by' ay).differentiableAt (by decide)
  have atY : (b ∘ a.symm) (a y) = b y := by simp [a.left_inv ay]
  have result := same.fderiv_eq (𝕜 := ℝ)
  rwa [fderiv_comp (a y) (atY.symm ▸ reverse) forward,atY,fderiv_id] at result

/-- The scalar second variation at the full control, restricted in both
arguments to the kernel of the full endpoint differential. -/
private def kernelRowFrom {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (D : U →L[ℝ] State) (H : U →L[ℝ] U →L[ℝ] State) (p : State →L[ℝ] ℝ) :=
  let K := LinearMap.ker D.toLinearMap
  let row := ((ContinuousLinearMap.compL ℝ U State ℝ p).comp H).toLinearMap
  let restrict : (U →L[ℝ] ℝ) →ₗ[ℝ] (K →ₗ[ℝ] ℝ) :=
    { toFun := fun f => f.toLinearMap.comp K.subtype
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  restrict.comp (row.comp K.subtype)

def kernelRowAt {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (F : U → State) (w : U) (p : State →L[ℝ] ℝ) :=
  kernelRowFrom (fderiv ℝ F w) (fderiv ℝ (fderiv ℝ F) w) p

private theorem row_on_terminal {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (F : U → State) (w : U) (I : Controls →L[ℝ] U) (ψ : State → State) (A : Controls → State)
    (k : State) (jet : WholeJet F w I ψ A k) (p : State →L[ℝ] ℝ)
    [FiniteDimensional ℝ (LinearMap.range (kernelRowAt F w p))] :
    FiniteDimensional ℝ (LinearMap.range (hessianRow A (p.comp (fderiv ℝ ψ k)))) := by
  let K := LinearMap.ker (fderiv ℝ A 0).toLinearMap
  let N := LinearMap.ker (fderiv ℝ F w).toLinearMap
  let inj : K →ₗ[ℝ] N := (I.toLinearMap.comp K.subtype).codRestrict N (fun h => by
    change fderiv ℝ F w (I h.val) = 0
    rw [jet.2.1,show fderiv ℝ A 0 h.val = 0 from h.property,map_zero])
  let H := kernelRowAt F w p
  let Q := H.rangeRestrict.comp inj
  let T := restrictedHessianRow A (p.comp (fderiv ℝ ψ k))
  have sub : LinearMap.ker Q ≤ LinearMap.ker T := by
    intro h hh
    apply LinearMap.ext
    intro l
    have eq : Q h = 0 := hh
    have hz : p (fderiv ℝ (fderiv ℝ F) w (I h.val) (I l.val)) = 0 :=
      congrArg (fun v : LinearMap.range H => v.val (inj l)) eq
    rw [jet.2.2,show fderiv ℝ A 0 h.val = 0 from h.property,map_zero,
      ContinuousLinearMap.zero_apply,add_zero] at hz
    exact hz
  letI : FiniteDimensional ℝ (LinearMap.range T) := finite_range_of_kernel Q T sub
  exact full_rank_finite_of_restricted A _

def WholeCovectors {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (F : U → State) (w : U) (ψ : State → State) (A : Controls → State) (k : State) : Prop :=
  ∀ p : State →L[ℝ] ℝ, let p' := p.comp (fderiv ℝ ψ k)
    (p ≠ 0 → p' ≠ 0) ∧ ((∀ h, p (fderiv ℝ F w h) = 0) → ∀ h, p' (fderiv ℝ A 0 h) = 0) ∧
    (FiniteDimensional ℝ (LinearMap.range (kernelRowAt F w p)) →
      FiniteDimensional ℝ (LinearMap.range (hessianRow A p')))

/-- Pulse consequences for the actual pulled columns, including equal
times on the late interval. The cutoff disappears by equality of germs. -/
def WholePulseTest {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (F : U → State) (w : U) (ψ : State → State) (e : Frame M 2)
    (P : State → C(Time,State)) (k : State) : Prop :=
  ∀ p : State →L[ℝ] ℝ, let p' := p.comp (fderiv ℝ ψ k)
    ((∀ h, p (fderiv ℝ F w h) = 0) → ∀ i (t : Time), p' (pulledField e P i t k) = 0) ∧
    (FiniteDimensional ℝ (LinearMap.range (kernelRowAt F w p)) →
      ∃ τ : ℝ, 0 ≤ τ ∧ τ < 1 ∧ ∀ i j s t, τ < s → s ≤ t → t ≤ 1 →
        p' (VectorField.lieBracket ℝ (pulledField e P i (clamp s)) (pulledField e P j (clamp t)) k) = 0)

private theorem actual_pulses {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (F : U → State) (w : U) (ψ : State → State) (A : Controls → State) (e : Frame M 2)
    (P : State → C(Time,State)) (k : State) (X : Columns State) (endA : X.Endpoint k A)
    (ca : ContDiffAt ℝ 2 A 0) (rows : WholeCovectors F w ψ A k)
    (cols : ∀ᶠ z in 𝓝 k, ∀ i t, X.Y i t z = pulledField e P i (clamp t) z) :
    WholePulseTest F w ψ e P k := by
  choose Z sol using fun i => pulse_family_exists (X.window i) k
  have graph := graph_of_integral_endpoint X k A endA Z sol
  intro p
  let p' := p.comp (fderiv ℝ ψ k)
  have col (i t) : X.Y i t =ᶠ[𝓝 k] pulledField e P i (clamp t) := cols.mono fun _ h => h i t
  constructor
  · intro annih i t
    have hz := annihilates_columns X A k p' (ca.differentiableAt (by decide))
      ((rows p).2.1 annih) Z sol graph i t t.2
    simpa only [(col i t).self_of_nhds,show clamp (t:ℝ) = t from projIcc_of_mem _ t.2] using hz
  · intro small
    letI : FiniteDimensional ℝ (LinearMap.range (hessianRow A p')) := (rows p).2.2 small
    obtain ⟨τ,hτ,h1,off⟩ := mixed_time_zero X A k p' ca Z sol graph
    refine ⟨τ,hτ,h1,?_⟩
    intro i j s t hs st ht
    let f (v : ℝ) := p' (VectorField.lieBracket ℝ (X.Y i v) (X.Y j t) k)
    have cf : Continuous f := by
      change Continuous (fun v : ℝ => p' (fderiv ℝ (X.Y j t) k (X.Y i v k) - fderiv ℝ (X.Y i v) k (X.Y j t k)))
      exact p'.continuous.comp ((((fderiv ℝ (X.Y j t) k).continuous).comp
        ((X.continuous i).comp (continuous_id.prodMk continuous_const))).sub
        (((X.jacobian i).comp (continuous_id.prodMk continuous_const)).clm_apply continuous_const))
    have onOpen : EqOn f (fun _ => 0) (Ioo τ t) := fun v hv => off i j v t hv.1 hv.2 ht
    have closed := onOpen.closure cf continuous_const
    rw [closure_Ioo (hs.trans_le st).ne] at closed
    have hz := closed (show s ∈ Icc τ t from ⟨hs.le,st⟩)
    change p' (fderiv ℝ (X.Y j t) k (X.Y i s k) - fderiv ℝ (X.Y i s) k (X.Y j t k)) = 0 at hz
    rw [(col j t).fderiv_eq (𝕜 := ℝ),(col i s).fderiv_eq (𝕜 := ℝ),
      (col j t).self_of_nhds,(col i s).self_of_nhds] at hz
    exact hz

theorem whole_moving_endpoint_germ [IsManifold 𝓘(ℝ, State) ∞ M] {n : ℕ}
    (e : Fin (n+1) → Frame M 2) (w : Fin (n+1) → Control 2) {x y : M}
    (path : Joins e w x y) (c : OpenPartialHomeomorph M State)
    (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (hy : y ∈ c.source) :
    let j := Fin.last n
    ∃ (d : ℝ) (I : Controls →L[ℝ] (Fin (n+1) → Control 2)) (k : State)
      (P : State → C(Time,State)) (X : Columns State) (A : Controls → State)
      (F : (Fin (n+1) → Control 2) → State),
      0 < d ∧ d < 1 ∧ Function.Injective I ∧
      (∀ h (i : Fin n), I h i.castSucc = 0) ∧
      (∀ h, ∀ᵐ t ∂volume.restrict (Ioc (0:ℝ) (1-d)), (w j + I h j) t = w j t) ∧
      (∀ h, ∀ᵐ t ∂volume.restrict (Ioc (1-d) 1), I h j t = d⁻¹ • h ((t-(1-d))/d)) ∧
      A 0 = k ∧ X.Endpoint k A ∧ Nonempty (SpatialJets X) ∧ ContDiffAt ℝ 2 A 0 ∧
      (∀ᶠ z in 𝓝 k, ∀ i t, X.Y i t z = pulledField (e j) P i (clamp t) z) ∧
      P k (clamp 1) = (e j).chart y ∧ F w = c y ∧ ContDiffAt ℝ 2 F w ∧
      (∀ᶠ b in 𝓝 w, F b ∈ c.target ∧ ∀ z, Joins e b x z ↔ z = c.symm (F b)) ∧
      (Singular e w x y ↔ ¬ Function.Surjective (fderiv ℝ F w)) ∧
      let ψ := fun z => c ((e j).chart.symm (P z (clamp 1)))
      WholeJet F w I ψ A k ∧ WholeCovectors F w ψ A k ∧ WholePulseTest F w ψ (e j) P k ∧
      ∃ (r : ℝ) (u : Control 2), 0 < r ∧ k ∈ Metric.ball ((e j).chart y) (r/2) ∧
        ReferenceTube (e j) ((e j).chart y) r u P ∧
        ∀ᵐ t ∂volume.restrict (Icc (0:ℝ) 1), u t = d • w j ((1-d)+d*t) := by
  let j := Fin.last n
  obtain ⟨F,fw,cf,fg,singular⟩ := path_endpoint_and_singularity e w x y path c hc hy 2 (by decide)
  obtain ⟨q,q0,q1,pieces⟩ := path
  have last : Segment (e j) (w j) (q j.castSucc) y := by simpa [j,Fin.succ_last,q1] using pieces j
  obtain ⟨d,r,u,k,P,R,X,A,hd,_,hr,hk,rep,tube,stop,hR,jets,cols,a0,endA,ca,short,_,strict,
    pre,pRep,before⟩ := terminal_moving_endpoint_germ (e j) (w j) last
  obtain ⟨J,inj,freeze,back,paste⟩ := terminal_control_injection (e j) (w j) pre u d hd strict pRep rep
  let L := J.comp R.symm.toContinuousLinearEquiv.toContinuousLinearMap
  let I := (ContinuousLinearMap.single ℝ (fun _ : Fin (n+1) => Control 2) j).comp L
  have atJ (v : Controls) : I v j = J (R.symm v) := Pi.single_eq_same _ _
  have early (v : Controls) (i : Fin n) : I v i.castSucc = 0 :=
    Pi.single_eq_of_ne (Fin.ne_last_of_lt (Fin.castSucc_lt_last i)) _
  have ii : Function.Injective I := by
    intro v b eq
    apply R.symm.injective
    apply inj
    simpa only [atJ] using congrFun eq j
  let ψ := fun z => c ((e j).chart.symm (P z (clamp 1)))
  have kc : k ∈ Metric.closedBall ((e j).chart y) r := hk.le.trans (half_le_self hr.le)
  have ev : ContDiffAt ℝ 2 (fun z => P z (clamp 1)) k :=
    (@ContinuousLinearMap.contDiff ℝ _ C(Time,State) _ _ State _ _ 2
      (ContinuousMap.evalCLM ℝ (clamp 1))).contDiffAt.comp k ((tube.regular k kc).of_le (by decide))
  have tr := transition_smooth (k := 2) (e j).chart c (e j).compatible hc y last.2.1 hy
  have cp : ContDiffAt ℝ 2 ψ k := by
    change ContDiffAt ℝ 2 ((c ∘ (e j).chart.symm) ∘ (fun z => P z (clamp 1))) k
    exact (stop.symm ▸ tr).comp k ev
  have push : Tendsto (fun v => w + I v) (𝓝 0) (𝓝 w) := by
    simpa only [map_zero,add_zero] using (continuous_const.add I.continuous).tendsto 0
  have same : (fun v => F (w+I v)) =ᶠ[𝓝 0] ψ ∘ A := by
    filter_upwards [linear_cast R.symm short,push fg] with v small full
    rw [R.apply_symm_apply] at small
    let z := (e j).chart.symm (P (A v) (clamp 1))
    have shortSeg := (small.2 z).mpr rfl
    have wholeSeg := paste _ _ _ _ before shortSeg
    have join : Joins e (w+I v) x z := by
      rw [← q0]
      apply attach_last e w q pieces
      · intro i
        simp only [Pi.add_apply,early,add_zero]
      · change Segment (e j) (w j+I v j) (q j.castSucc) z
        rwa [atJ]
    have he := congrArg c ((full.2 z).mp join)
    exact ((he.trans (c.right_inv full.1))).symm
  have whole := whole_jet_of_germ F w I ψ A k a0 ca cf cp same
  have invT := ContinuousLinearMap.IsInvertible.of_inverse
    (transition_left c (e j).chart hc (e j).compatible y hy last.2.1)
    (transition_left (e j).chart c (e j).compatible hc y last.2.1 hy)
  let E := (ContinuousMap.evalCLM ℝ (clamp 1) : C(Time,State) →L[ℝ] State)
  have de := E.hasFDerivAt.comp k ((tube.regular k kc).differentiableAt (by decide)).hasFDerivAt
  have dψ := ((stop.symm ▸ tr).differentiableAt (by decide)).hasFDerivAt.comp k de
  have inv : (fderiv ℝ ψ k).IsInvertible := by
    rw [show fderiv ℝ ψ k = _ from dψ.fderiv]
    exact (stop.symm ▸ invT).comp (tube.invertible k kc (clamp 1))
  have rows : WholeCovectors F w ψ A k := by
    intro p
    refine ⟨nonzero_pullback inv,?_,fun hp => @row_on_terminal _ _ _ F w I ψ A k whole p hp⟩
    intro annih h
    exact (congrArg p (whole.2.1 h)).symm.trans (annih (I h))
  refine ⟨d,I,k,P,X,A,F,hd,strict,ii,early,?_,?_,a0,endA,jets,ca,cols,stop,fw,cf,fg,singular,
    whole,rows,actual_pulses F w ψ A (e j) P k X endA ca rows cols,r,u,hr,hk,tube,rep⟩
  · intro h
    change ∀ᵐ t ∂volume.restrict (Ioc (0:ℝ) (1-d)), (w j + I h j) t = w j t
    simpa only [atJ] using freeze (R.symm h)
  · intro h
    change ∀ᵐ t ∂volume.restrict (Ioc (1-d) 1), I h j t = d⁻¹ • h ((t-(1-d))/d)
    have eq (s : ℝ) : (R.symm h) s = h s := by simpa only [R.apply_symm_apply] using (hR (R.symm h) s).symm
    simpa only [atJ,eq] using back (R.symm h)

#print axioms whole_moving_endpoint_germ

private theorem return_to_frame {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (F : U → State) (w : U) (e : Frame M 2) (y : M) (k : State) {r u P}
    (tube : ReferenceTube e (e.chart y) r u P) (hk : k ∈ Metric.ball (e.chart y) r)
    (stop : P k (clamp 1) = e.chart y) (θ : State → State) (ct : ContDiffAt ℝ 2 θ (e.chart y))
    (pulses : WholePulseTest F w (fun z => θ (P z (clamp 1))) e P k)
    (p : State →L[ℝ] ℝ) :
    ((∀ h, p (fderiv ℝ F w h) = 0) → ∀ i, p (fderiv ℝ θ (e.chart y) (e.X i (e.chart y))) = 0) ∧
    (FiniteDimensional ℝ (LinearMap.range (kernelRowAt F w p)) → ∀ i j,
      p (fderiv ℝ θ (e.chart y) (VectorField.lieBracket ℝ (e.X i) (e.X j) (e.chart y))) = 0) := by
  let φ := fun z => P z (clamp 1)
  let E := (ContinuousMap.evalCLM ℝ (clamp 1) : C(Time,State) →L[ℝ] State)
  have kc := Metric.ball_subset_closedBall hk
  have de (z : State) (hz : z ∈ Metric.closedBall (e.chart y) r) :
      fderiv ℝ φ z = E.comp (fderiv ℝ P z) :=
    (E.hasFDerivAt.comp z ((tube.regular z hz).differentiableAt (by decide)).hasFDerivAt).fderiv
  have inv : (fderiv ℝ φ k).IsInvertible := de k kc ▸ tube.invertible k kc (clamp 1)
  have smooth : ContDiffAt ℝ 2 φ k := (@ContinuousLinearMap.contDiff ℝ _ C(Time,State) _ _
    State _ _ 2 E).contDiffAt.comp k ((tube.regular k kc).of_le (by decide))
  have target : φ k = e.chart y := stop
  have chain := fderiv_comp k ((target.symm ▸ ct).differentiableAt (by decide)) (smooth.differentiableAt (by decide))
  have germ (i) : pulledField e P i (clamp 1) =ᶠ[𝓝 k] VectorField.pullback ℝ φ (e.X i) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hk] with z hz
    change (E.comp (fderiv ℝ P z)).inverse (e.X i (φ z)) = (fderiv ℝ φ z).inverse (e.X i (φ z))
    rw [de z (Metric.ball_subset_closedBall hz)]
  have push (V : State → State) :
      (p.comp (fderiv ℝ (θ ∘ φ) k)) (VectorField.pullback ℝ φ V k) =
      p (fderiv ℝ θ (e.chart y) (V (e.chart y))) := by
    rw [chain]
    simp only [ContinuousLinearMap.comp_apply,VectorField.fderiv_pullback φ V k inv,target]
  constructor
  · intro ann i
    have h := (pulses p).1 ann i (clamp 1)
    rw [(germ i).self_of_nhds] at h
    exact (push _).symm.trans h
  · intro finite i j
    obtain ⟨τ,_,h1,off⟩ := (pulses p).2 finite
    have h := off i j 1 1 h1 le_rfl le_rfl
    have dx (l) : DifferentiableAt ℝ (e.X l) (φ k) :=
      ((e.smooth l).contDiffAt (e.chart.open_target.mem_nhds (tube.chart k kc (clamp 1)))).differentiableAt (by simp)
    have pb := VectorField.pullback_lieBracket (by simp : minSmoothness ℝ 2 ≤ 2) smooth (dx i) (dx j)
    have gb : VectorField.lieBracket ℝ (pulledField e P i (clamp 1)) (pulledField e P j (clamp 1)) k =
      VectorField.lieBracket ℝ (VectorField.pullback ℝ φ (e.X i)) (VectorField.pullback ℝ φ (e.X j)) k := by
      change fderiv ℝ _ k _ - fderiv ℝ _ k _ = _
      rw [(germ i).fderiv_eq (𝕜 := ℝ),(germ j).fderiv_eq (𝕜 := ℝ),
        (germ i).self_of_nhds,(germ j).self_of_nhds]
      rfl
    rw [gb,← pb] at h
    exact (push _).symm.trans h

theorem same_kernel_rank {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    {G F : U → State} {w : U} (same : G =ᶠ[𝓝 w] F) (p : State →L[ℝ] ℝ) :
    FiniteDimensional ℝ (LinearMap.range (kernelRowAt G w p)) →
      FiniteDimensional ℝ (LinearMap.range (kernelRowAt F w p)) :=
  (congrArg₂ (fun (D : U →L[ℝ] State) (H : U →L[ℝ] U →L[ℝ] State) =>
    FiniteDimensional ℝ (LinearMap.range (kernelRowFrom D H p)))
    (same.fderiv_eq (𝕜 := ℝ)) ((same.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ))).mp

set_option maxHeartbeats 600000 in
/-- A covector of any genuine full endpoint representative annihilates
the terminal horizontals if it annihilates the full first derivative.
Finite rank of its Hessian on the full kernel forces it to annihilate
the terminal brackets of length two in the chosen endpoint chart. -/
theorem whole_terminal_bracket [IsManifold 𝓘(ℝ, State) ∞ M] {n : ℕ}
    (e : Fin (n+1) → Frame M 2) (w : Fin (n+1) → Control 2) {x y : M}
    (path : Joins e w x y) (c : OpenPartialHomeomorph M State)
    (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (hy : y ∈ c.source)
    (G : (Fin (n+1) → Control 2) → State)
    (graph : ∀ᶠ b in 𝓝 w, G b ∈ c.target ∧ ∀ z, Joins e b x z ↔ z = c.symm (G b))
    (p : State →L[ℝ] ℝ) :
    let f := e (Fin.last n)
    let l := p.comp (fderiv ℝ (c ∘ f.chart.symm) (f.chart y))
    ((∀ h, p (fderiv ℝ G w h) = 0) → ∀ i, l (f.X i (f.chart y)) = 0) ∧
    (FiniteDimensional ℝ (LinearMap.range (kernelRowAt G w p)) → ∀ i j,
      l (VectorField.lieBracket ℝ (f.X i) (f.X j) (f.chart y)) = 0) := by
  obtain ⟨_,_,k,P,_,_,F,_,_,_,_,_,_,_,_,_,_,_,stop,_,_,full,_,_,_,pulses,r,u,hr,hk,tube,_⟩ :=
    whole_moving_endpoint_germ e w path c hc hy
  have same : G =ᶠ[𝓝 w] F := by
    filter_upwards [graph,full] with b gb fb
    have h := (fb.2 _).mp ((gb.2 _).mpr rfl)
    exact (c.right_inv gb.1).symm.trans ((congrArg c h).trans (c.right_inv fb.1))
  let f := e (Fin.last n)
  obtain ⟨q,_,qy,parts⟩ := path
  have ys : y ∈ f.chart.source := by simpa [f,Fin.succ_last,qy] using (parts (Fin.last n)).2.1
  have ct := transition_smooth (k := 2) f.chart c f.compatible hc y ys hy
  have h := return_to_frame F w f y k tube (hk.trans (half_lt_self hr)) stop _ ct pulses p
  have d1 := same.fderiv_eq (𝕜 := ℝ)
  constructor
  · intro ann
    exact h.1 (fun v => (congrArg (fun D : (Fin (n+1) → Control 2) →L[ℝ] State => p (D v)) d1).symm.trans (ann v))
  · intro sm
    exact h.2 (same_kernel_rank same p sm)

#print axioms whole_terminal_bracket
end MinimizingSard.Five
