import WholeTerminalVariation
import LiftedReferenceJets
import MixedTimeJets

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open scoped Manifold ContDiff
open IsManifold
namespace MinimizingSard.Five
open Volterra PulseGeometry

def IdleTail (v : ℝ → Fiber 2) : Prop :=
  ∃ a ∈ Ico (0:ℝ) 1, ∀ᵐ s ∂volume.restrict (Ioo a 1), v s = 0

theorem first_idle_time (w : Control 2) (quiet : IdleTail w) :
    ∃ a ∈ Ico (0:ℝ) 1, (∀ᵐ s ∂volume.restrict (Ioo a 1), w s = 0) ∧
      ∀ b ∈ Ico (0:ℝ) a, ¬ ∀ᵐ s ∂volume.restrict (Ioo b a), w s = 0 := by
  let T := fun b : ℝ => ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ioo b 1 → w s = 0
  let S := {b : ℝ | b ∈ Icc 0 1 ∧ T b}
  obtain ⟨d,hd,tail⟩ := quiet
  have dm : d ∈ S := ⟨⟨hd.1,hd.2.le⟩,(ae_restrict_iff' measurableSet_Ioo).mp tail⟩
  have ne : S.Nonempty := ⟨d,dm⟩
  have lb : (0 : ℝ) ∈ lowerBounds S := fun _ h => h.1.1
  have inf0 := le_csInf ne lb
  have inf1 := (csInf_le ⟨0,lb⟩ dm).trans_lt hd.2
  have rat (r : ℚ) : ∀ᵐ s ∂(volume : Measure ℝ), sInf S < r → s ∈ Ioo (r:ℝ) 1 → w s = 0 := by
    by_cases hr : sInf S < r
    · obtain ⟨b,hb,hbr⟩ := exists_lt_of_csInf_lt ne hr
      filter_upwards [hb.2] with s hs
      exact fun _ hm => hs ⟨hbr.trans hm.1,hm.2⟩
    · exact Filter.Eventually.of_forall (fun _ h => (hr h).elim)
  have last : T (sInf S) := by
    filter_upwards [ae_all_iff.mpr rat] with s hs
    intro h
    obtain ⟨r,hr,hrs⟩ := exists_rat_btwn h.1
    exact hs r hr ⟨hrs,h.2⟩
  refine ⟨sInf S,⟨inf0,inf1⟩,(ae_restrict_iff' measurableSet_Ioo).mpr last,?_⟩
  intro b hb silent
  have joined : T b := by
    have ignore : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ sInf S := by
      apply ae_iff.mpr
      simpa only [not_not] using (measure_singleton (μ := (volume : Measure ℝ)) (sInf S))
    filter_upwards [last,(ae_restrict_iff' measurableSet_Ioo).mp silent,ignore] with s right left hn
    intro hi
    rcases lt_or_gt_of_ne hn with h | h
    · exact left ⟨hi.1,h⟩
    · exact right ⟨h,hi.2⟩
  exact (not_lt_of_ge (csInf_le ⟨0,lb⟩ (show b ∈ S from ⟨⟨hb.1,hb.2.le.trans inf1.le⟩,joined⟩))) hb.2

private theorem idle_original {d : ℝ} (hd : 0 < d) (h1 : d < 1) (u w : Control 2)
    (rep : ∀ᵐ s ∂volume.restrict (Icc (0:ℝ) 1), u s = d • w ((1-d)+d*s))
    (quiet : IdleTail u) : IdleTail w := by
  obtain ⟨c,hc,off⟩ := quiet
  let a := 1-d
  let g := fun t : ℝ => (t-a)/d
  have back : Measure.QuasiMeasurePreserving g (volume : Measure ℝ) volume := by
    simpa only [g,div_eq_inv_mul,sub_eq_add_neg,add_comm,Function.comp_def,smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) (inv_ne_zero hd.ne')).comp
        (measurePreserving_add_left volume (-a)).quasiMeasurePreserving
  have aa : a + d = 1 := by dsimp [a]; ring
  have restrictMap := back.restrict (s := Ioo (a+d*c) 1) (t := Ioo c 1) (by
    intro s hs
    exact ⟨(lt_div_iff₀ hd).mpr (by linarith [hs.1,mul_comm c d]),
      (div_lt_one hd).mpr (by linarith [hs.2])⟩)
  have sub : Ioo c 1 ⊆ Icc (0:ℝ) 1 := fun s hs => ⟨hc.1.trans hs.1.le,hs.2.le⟩
  refine ⟨a+d*c,⟨add_nonneg (sub_nonneg.mpr h1.le) (mul_nonneg hd.le hc.1),
    by linarith [mul_lt_mul_of_pos_left hc.2 hd]⟩,?_⟩
  filter_upwards [restrictMap.ae off,restrictMap.ae (ae_restrict_of_ae_restrict_of_subset sub rep)] with s zero eq
  change u (g s) = 0 at zero
  change u (g s) = d • w (a+d*g s) at eq
  rw [show a+d*g s = s by dsimp [g]; field_simp; ring,zero] at eq
  exact (smul_eq_zero.mp eq.symm).resolve_left hd.ne'

private theorem terminal_transfer {M : Type*} [TopologicalSpace M] [ChartedSpace State M]
    (e : Frame M 2) {q r u P} (tube : ReferenceTube e q r u P) {k : State}
    (hk : k ∈ Metric.ball q r) (θ : State → State) (ct : ContDiffAt ℝ 2 θ (P k (clamp 1)))
    (p : State →L[ℝ] ℝ) {τ : ℝ} (hτ : 0 ≤ τ) (hlt : τ < 1)
    (mixed : let p' := p.comp (fderiv ℝ (fun x => θ (P x (clamp 1))) k)
      ∀ i j s t, τ < s → s ≤ t → t ≤ 1 →
        p' (VectorField.lieBracket ℝ (pulledField e P i (clamp s)) (pulledField e P j (clamp t)) k) = 0)
    (active : ¬ IdleTail u) :
    ∀ i, let y := P k (clamp 1)
      p (fderiv ℝ θ y (VectorField.lieBracket ℝ (e.X i) (VectorField.lieBracket ℝ (e.X 0) (e.X 1)) y)) = 0 := by
  let φ := fun (s : ℝ) x => P x (clamp s)
  let Y := fun (i : Fin 2) (s : ℝ) => pulledField e P i (clamp s)
  let X := VectorField.lieBracket ℝ (e.X 0) (e.X 1)
  let B := fun s => VectorField.pullback ℝ (φ s) X
  let p' := p.comp (fderiv ℝ (θ ∘ φ 1) k)
  have kc := Metric.ball_subset_closedBall hk
  have dφ (x : State) (hx : x ∈ Metric.closedBall q r) :
      fderiv ℝ (φ 1) x = (ContinuousMap.evalCLM ℝ (clamp 1)).comp (fderiv ℝ P x) :=
    ((ContinuousMap.evalCLM ℝ (clamp 1) : C(Time,State) →L[ℝ] State).hasFDerivAt.comp x
      ((tube.regular _ hx).differentiableAt (by decide)).hasFDerivAt).fderiv
  have inv : (fderiv ℝ (φ 1) k).IsInvertible := dφ k kc ▸ tube.invertible k kc _
  have sm : ContDiffAt ℝ 2 (φ 1) k :=
    (@ContinuousLinearMap.contDiff ℝ _ C(Time,State) _ _ State _ _ 2
      (ContinuousMap.evalCLM ℝ (clamp 1))).contDiffAt.comp k ((tube.regular k kc).of_le (by decide))
  have chain := fderiv_comp k (ct.differentiableAt (by decide)) (sm.differentiableAt (by decide))
  have sx (i) : ContDiffAt ℝ 2 (e.X i) (φ 1 k) :=
    ((e.smooth i).contDiffAt (e.chart.open_target.mem_nhds (tube.chart k kc _))).of_le (by decide)
  have sb : ContDiffAt ℝ 1 X (φ 1 k) := (sx 0).lieBracket_vectorField (sx 1) (by decide)
  intro i
  have row (s : ℝ) (hs : s ∈ Ioo τ 1) (j : Fin 2) :
      p' (VectorField.lieBracket ℝ (Y i 1) (Y j s) k) = 0 := by
    rw [VectorField.lieBracket_swap,map_neg,neg_eq_zero]
    exact mixed j i s 1 hs.1 hs.2.le le_rfl
  have test := MixedTime.terminal_bracket_or_idle p' k (Y 0) (Y 1) B (Y i 1)
    (fun t => u t 0) (fun t => u t 1) hlt (reference_bracket_jet_continuous e tube hk).continuousAt
    (fun s hs => ⟨row s hs 0,row s hs 1⟩)
    (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_left hτ) (reference_signed_jet_time e tube hk))
  have vanish := test.resolve_right (by
    rintro ⟨c,hc,quiet⟩
    apply active
    refine ⟨c,⟨hτ.trans hc.1,hc.2⟩,?_⟩
    filter_upwards [quiet] with s hs
    funext j
    fin_cases j <;> first | exact hs.1 | exact hs.2)
  have agree : Y i 1 =ᶠ[𝓝 k] VectorField.pullback ℝ (φ 1) (e.X i) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hk] with x hx
    change _ = (fderiv ℝ (φ 1) x).inverse _
    rw [dφ x (Metric.ball_subset_closedBall hx)]
    rfl
  have natural := VectorField.pullback_lieBracket (by simp : minSmoothness ℝ 2 ≤ 2) sm
    ((sx i).differentiableAt (by decide)) (sb.differentiableAt (by decide))
  have br : VectorField.lieBracket ℝ (Y i 1) (B 1) k =
      VectorField.pullback ℝ (φ 1) (VectorField.lieBracket ℝ (e.X i) X) k := by
    rw [natural]
    change fderiv ℝ _ k _ - fderiv ℝ _ k _ = _
    rw [agree.self_of_nhds,agree.fderiv_eq (𝕜 := ℝ)]
    rfl
  change p' (VectorField.lieBracket ℝ (Y i 1) (B 1) k) = 0 at vanish
  rw [br] at vanish
  simpa only [p',chain,ContinuousLinearMap.comp_apply,VectorField.fderiv_pullback _ _ k inv] using vanish

/-- A finite-rank row on the actual kernel at the original control kills
both terminal triple brackets, or the last original control vanishes a.e.
on an entire final interval. The statement imposes no speed condition. -/
theorem whole_terminal_triples_or_idle {M : Type*} [TopologicalSpace M] [ChartedSpace State M]
    [IsManifold 𝓘(ℝ, State) ∞ M] {n : ℕ}
    (e : Fin (n+1) → Frame M 2) (w : Fin (n+1) → Control 2) {x y : M}
    (path : Joins e w x y) (c : OpenPartialHomeomorph M State)
    (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (hy : y ∈ c.source)
    (G : (Fin (n+1) → Control 2) → State)
    (graph : ∀ᶠ b in 𝓝 w, G b ∈ c.target ∧ ∀ z, Joins e b x z ↔ z = c.symm (G b))
    (p : State →L[ℝ] ℝ) (rank : FiniteDimensional ℝ (LinearMap.range (kernelRowAt G w p))) :
    let j := Fin.last n
    let f := e j
    let z := f.chart y
    let l := p.comp (fderiv ℝ (c ∘ f.chart.symm) z)
    (∀ i, l (VectorField.lieBracket ℝ (f.X i) (VectorField.lieBracket ℝ (f.X 0) (f.X 1)) z) = 0) ∨
    ∃ a ∈ Ico (0:ℝ) 1, (∀ᵐ s ∂volume.restrict (Ioo a 1), w j s = 0) ∧
      ∀ b ∈ Ico (0:ℝ) a, ¬ ∀ᵐ s ∂volume.restrict (Ioo b a), w j s = 0 := by
  let j := Fin.last n
  let f := e j
  by_cases quiet : IdleTail (w j)
  · exact Or.inr (first_idle_time _ quiet)
  apply Or.inl
  obtain ⟨d,_,k,P,_,_,F,hd,h1,_,_,_,_,_,_,_,_,_,stop,_,_,full,_,_,_,pulses,r,u,hr,hk,tube,rep⟩ :=
    whole_moving_endpoint_germ e w path c hc hy
  have same : G =ᶠ[𝓝 w] F := by
    filter_upwards [graph,full] with b gb fb
    have h := (fb.2 _).mp ((gb.2 _).mpr rfl)
    exact (c.right_inv gb.1).symm.trans ((congrArg c h).trans (c.right_inv fb.1))
  obtain ⟨τ,hτ,hτ1,mixed⟩ := (pulses p).2 (same_kernel_rank same p rank)
  obtain ⟨nodes,_,endNode,pieces⟩ := path
  have ys : y ∈ f.chart.source := by simpa [j,f,Fin.succ_last,endNode] using (pieces j).2.1
  have ct := transition_smooth (k := 2) f.chart c f.compatible hc y ys hy
  have out := terminal_transfer f tube (hk.trans (half_lt_self hr)) (c ∘ f.chart.symm)
    (stop.symm ▸ ct) p hτ hτ1 mixed (fun hu => quiet (idle_original hd h1 u (w j) rep hu))
  simpa only [stop] using out

#print axioms whole_terminal_triples_or_idle
private theorem terminal_value_transfer {M : Type*} [TopologicalSpace M] [ChartedSpace State M]
    (e : Frame M 2) {q r u P} (tube : ReferenceTube e q r u P) {k : State}
    (hk : k ∈ Metric.ball q r) (θ : State → State) (ct : ContDiffAt ℝ 2 θ (P k (clamp 1)))
    (p : State →L[ℝ] ℝ)
    (columns : let p' := p.comp (fderiv ℝ (fun x => θ (P x (clamp 1))) k)
      ∀ i (t : Time), p' (pulledField e P i t k) = 0)
    (active : ¬ IdleTail u) :
    let y := P k (clamp 1)
    p (fderiv ℝ θ y (VectorField.lieBracket ℝ (e.X 0) (e.X 1) y)) = 0 := by
  let φ := fun (s : ℝ) x => P x (clamp s)
  let Y := fun (i : Fin 2) (s : ℝ) => pulledField e P i (clamp s)
  let X := VectorField.lieBracket ℝ (e.X 0) (e.X 1)
  let B := fun s => VectorField.pullback ℝ (φ s) X
  let p' := p.comp (fderiv ℝ (θ ∘ φ 1) k)
  have kc := Metric.ball_subset_closedBall hk
  have dφ (x : State) (hx : x ∈ Metric.closedBall q r) :
      fderiv ℝ (φ 1) x = (ContinuousMap.evalCLM ℝ (clamp 1)).comp (fderiv ℝ P x) :=
    ((ContinuousMap.evalCLM ℝ (clamp 1) : C(Time,State) →L[ℝ] State).hasFDerivAt.comp x
      ((tube.regular _ hx).differentiableAt (by decide)).hasFDerivAt).fderiv
  have inv : (fderiv ℝ (φ 1) k).IsInvertible := dφ k kc ▸ tube.invertible k kc _
  have sm : ContDiffAt ℝ 2 (φ 1) k :=
    (@ContinuousLinearMap.contDiff ℝ _ C(Time,State) _ _ State _ _ 2
      (ContinuousMap.evalCLM ℝ (clamp 1))).contDiffAt.comp k ((tube.regular k kc).of_le (by decide))
  have chain := fderiv_comp k (ct.differentiableAt (by decide)) (sm.differentiableAt (by decide))
  let L := p'.comp (ContinuousLinearMap.fst ℝ State (State →L[ℝ] State))
  have paired (s : ℝ) (_hs : s ∈ Ioo (0:ℝ) 1) :
      L (MixedTime.jet (Y 0 s) k) = 0 ∧ L (MixedTime.jet (Y 1 s) k) = 0 :=
    ⟨columns 0 (clamp s),columns 1 (clamp s)⟩
  have test := MixedTime.column_row_or_idle L (fun t => MixedTime.jet (Y 0 t) k)
    (fun t => MixedTime.jet (Y 1 t) k) (fun t => MixedTime.jet (B t) k)
    (fun t => u t 0) (fun t => u t 1) zero_lt_one (reference_bracket_jet_continuous e tube hk).continuousAt
    paired (reference_signed_jet_time e tube hk)
  have vanish := test.resolve_right (by
    rintro ⟨a,ha,h⟩
    apply active
    refine ⟨a,ha,?_⟩
    filter_upwards [h] with s hs
    funext j
    fin_cases j <;> first | exact hs.1 | exact hs.2)
  change p' (VectorField.pullback ℝ (φ 1) X k) = 0 at vanish
  simpa only [p',chain,ContinuousLinearMap.comp_apply,VectorField.fderiv_pullback _ _ k inv] using vanish

/-- An annihilator of the endpoint derivative annihilates the simple terminal
bracket unless the last control has an idle interval. -/
theorem whole_active_bracket_or_idle {M : Type*} [TopologicalSpace M] [ChartedSpace State M]
    [IsManifold 𝓘(ℝ, State) ∞ M] {n : ℕ}
    (e : Fin (n+1) → Frame M 2) (w : Fin (n+1) → Control 2) {x y : M}
    (path : Joins e w x y) (c : OpenPartialHomeomorph M State)
    (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (hy : y ∈ c.source)
    (G : (Fin (n+1) → Control 2) → State)
    (graph : ∀ᶠ b in 𝓝 w, G b ∈ c.target ∧ ∀ z, Joins e b x z ↔ z = c.symm (G b))
    (p : State →L[ℝ] ℝ) (ann : ∀ h, p (fderiv ℝ G w h) = 0) :
    let j := Fin.last n
    let f := e j
    let z := f.chart y
    let l := p.comp (fderiv ℝ (c ∘ f.chart.symm) z)
    l (VectorField.lieBracket ℝ (f.X 0) (f.X 1) z) = 0 ∨
    ∃ a ∈ Ico (0:ℝ) 1, (∀ᵐ s ∂volume.restrict (Ioo a 1), w j s = 0) ∧
      ∀ b ∈ Ico (0:ℝ) a, ¬ ∀ᵐ s ∂volume.restrict (Ioo b a), w j s = 0 := by
  let j := Fin.last n
  let f := e j
  by_cases quiet : IdleTail (w j)
  · exact Or.inr (first_idle_time _ quiet)
  apply Or.inl
  obtain ⟨d,_,k,P,_,_,F,hd,h1,_,_,_,_,_,_,_,_,_,stop,_,_,full,_,_,_,pulses,r,u,hr,hk,tube,rep⟩ :=
    whole_moving_endpoint_germ e w path c hc hy
  have same : G =ᶠ[𝓝 w] F := by
    filter_upwards [graph,full] with b gb fb
    have h := (fb.2 _).mp ((gb.2 _).mpr rfl)
    exact (c.right_inv gb.1).symm.trans ((congrArg c h).trans (c.right_inv fb.1))
  have columns := (pulses p).1 (fun h => by rw [← same.fderiv_eq]; exact ann h)
  obtain ⟨nodes,_,endNode,pieces⟩ := path
  have ys : y ∈ f.chart.source := by simpa [j,f,Fin.succ_last,endNode] using (pieces j).2.1
  have ct := transition_smooth (k := 2) f.chart c f.compatible hc y ys hy
  have out := terminal_value_transfer f tube (hk.trans (half_lt_self hr)) (c ∘ f.chart.symm)
    (stop.symm ▸ ct) p columns (fun hu => quiet (idle_original hd h1 u (w j) rep hu))
  simpa only [stop] using out

#print axioms whole_active_bracket_or_idle

end MinimizingSard.Five
