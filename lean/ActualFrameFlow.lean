import BracketGrowth
import L2MovingEndpoint

/-! Smooth control dependence and confinement for the chart ODE
specified by the original rank-two frame. -/
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff
namespace MinimizingSard.Five
open Volterra PulseGeometry

private def castLp {μ ν : Measure ℝ} (h : μ = ν) : Lp (Fiber 2) 2 μ ≃ₗᵢ[ℝ] Lp (Fiber 2) 2 ν := by
  subst ν
  exact LinearIsometryEquiv.refl _ _

private theorem castLp_apply {μ ν : Measure ℝ} (h : μ = ν) (u : Lp (Fiber 2) 2 μ) (t : ℝ) :
    (castLp h u) t = u t := by subst ν; rfl

private theorem interval_measure_eq : volume.restrict (Icc (0:ℝ) 1) = Causal.timeMeasure :=
  Measure.restrict_congr_set Ioo_ae_eq_Icc.symm

private def castPair {μ ν : Measure ℝ} (h : μ = ν) :
    {L : Lp (Fiber 2) 2 μ ≃ₗᵢ[ℝ] Lp (Fiber 2) 2 ν // ∀ (u : Lp (Fiber 2) 2 μ) (t : ℝ), (L u) t = u t} :=
  ⟨castLp h,castLp_apply h⟩

private opaque signalPair : {L : Control 2 ≃ₗᵢ[ℝ] Controls // ∀ (u : Control 2) (t : ℝ), (L u) t = u t} :=
  castPair interval_measure_eq

private abbrev signal : Control 2 ≃ₗᵢ[ℝ] Controls := signalPair.val

private theorem signal_apply (u : Control 2) (t : ℝ) : (signal u) t = u t := signalPair.property u t

/-- The original frame input and the Volterra input differ only by the
choice of endpoints of a Lebesgue interval. -/
theorem control_signal_equiv : ∃ R : Control 2 ≃ₗᵢ[ℝ] Controls,
    ∀ (u : Control 2) (t : ℝ), (R u) t = u t := ⟨signal,signal_apply⟩

#print axioms control_signal_equiv

private def autoField {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : State → E) (hf : ContDiff ℝ ∞ f) : C(Time × State,E) :=
  ⟨fun p => f p.2,hf.continuous.comp continuous_snd⟩

private theorem auto_order (n : ℕ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : State → E) (hf : ContDiff ℝ ∞ f) : PathCalculus.SpatialOrder n (autoField f hf) := by
  induction n generalizing E with
  | zero => trivial
  | succ n ih =>
    have d : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
    exact ⟨autoField _ d,fun _ x => (hf.differentiable (by simp) x).hasFDerivAt,ih _ d⟩

private def autonomous (Y : Fin 2 → State → State) (hY : ∀ i, ContDiff ℝ ∞ (Y i)) : Columns State where
  Y i _ := Y i
  continuous i := (hY i).continuous.comp continuous_snd
  differentiable i _ _ := (hY i).differentiable (by simp)
  jacobian i := ((hY i).continuous_fderiv (by simp)).comp continuous_snd

variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M]

private def frameMap (e : Frame M 2) (z : State) : Fiber 2 →L[ℝ] State :=
  ∑ i : Fin 2, (ContinuousLinearMap.smulRightL ℝ (Fiber 2) State (ContinuousLinearMap.proj i)) (e.X i z)

private theorem frameMap_apply (e : Frame M 2) (z : State) (v : Fiber 2) :
    frameMap e z v = e.velocity z v := by
  simp only [frameMap,Frame.velocity,Fin.sum_univ_two,ContinuousLinearMap.add_apply]; rfl

private theorem frameMap_continuous (e : Frame M 2) : ContinuousOn (frameMap e) e.chart.target := by
  apply continuousOn_finset_sum
  intro i _
  exact (ContinuousLinearMap.smulRightL ℝ (Fiber 2) State (ContinuousLinearMap.proj i)).continuous.comp_continuousOn (e.smooth i).continuousOn

/-- Every chart trajectory with small control and nearby initial point
stays in the specified neighborhood. This quantifies over all solutions. -/
theorem small_frame_paths_stay (e : Frame M 2) {q : State} (hq : q ∈ e.chart.target)
    {V : Set State} (hV : V ∈ 𝓝 q) :
    ∀ᶠ p : State × Control 2 in 𝓝 0, ∀ z : ℝ → State,
      ContinuousOn z (Icc 0 1) → MapsTo z (Icc 0 1) e.chart.target →
      (∀ t ∈ Icc (0:ℝ) 1, z t = (q+p.1) + ∫ s in (0:ℝ)..t, e.velocity (z s) (p.2 s)) →
      MapsTo z (Icc 0 1) V := by
  let L := ‖frameMap e q‖+1
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have near : ∀ᶠ x in 𝓝 q, ‖frameMap e x‖ < L :=
    ((frameMap_continuous e q hq).continuousAt (e.chart.open_target.mem_nhds hq)).norm.eventually_lt
      continuousAt_const (by dsimp [L]; linarith)
  obtain ⟨R,hR,ball⟩ := Metric.mem_nhds_iff.mp (inter_mem hV near)
  have tiny : ∀ᶠ p : State × Control 2 in 𝓝 0, ‖p.1‖ + L*‖p.2‖ < R/2 :=
    (continuous_fst.norm.add (continuous_const.mul continuous_snd.norm)).continuousAt.eventually_lt
      continuousAt_const (by simpa using half_pos hR)
  filter_upwards [tiny] with p hp
  intro z cz mz eq t ht
  let w : C(Time,State) := ⟨fun s => z s-q,
    (continuousOn_iff_continuous_restrict.mp cz).sub continuous_const⟩
  let A : C(Time,Fiber 2 →L[ℝ] State) := ⟨fun s => frameMap e (z s),
    continuousOn_iff_continuous_restrict.mp ((frameMap_continuous e).comp cz mz)⟩
  have ident (s : Time) : w s = p.1 + primitive A (signal p.2) s := by
    change z s-q = p.1 + operator (Fiber 2) State A (signal p.2) s
    rw [operator_eq_interval,eq s s.2]
    have val : (∫ r in (0:ℝ)..(s:ℝ), A (clamp r) (signal p.2 r)) =
        ∫ r in (0:ℝ)..(s:ℝ), e.velocity (z r) (p.2 r) := by
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le s.2.1] at hr
      have H : r ∈ Icc (0:ℝ) 1 := ⟨hr.1,hr.2.trans s.2.2⟩
      change A (clamp r) (signal p.2 r) = e.velocity (z r) (p.2 r)
      rw [show clamp r = ⟨r,H⟩ from projIcc_of_mem _ H,signal_apply]
      exact frameMap_apply _ _ _
    rw [val]; abel
  have trapped := path_stays_in_ball w p.1 A (signal p.2) hL ident (R := R/2)
    (fun s hs => (ball (show dist (z s) q < R by
      rw [dist_eq_norm]; exact hs.trans_lt (half_lt_self hR))).2.le)
    (by simpa only [LinearIsometryEquiv.norm_map] using hp)
  apply (ball _).1
  rw [mem_ball,dist_eq_norm]
  exact ((w.norm_coe_le_norm ⟨t,ht⟩).trans_lt trapped).trans (half_lt_self hR)

#print axioms small_frame_paths_stay

private def chartPath (e : Frame M 2) (a : State) (u : Control 2) (z : ℝ → State) : Prop :=
  ContinuousOn z (Icc 0 1) ∧
  IntervalIntegrable (fun s => e.velocity (z s) (u s)) volume 0 1 ∧
  ∀ t ∈ Icc (0:ℝ) 1, z t = a + ∫ s in (0:ℝ)..t, e.velocity (z s) (u s)

private theorem chartPath_iff (e : Frame M 2) (X : Columns State) (a : State) (u : Control 2)
    (z : ℝ → State) (agree : ∀ t ∈ Icc (0:ℝ) 1, ∀ v, X.velocity t (z t) v = e.velocity (z t) v) :
    X.Path a (signal u) z ↔ chartPath e a u z := by
  have same (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      X.velocity s (z s) (signal u s) = e.velocity (z s) (u s) := by
    rw [signal_apply,agree _ hs]
  have integ := intervalIntegrable_congr (μ := volume) (a := (0:ℝ)) (b := 1)
    (f := fun s => X.velocity s (z s) (signal u s)) (g := fun s => e.velocity (z s) (u s))
    (fun s hs => same s (by rw [uIoc_of_le zero_le_one] at hs; exact ⟨hs.1.le,hs.2⟩))
  have intEq (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      (∫ s in (0:ℝ)..t, X.velocity s (z s) (signal u s)) =
      ∫ s in (0:ℝ)..t, e.velocity (z s) (u s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    exact same s ⟨hs.1,hs.2.trans ht.2⟩
  constructor
  · rintro ⟨hz,hi,he⟩
    exact ⟨hz,integ.mp hi,fun t ht => (he t ht).trans (congrArg (a+ ·) (intEq t ht))⟩
  · rintro ⟨hz,hi,he⟩
    exact ⟨hz,integ.mpr hi,fun t ht => (he t ht).trans (congrArg (a+ ·) (intEq t ht).symm)⟩

private theorem graph_of_trapped (e : Frame M 2) (X : Columns State) (a : State) (u : Control 2)
    (V : Set State) (inChart : V ⊆ e.chart.target) (hi : a ∈ e.chart.target) (z : ℝ → State)
    (zv : ∀ t, z t ∈ V) (agree : ∀ x ∈ V, ∀ t v, X.velocity t x v = e.velocity x v)
    (model : X.Path a (signal u) z) (unique : ∀ z', X.Path a (signal u) z' → z' 1 = z 1)
    (trap : ∀ z', ContinuousOn z' (Icc 0 1) → MapsTo z' (Icc 0 1) e.chart.target →
      (∀ t ∈ Icc (0:ℝ) 1, z' t = a + ∫ s in (0:ℝ)..t, e.velocity (z' s) (u s)) →
      MapsTo z' (Icc 0 1) V) :
    ∀ y, Segment e u (e.chart.symm a) y ↔ y = e.chart.symm (z 1) := by
  have hz := (chartPath_iff e X a u z (fun t _ => agree (z t) (zv t) t)).mp model
  have zz : z 0 = a := by simpa using hz.2.2 0 (by norm_num)
  intro y
  constructor
  · rintro ⟨_,hy,z',cz,mz,start,stop,integ,eq⟩
    rw [e.chart.right_inv hi] at start
    have he (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) := (eq t ht).trans (congrArg (· + _) start)
    have localZ := trap z' cz mz he
    have path := (chartPath_iff e X _ u z' (fun t ht => agree _ (localZ ht) t)).mpr ⟨cz,integ,he⟩
    rw [← unique z' path,stop,e.chart.left_inv hy]
  · rintro rfl
    refine ⟨e.chart.map_target hi,e.chart.map_target (inChart (zv 1)),z,hz.1,fun t _ => inChart (zv t),
      zz.trans (e.chart.right_inv hi).symm,(e.chart.right_inv (inChart (zv 1))).symm,hz.2.1,?_⟩
    intro t ht
    rw [zz]; exact hz.2.2 t ht

private theorem change_family {A U W B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup B] [NormedSpace ℝ B] (L : U →L[ℝ] W) (n : ℕ) (R : A → W → B → Prop)
    (data : ∃ S : A × W → B, S 0 = 0 ∧ ContDiffAt ℝ n S 0 ∧ ∀ᶠ p in 𝓝 0, R p.1 p.2 (S p)) :
    ∃ T : A × U → B, T 0 = 0 ∧ ContDiffAt ℝ n T 0 ∧ ∀ᶠ p in 𝓝 0, R p.1 (L p.2) (T p) := by
  obtain ⟨S,s0,cs,paths⟩ := data
  let J := (ContinuousLinearMap.fst ℝ A U).prod (L.comp (ContinuousLinearMap.snd ℝ A U))
  have zJ : J 0 = 0 := J.map_zero
  have cj : ContDiffAt ℝ n S (J 0) := by rw [zJ]; exact cs
  refine ⟨S ∘ J,?_,cj.comp 0 J.contDiff.contDiffAt,?_⟩
  · change S (J 0) = 0
    rw [zJ,s0]
  · have c : Tendsto J (𝓝 0) (𝓝 0) := zJ ▸ J.continuous.tendsto 0
    exact c paths

private theorem original_path_family (X : Columns State) (n : ℕ) (hn : 1 ≤ (n : WithTop ℕ∞))
    (jets : ∀ i, PathCalculus.SpatialOrder n (X.spatialField i)) (q : State) :
    ∃ T : State × Control 2 → C(Time,State), T 0 = 0 ∧ ContDiffAt ℝ n T 0 ∧
      ∀ᶠ p in 𝓝 0, X.Path (q+p.1) (signal p.2) (fun t => q+T p (clamp t)) ∧
        ∀ z, X.Path (q+p.1) (signal p.2) z → ∀ t : Time, z t = q+T p t := by
  let R (a : State) (u : Controls) (w : C(Time,State)) :=
    X.Path (q+a) u (fun t => q+w (clamp t)) ∧ ∀ z, X.Path (q+a) u z → ∀ t : Time, z t = q+w t
  exact change_family signal.toContinuousLinearEquiv.toContinuousLinearMap n R (joint_path_family X n hn jets q)

private theorem endpoint_of_columns (e : Frame M 2) {q : State} (hq : q ∈ e.chart.target)
    (n : ℕ) (hn : 1 ≤ (n : WithTop ℕ∞)) (X : Columns State)
    (jets : ∀ i, PathCalculus.SpatialOrder n (X.spatialField i)) (V : Set State) (nearV : V ∈ 𝓝 q)
    (inChart : V ⊆ e.chart.target) (agree : ∀ x ∈ V, ∀ t v, X.velocity t x v = e.velocity x v) :
    ∃ F : State × Control 2 → State, F 0 = q ∧ ContDiffAt ℝ n F 0 ∧
      ∀ᶠ p in 𝓝 0, q+p.1 ∈ e.chart.target ∧ F p ∈ e.chart.target ∧
        ∀ y, Segment e p.2 (e.chart.symm (q+p.1)) y ↔ y = e.chart.symm (F p) := by
  obtain ⟨T,t0,cj,run⟩ := original_path_family X n hn jets q
  let F (p : State × Control 2) := q+T p (clamp 1)
  have f0 : F 0 = q := by simp [F,t0]
  have cf : ContDiffAt ℝ n F 0 := contDiffAt_const.add
    ((@ContinuousLinearMap.contDiff ℝ _ C(Time,State) _ _ State _ _ n
      (ContinuousMap.evalCLM ℝ (clamp 1))).contDiffAt.comp 0 cj)
  obtain ⟨R,hR,ball⟩ := Metric.mem_nhds_iff.mp nearV
  have nearS : ∀ᶠ p : State × Control 2 in 𝓝 0, ‖T p‖ < R :=
    cj.continuousAt.norm.eventually_lt continuousAt_const (by simpa [t0] using hR)
  have initial : ∀ᶠ p : State × Control 2 in 𝓝 0, q+p.1 ∈ e.chart.target :=
    (show Tendsto (fun p : State × Control 2 => q+p.1) (𝓝 0) (𝓝 q) by
      simpa using (continuous_const.add continuous_fst).tendsto (0 : State × Control 2))
      (e.chart.open_target.mem_nhds hq)
  refine ⟨F,f0,cf,?_⟩
  filter_upwards [run,nearS,initial,small_frame_paths_stay e hq nearV] with p hp hS hi trap
  let z (t : ℝ) := q+T p (clamp t)
  have zv (t : ℝ) : z t ∈ V := by
    apply ball
    simpa [z,dist_eq_norm] using ((T p).norm_coe_le_norm (clamp t)).trans_lt hS
  refine ⟨hi,inChart (zv 1),graph_of_trapped e X _ _ V inChart hi z zv agree hp.1 ?_ trap⟩
  intro z' path
  let last : Time := ⟨1,zero_le_one,le_rfl⟩
  have v := hp.2 z' path last
  simpa only [z,show clamp 1 = last from projIcc_of_mem _ last.2] using v

/-- The actual Segment relation near a constant path is the graph of
a finite-order smooth endpoint, jointly in the initial coordinate
and the original L² control. -/
theorem small_segment_endpoint (e : Frame M 2) {q : State} (hq : q ∈ e.chart.target)
    (n : ℕ) (hn : 1 ≤ (n : WithTop ℕ∞)) :
    ∃ F : State × Control 2 → State, F 0 = q ∧ ContDiffAt ℝ n F 0 ∧
      ∀ᶠ p in 𝓝 0, q+p.1 ∈ e.chart.target ∧ F p ∈ e.chart.target ∧
        ∀ y, Segment e p.2 (e.chart.symm (q+p.1)) y ↔ y = e.chart.symm (F p) := by
  choose Y cy same using fun i => smooth_germ_extension e.chart.open_target hq (e.X i) (e.smooth i)
  let X := autonomous Y cy
  let V := e.chart.target ∩ {x | ∀ i, Y i x = e.X i x}
  have nearV : V ∈ 𝓝 q := inter_mem (e.chart.open_target.mem_nhds hq) (Filter.eventually_all.mpr same)
  have agree (x : State) (hx : x ∈ V) (t : ℝ) (v : Fiber 2) :
      X.velocity t x v = e.velocity x v := by
    change v 0 • Y 0 x + v 1 • Y 1 x = _
    rw [hx.2 0,hx.2 1]; simp [Frame.velocity,Fin.sum_univ_two]
  exact endpoint_of_columns e hq n hn X (fun i => auto_order n (Y i) (cy i)) V nearV inter_subset_left agree

#print axioms small_segment_endpoint

/-- A path-valued finite-order flow for the original frame, simultaneously
for nearby initial displacements and original controls. -/
theorem small_chart_path_family (e : Frame M 2) {q : State} (hq : q ∈ e.chart.target)
    (n : ℕ) (hn : 1 ≤ (n : WithTop ℕ∞)) :
    ∃ S : State × Control 2 → C(Time,State), ContDiffAt ℝ n S 0 ∧
      (∀ᶠ x in 𝓝 0, S (x,0) = ContinuousMap.const Time (q+x)) ∧
      ∀ᶠ p in 𝓝 0, (∀ t : Time, S p t ∈ e.chart.target) ∧
        ∀ t ∈ Icc (0:ℝ) 1, S p (clamp t) = q+p.1 +
          ∫ r in (0:ℝ)..t, e.velocity (S p (clamp r)) (p.2 r) := by
  choose Y cy same using fun i => smooth_germ_extension e.chart.open_target hq (e.X i) (e.smooth i)
  let X := autonomous Y cy
  obtain ⟨T,t0,ct,run⟩ := original_path_family X n hn (fun i => auto_order n (Y i) (cy i)) q
  let S (p : State × Control 2) := ContinuousMap.const Time q + T p
  have nearV : e.chart.target ∩ {x | ∀ i, Y i x = e.X i x} ∈ 𝓝 q :=
    inter_mem (e.chart.open_target.mem_nhds hq) (Filter.eventually_all.mpr same)
  obtain ⟨R,hR,ball⟩ := Metric.mem_nhds_iff.mp nearV
  have near : ∀ᶠ p in 𝓝 0, ‖T p‖ < R :=
    ct.continuousAt.norm.eventually_lt continuousAt_const (by simpa [t0] using hR)
  have flow : ∀ᶠ p in 𝓝 0, (∀ t : Time, S p t ∈ e.chart.target) ∧
      ∀ t ∈ Icc (0:ℝ) 1, S p (clamp t) = q+p.1 + ∫ r in (0:ℝ)..t, e.velocity (S p (clamp r)) (p.2 r) := by
    filter_upwards [near,run] with p small actual
    have within (t : Time) : S p t ∈ e.chart.target ∩ {x | ∀ i, Y i x = e.X i x} := by
      apply ball
      simpa [S,dist_eq_norm] using ((T p).norm_coe_le_norm t).trans_lt small
    refine ⟨fun t => (within t).1,fun t ht => (actual.1.2.2 t ht).trans ?_⟩
    apply congrArg ((q+p.1)+ ·)
    apply intervalIntegral.integral_congr
    intro r _
    change signal p.2 r 0 • Y 0 (S p (clamp r)) + signal p.2 r 1 • Y 1 (S p (clamp r)) = _
    rw [signal_apply,(within _).2 0,(within _).2 1]
    simp [Frame.velocity,Fin.sum_univ_two]
  refine ⟨S,contDiffAt_const.add ct,?_,flow⟩
  have push : Tendsto (fun x : State => (x,(0:Control 2))) (𝓝 0) (𝓝 0) :=
    (continuous_id.prodMk continuous_const).tendsto 0
  filter_upwards [push flow] with x hx
  apply ContinuousMap.ext
  intro t
  have zero : ∀ᵐ r ∂volume.restrict (uIoc (0:ℝ) (t:ℝ)), (0 : Control 2) r = 0 :=
    ae_mono (Measure.restrict_mono (by rw [uIoc_of_le t.2.1]; exact fun r hr => ⟨hr.1.le,hr.2.trans t.2.2⟩) le_rfl)
      (Lp.coeFn_zero (Fiber 2) 2 (volume.restrict (Icc (0:ℝ) 1)))
  have eq := hx.2 (t:ℝ) t.2
  have vanish : (∫ r in (0:ℝ)..(t:ℝ), e.velocity (S (x,0) (clamp r)) ((0:Control 2) r)) = 0 := by
    calc
      _ = ∫ _ in (0:ℝ)..(t:ℝ), (0:State) := intervalIntegral.integral_congr_ae_restrict (by
        filter_upwards [zero] with r hr
        rw [hr]; simp [Frame.velocity])
      _ = 0 := by simp
  change S (x,0) (clamp (t:ℝ)) = q+x+_ at eq
  rw [show clamp (t:ℝ) = t from projIcc_of_mem _ t.2] at eq
  exact eq.trans (by rw [vanish,add_zero]; rfl)

#print axioms small_chart_path_family

end MinimizingSard.Five
