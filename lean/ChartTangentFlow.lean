import ActualFrameFlow
import TangentFlowIdentification

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace MinimizingSard.Five
open Volterra PulseGeometry

variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M]

def Frame.liftVelocity (e : Frame M 2) (p : State × State) (v : Fiber 2) :=
  v 0 • tangentLift (e.X 0) p + v 1 • tangentLift (e.X 1) p

/-- Lift the original fields inside their chart and use the original control.
Only the base point is restricted to the chart. -/
def ChartTangentPath (e : Frame M 2) (a : State × State) (u : Control 2) (w : ℝ → State × State) :=
  ContinuousOn w (Icc 0 1) ∧ MapsTo (Prod.fst ∘ w) (Icc 0 1) e.chart.target ∧
  IntervalIntegrable (fun t => e.liftVelocity (w t) (u t)) volume 0 1 ∧
  ∀ t ∈ Icc (0:ℝ) 1, w t = a + ∫ s in (0:ℝ)..t, e.liftVelocity (w s) (u s)

private theorem base_eq (e : Frame M 2) (p : State × State) (v : Fiber 2) :
    (e.liftVelocity p v).1 = e.velocity p.1 v := by
  simp [Frame.liftVelocity,tangentLift,Frame.velocity,Fin.sum_univ_two]

private theorem lift_stays (e : Frame M 2) {q : State} (hq : q ∈ e.chart.target) {V : Set State}
    (Vq : V ∈ 𝓝 q) (h : State) :
    ∀ᶠ p : (State × State) × Control 2 in 𝓝 0, ∀ w,
      ChartTangentPath e ((q,h)+p.1) p.2 w → MapsTo (Prod.fst ∘ w) (Icc 0 1) V := by
  have push : Tendsto (fun p : (State × State) × Control 2 => (p.1.1,p.2)) (𝓝 0) (𝓝 0) :=
    ((continuous_fst.comp continuous_fst).prodMk continuous_snd).tendsto 0
  filter_upwards [push (small_frame_paths_stay e hq Vq)] with p trap
  intro w hw
  apply trap (Prod.fst ∘ w) (continuous_fst.comp_continuousOn hw.1) hw.2.1
  intro t ht
  have sub := hw.2.2.1.mono_set (show uIcc (0:ℝ) t ⊆ uIcc 0 1 by
    rw [uIcc_of_le ht.1,uIcc_of_le zero_le_one]; exact Icc_subset_Icc le_rfl ht.2)
  have eq := congrArg (ContinuousLinearMap.fst ℝ State State) (hw.2.2.2 t ht)
  rw [map_add,← ContinuousLinearMap.intervalIntegral_comp_comm _ sub] at eq
  change (w t).1 = q + p.1.1 + ∫ s in (0:ℝ)..t, (e.liftVelocity (w s) (p.2 s)).1 at eq
  simpa only [base_eq] using eq

private theorem transfer_lift_path (B : Columns (State × State)) (e : Frame M 2)
    (u : Control 2) (v : Controls) (w : ℝ → State × State) (a : State × State)
    (inside : MapsTo (Prod.fst ∘ w) (Icc 0 1) e.chart.target)
    (point : ∀ t ∈ Icc (0:ℝ) 1, B.velocity t (w t) (v t) = e.liftVelocity (w t) (u t)) :
    ChartTangentPath e a u w ↔ B.Path a v w := by
  have integ := intervalIntegrable_congr (μ := volume) (a := (0:ℝ)) (b := 1)
    (fun t ht => point t (by rw [uIoc_of_le zero_le_one] at ht; exact ⟨ht.1.le,ht.2⟩))
  have eq (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : (∫ s in (0:ℝ)..t, B.velocity s (w s) (v s)) =
      ∫ s in (0:ℝ)..t, e.liftVelocity (w s) (u s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    exact point s ⟨hs.1,hs.2.trans ht.2⟩
  exact ⟨fun g => ⟨g.1,integ.mpr g.2.2.1,fun t ht => by rw [eq t ht]; exact g.2.2.2 t ht⟩,
    fun g => ⟨g.1,fun t ht => inside ht,integ.mp g.2.1,fun t ht => by rw [← eq t ht]; exact g.2.2 t ht⟩⟩

private theorem change_tangent_input {U V : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (R : U →L[ℝ] V) (q h : State)
    (Rel : State × State → V → (Time → State × State) → Prop)
    (S : State × V → C(Time,State)) (root : S 0 = ContinuousMap.const Time q)
    (cs : ContDiffAt ℝ 2 S 0)
    (near : ∀ᶠ p : (State × State) × V in 𝓝 0, Rel p.1 p.2
      (fun t => (S (p.1.1,p.2) t,fderiv ℝ (fun a => S (a,p.2) t) p.1.1 (h+p.1.2)))) :
    ∃ T : State × U → C(Time,State), T 0 = ContinuousMap.const Time q ∧ ContDiffAt ℝ 2 T 0 ∧
      ∀ᶠ p : (State × State) × U in 𝓝 0, Rel p.1 (R p.2)
        (fun t => (T (p.1.1,p.2) t,fderiv ℝ (fun a => T (a,p.2) t) p.1.1 (h+p.1.2))) := by
  let T (p : State × U) := S (p.1,R p.2)
  have cm : ContDiff ℝ 2 (fun p : State × U => (p.1,R p.2)) :=
    contDiff_fst.prodMk (R.contDiff.comp contDiff_snd)
  have base : (0,R 0) = (0 : State × V) := by simp
  refine ⟨T,?_,?_,?_⟩
  · exact (congrArg S base).trans root
  · exact (base.symm ▸ cs).comp (0 : State × U) cm.contDiffAt
  · have cast : Tendsto (fun p : (State × State) × U => (p.1,R p.2)) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_fst.prodMk (R.continuous.comp continuous_snd)).tendsto (0 : (State × State) × U)
    exact cast near

private theorem chart_tangent_of_extension (e : Frame M 2) {q : State} (hq : q ∈ e.chart.target) (h : State)
    (Y : Fin 2 → State → State) (sy : ∀ i, ContDiff ℝ ∞ (Y i)) (V : Set State) (Vq : V ∈ 𝓝 q)
    (within : V ⊆ e.chart.target)
    (agree : ∀ w : State × State, w.1 ∈ V → ∀ s v,
      (autonomousColumns (fun i => tangentLift (Y i)) (fun i => smooth_tangentLift _ (sy i))).velocity s w v = e.liftVelocity w v) :
    ∃ S : State × Control 2 → C(Time,State), ContDiffAt ℝ 2 S 0 ∧
      ∀ᶠ p : (State × State) × Control 2 in 𝓝 0,
        let w := fun t : Time => (S (p.1.1,p.2) t,
          fderiv ℝ (fun a => S (a,p.2) t) p.1.1 (h+p.1.2))
        ChartTangentPath e ((q,h)+p.1) p.2 (w ∘ clamp) ∧
          ∀ z, ChartTangentPath e ((q,h)+p.1) p.2 z → ∀ t : Time, z t = w t := by
  let B := autonomousColumns (fun i => tangentLift (Y i)) (fun i => smooth_tangentLift _ (sy i))
  obtain ⟨R,rep⟩ := control_signal_equiv
  obtain ⟨S,root,cs,near⟩ := local_tangent_flow Y sy q h
  let Rel (a : State × State) (v : Controls) (w : Time → State × State) :=
    B.Path ((q,h)+a) v (w ∘ clamp) ∧ ∀ z, B.Path ((q,h)+a) v z → ∀ t : Time, z t = w t
  obtain ⟨T,t0,cT,run⟩ := change_tangent_input R.toContinuousLinearEquiv.toContinuousLinearMap q h Rel S root cs
    (near.mono fun _ hnear => hnear.2)
  obtain ⟨r,hr,ball⟩ := Metric.mem_nhds_iff.mp Vq
  have small : ∀ᶠ p : State × Control 2 in 𝓝 0, dist (T p) (ContinuousMap.const Time q) < r :=
    cT.continuousAt.dist continuousAt_const |>.eventually_lt continuousAt_const (by simpa only [t0,dist_self] using hr)
  have first : Tendsto (fun p : (State × State) × Control 2 => (p.1.1,p.2)) (𝓝 0) (𝓝 0) :=
    ((continuous_fst.comp continuous_fst).prodMk continuous_snd).tendsto 0
  have same (u : Control 2) (w : ℝ → State × State) (inside : MapsTo (Prod.fst ∘ w) (Icc 0 1) V)
      (a : State × State) : ChartTangentPath e a u w ↔ B.Path a (R u) w :=
    transfer_lift_path B e u (R u) w a (fun _ ht => within (inside ht))
      (fun t ht => by rw [rep,agree _ (inside ht)])
  refine ⟨T,cT,?_⟩
  filter_upwards [first small,run,lift_stays e hq Vq h] with p tiny sol trap
  let w (t : Time) := (T (p.1.1,p.2) t,fderiv ℝ (fun a => T (a,p.2) t) p.1.1 (h+p.1.2))
  have inside : MapsTo (Prod.fst ∘ (w ∘ clamp)) (Icc 0 1) V := by
    intro t _
    apply ball
    exact (ContinuousMap.dist_apply_le_dist (f := T (p.1.1,p.2)) (g := ContinuousMap.const Time q) (clamp t)).trans_lt tiny
  exact ⟨(same _ _ inside _).mpr sol.1,fun z hz => sol.2 z ((same _ _ (trap z hz) _).mp hz)⟩

/-- Local tangent-flow identification for the actual smooth chart fields, with
original controls and uniqueness among every lifted trajectory staying in
the chart. The Jacobian is taken at the indicated time and initial state. -/
theorem chart_tangent_flow (e : Frame M 2) {q : State} (hq : q ∈ e.chart.target) (h : State) :
    ∃ S : State × Control 2 → C(Time,State), ContDiffAt ℝ 2 S 0 ∧
      ∀ᶠ p : (State × State) × Control 2 in 𝓝 0,
        let w := fun t : Time => (S (p.1.1,p.2) t,
          fderiv ℝ (fun a => S (a,p.2) t) p.1.1 (h+p.1.2))
        ChartTangentPath e ((q,h)+p.1) p.2 (w ∘ clamp) ∧
          ∀ z, ChartTangentPath e ((q,h)+p.1) p.2 z → ∀ t : Time, z t = w t := by
  choose Y sy germ using fun i => smooth_germ_extension e.chart.open_target hq (e.X i) (e.smooth i)
  let V := e.chart.target ∩ {x | ∀ i, Y i =ᶠ[𝓝 x] e.X i}
  have Vq : V ∈ 𝓝 q := inter_mem (e.chart.open_target.mem_nhds hq)
    (Filter.eventually_all.mpr fun i => eventually_eventually_nhds.mpr (germ i))
  let B := autonomousColumns (fun i => tangentLift (Y i)) (fun i => smooth_tangentLift _ (sy i))
  have agree (w : State × State) (hw : w.1 ∈ V) (s : ℝ) (v : Fiber 2) :
      B.velocity s w v = e.liftVelocity w v := by
    have eq (i : Fin 2) : tangentLift (Y i) w = tangentLift (e.X i) w := by
      unfold tangentLift
      rw [(hw.2 i).self_of_nhds,(hw.2 i).fderiv_eq]
    change v 0 • tangentLift (Y 0) w + v 1 • tangentLift (Y 1) w = _
    rw [eq,eq]; rfl
  exact chart_tangent_of_extension e hq h Y sy V Vq inter_subset_left agree

#print axioms chart_tangent_flow

/-- Chain rule when the spatial flow takes values in continuous paths.
Only the frozen path through the current initial point is differentiated
in time. The control itself needs no time derivative. -/
theorem moving_path_derivative {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (S : E → C(Time,V)) (a : ℝ → E)
    (t : ℝ) (v : E) (w : V) (dS : DifferentiableAt ℝ S (a t))
    (da : HasDerivAt a v t) (fixedTime : HasDerivAt (fun s => S (a t) (clamp s)) w t) :
    HasDerivAt (fun s => S (a s) (clamp s)) (fderiv ℝ S (a t) v (clamp t) + w) t := by
  have spatial := dS.hasFDerivAt.comp_hasDerivAt t da
  have slopeLim := hasDerivAt_iff_tendsto_slope.mp spatial
  have timeLim : Tendsto clamp (𝓝[≠] t) (𝓝 (clamp t)) :=
    continuous_projIcc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have both : Tendsto (fun s => slope (S ∘ a) t s (clamp s)) (𝓝[≠] t)
      (𝓝 (fderiv ℝ S (a t) v (clamp t))) :=
    continuous_eval.continuousAt.tendsto.comp (slopeLim.prodMk_nhds timeLim)
  apply hasDerivAt_iff_tendsto_slope.mpr
  apply (both.add (hasDerivAt_iff_tendsto_slope.mp fixedTime)).congr'
  filter_upwards with s
  simp only [slope_def_module,ContinuousMap.smul_apply,ContinuousMap.sub_apply,Function.comp_apply,
    ← smul_add,sub_add_sub_cancel]

#print axioms moving_path_derivative

/-- Differentiate a compact family of integral trajectories on one
common full-measure time set. The initial point may be chosen after
the time, including as a function of that time. The integrand can be
extended by zero outside the chart time window. -/
theorem simultaneous_integral_velocity {K V : Type*} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (f : ℝ → C(K,V))
    (hf : Integrable f volume) : ∀ᵐ t ∂volume, ∀ x : K, ∀ c : ℝ,
      HasDerivAt (fun s => ∫ r in c..s, f r x) (f t x) t := by
  open IsUnifLocDoublingMeasure in
    have avg := (vitaliFamily volume 1).ae_tendsto_average hf.locallyIntegrable
  filter_upwards [avg] with t ht
  intro x c
  let P (s : ℝ) := ∫ r in c..s, f r
  have der : HasDerivAt P (f t) t := by
    rw [hasDerivAt_iff_tendsto_slope_left_right]
    have eq (a b : ℝ) : (∫ r in Ioc a b, f r) = ∫ r in Icc a b, f r :=
      integral_Icc_eq_integral_Ioc.symm
    constructor
    · refine Filter.tendsto_congr' ?_ |>.mpr (ht.comp t.tendsto_Icc_vitaliFamily_left)
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hst : s ≤ t := le_of_lt hs
      simp [P,slope,average,intervalIntegral.integral_interval_sub_left,hf.intervalIntegrable,
        intervalIntegral.integral_of_ge,hst,eq,← neg_smul,← inv_neg]
    · refine Filter.tendsto_congr' ?_ |>.mpr (ht.comp t.tendsto_Icc_vitaliFamily_right)
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hts : t ≤ s := le_of_lt hs
      simp [P,slope,average,intervalIntegral.integral_interval_sub_left,hf.intervalIntegrable,
        intervalIntegral.integral_of_le,hts,eq]
  let L : C(K,V) →L[ℝ] V := ContinuousMap.evalCLM ℝ x
  have d := (@ContinuousLinearMap.hasFDerivAt ℝ _ C(K,V) _ _ V _ _ L (P t)).comp_hasDerivAt t der
  apply d.congr_of_eventuallyEq
  filter_upwards with s
  exact L.intervalIntegral_comp_comm hf.intervalIntegrable

#print axioms simultaneous_integral_velocity

/-- Time differentiation of a flow along a moving initial point. The
exceptional time set is independent of the curve of initial points.
This version is local on a compact set of chart coordinates. -/
theorem moving_integral_family {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (K : Set E) [CompactSpace K]
    (S : E → C(Time,V)) (f : ℝ → C(K,V)) (hf : Integrable f volume)
    (eq : ∀ x : K, ∀ s ∈ Icc (0:ℝ) 1,
      S x (clamp s) = S x (clamp 0) + ∫ r in (0:ℝ)..s, f r x) :
    ∀ᵐ t ∂volume.restrict (Ioo (0:ℝ) 1), ∀ (a : ℝ → E) (v : E) (inside : a t ∈ K),
      DifferentiableAt ℝ S (a t) → HasDerivAt a v t →
      HasDerivAt (fun s => S (a s) (clamp s))
        (fderiv ℝ S (a t) v (clamp t) + f t ⟨a t,inside⟩) t := by
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [simultaneous_integral_velocity f hf] with t good
  intro ht a v inside dS da
  apply moving_path_derivative S a t v _ dS da
  apply ((good ⟨a t,inside⟩ 0).const_add (S (a t) (clamp 0))).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact eq ⟨a t,inside⟩ s ⟨hs.1.le,hs.2.le⟩

#print axioms moving_integral_family
end MinimizingSard.Five
