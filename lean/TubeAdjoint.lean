import ReferencePathJets
import TerminalMovingEndpoint
import HamiltonianFrame

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
open Volterra PulseGeometry

variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M]

def stateJacobian (P : State → C(Time,State)) (k : State) (t : Time) :=
  (ContinuousMap.evalCLM ℝ t).comp (fderiv ℝ P k)

def tubeAdjoint (P : State → C(Time,State)) (k : State) (η : State →L[ℝ] ℝ) (t : Time) :=
  (η.comp (stateJacobian P k (clamp 1))).comp (stateJacobian P k t).inverse

theorem tube_adjoint_endpoints (e : Frame M 2) {q r u P} (tube : ReferenceTube e q r u P)
    {k : State} (hk : k ∈ Metric.ball q r) (η : State →L[ℝ] ℝ) :
    Continuous (tubeAdjoint P k η) ∧ tubeAdjoint P k η (clamp 1) = η ∧
      tubeAdjoint P k η (clamp 0) = η.comp (stateJacobian P k (clamp 1)) := by
  let J := stateJacobian P k
  have kc := Metric.ball_subset_closedBall hk
  have cont : Continuous J := continuous_clm_apply.mpr (fun h => (fderiv ℝ P k h).continuous)
  have iv (t : Time) : (J t).IsInvertible := tube.invertible k kc t
  have cin : Continuous (fun t => (J t).inverse) := continuous_iff_continuousAt.mpr fun t =>
    ((iv t).contDiffAt_map_inverse (n := 1)).continuousAt.comp (x := t) cont.continuousAt
  have at0 : J (clamp 0) = ContinuousLinearMap.id ℝ State := by
    let ev := (ContinuousMap.evalCLM ℝ (clamp 0) : C(Time,State) →L[ℝ] State)
    have eq : (fun x => P x (clamp 0)) =ᶠ[𝓝 k] id := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hk] with x hx using tube.initial x (Metric.ball_subset_closedBall hx)
    have d := ev.hasFDerivAt.comp k ((tube.regular k kc).differentiableAt (by decide)).hasFDerivAt
    exact (d.congr_of_eventuallyEq eq.symm).unique (hasFDerivAt_id k)
  refine ⟨continuous_const.clm_comp cin,?_,?_⟩
  · obtain ⟨L,eq⟩ := iv (clamp 1)
    change (η.comp (J (clamp 1))).comp (J (clamp 1)).inverse = η
    rw [← eq,ContinuousLinearMap.inverse_equiv]
    exact ContinuousLinearMap.ext fun h => congrArg η (L.apply_symm_apply h)
  · change (η.comp (J (clamp 1))).comp (J (clamp 0)).inverse = _
    rw [at0,ContinuousLinearMap.inverse_id]
    rfl

/-- The adjoint of the genuine rough controlled ODE solves the adjoint
equation almost everywhere along the original clock. -/
theorem tube_adjoint_ode (e : Frame M 2) {q r u P} (tube : ReferenceTube e q r u P)
    {k : State} (hk : k ∈ Metric.ball q r) (η : State →L[ℝ] ℝ) :
    ∀ᵐ t ∂volume.restrict (Ioo (0:ℝ) 1), HasDerivAt (fun s => tubeAdjoint P k η (clamp s))
      (-(tubeAdjoint P k η (clamp t)).comp (fderiv ℝ (fun x => e.velocity x (u t)) (P k (clamp t)))) t := by
  let J (t : ℝ) := stateJacobian P k (clamp t)
  let p := η.comp (J 1)
  filter_upwards [reference_jacobian_ode e tube hk] with t dt
  let D := fderiv ℝ (fun x => e.velocity x (u t)) (P k (clamp t))
  obtain ⟨L,eq⟩ := dt.1
  let g := (ContinuousLinearEquiv.unitsEquiv ℝ State).symm L
  have eg : (g : State →L[ℝ] State) = J t := eq
  have d := hasFDerivAt_ringInverse (𝕜 := ℝ) g
  rw [eg] at d
  have dj := d.comp_hasDerivAt t dt.2
  rw [ContinuousLinearMap.ringInverse_eq_inverse] at dj
  let row := (ContinuousLinearMap.compL ℝ State State ℝ) p
  have der := row.hasFDerivAt.comp_hasDerivAt t dj
  convert der using 1
  apply ContinuousLinearMap.ext
  intro h
  change -p ((J t).inverse (D h)) = p (-(L.symm ((D.comp (J t)) (L.symm h))))
  rw [← (show (L : State →L[ℝ] State) = J t from eq),ContinuousLinearMap.inverse_equiv]
  simp

theorem tube_segment (e : Frame M 2) {q r u P} (tube : ReferenceTube e q r u P)
    {k : State} (hk : k ∈ Metric.ball q r) :
    Segment e u (e.chart.symm k) (e.chart.symm (P k (clamp 1))) := by
  have kc := Metric.ball_subset_closedBall hk
  have start := tube.initial k kc
  have kt : k ∈ e.chart.target := start ▸ tube.chart k kc _
  have fin := tube.chart k kc (clamp 1)
  obtain ⟨C,_,agree⟩ := reference_velocity_family e tube hk
  obtain ⟨R,rep⟩ := control_signal_equiv
  have vel (s : ℝ) : C k (clamp s) (R u s) = e.velocity (P k (clamp s)) (u s) := by
    rw [rep,agree.self_of_nhds]
  refine ⟨e.chart.map_target kt,e.chart.map_target fin,fun s => P k (clamp s),
    ((P k).continuous.comp continuous_projIcc).continuousOn,fun t _ => tube.chart k kc _,
    start.trans (e.chart.right_inv kt).symm,(e.chart.right_inv fin).symm,?_,?_⟩
  · simpa only [← vel] using Volterra.intervalIntegrable (C k) (R u)
  · intro t ht
    simpa only [start] using tube.flow k kc t ht

/-- Both blocks of the endpoint derivative on an actual tube. The second
formula tests arbitrary square-integrable variations of the original input. -/
theorem tube_endpoint_first_variation (e : Frame M 2) {q r u P} (tube : ReferenceTube e q r u P)
    {k : State} (hk : k ∈ Metric.ball q r) (G : State × Control 2 → State)
    (dg : DifferentiableAt ℝ G (k,u))
    (graph : ∀ᶠ b in 𝓝 (k,u), b.1 ∈ e.chart.target ∧ G b ∈ e.chart.target ∧
      ∀ y, Segment e b.2 (e.chart.symm b.1) y ↔ y = e.chart.symm (G b))
    (η : State →L[ℝ] ℝ) :
    (∀ h, η (fderiv ℝ G (k,u) (h,0)) = tubeAdjoint P k η (clamp 0) h) ∧
    (∀ h, η (fderiv ℝ G (k,u) (0,h)) =
      ∫ t in (0:ℝ)..1, ∑ i, h t i * tubeAdjoint P k η (clamp t) (e.X i (P k (clamp t)))) := by
  let J := stateJacobian P k
  let out := η.comp (J (clamp 1))
  let ψ (z : State) := P z (clamp 1)
  have ev : HasFDerivAt ψ (J (clamp 1)) k :=
    (ContinuousMap.evalCLM ℝ (clamp 1) : C(Time,State) →L[ℝ] State).hasFDerivAt.comp k
      ((tube.regular k (Metric.ball_subset_closedBall hk)).differentiableAt (by decide)).hasFDerivAt
  constructor
  · have incl : HasFDerivAt (fun z : State => (z,u)) (ContinuousLinearMap.inl ℝ State (Control 2)) k :=
      (hasFDerivAt_id k).prodMk (hasFDerivAt_const u k)
    have same : (fun z => G (z,u)) =ᶠ[𝓝 k] ψ := by
      filter_upwards [incl.continuousAt.tendsto graph,Metric.isOpen_ball.mem_nhds hk] with z gz hz
      have seg := tube_segment e tube hz
      exact e.chart.symm.injOn gz.2.1 (tube.chart z (Metric.ball_subset_closedBall hz) _) ((gz.2.2 _).mp seg).symm
    have eq := ((dg.hasFDerivAt.comp k incl).congr_of_eventuallyEq same.symm).unique ev
    intro h
    rw [(tube_adjoint_endpoints e tube hk η).2.2]
    exact congrArg η (congrArg (fun D : State →L[ℝ] State => D h) eq)
  · obtain ⟨X,⟨jets⟩,agree⟩ := localized_pulled_columns e tube hk
    obtain ⟨R,rep⟩ := control_signal_equiv
    obtain ⟨A,a0,endA,smA⟩ := exists_smooth_integral_endpoint X jets k
    let RC := R.toContinuousLinearEquiv.toContinuousLinearMap
    have rv : HasFDerivAt (fun v : Control 2 => (k,u+v)) (ContinuousLinearMap.inr ℝ State (Control 2)) 0 :=
      (hasFDerivAt_const k 0).prodMk ((hasFDerivAt_id (0 : Control 2)).const_add u)
    have push : Tendsto (fun v : Control 2 => (k,u+v)) (𝓝 0) (𝓝 (k,u)) := by simpa using rv.continuousAt.tendsto
    have same : (fun v => G (k,u+v)) =ᶠ[𝓝 0] ψ ∘ A ∘ RC := by
      filter_upwards [moving_segments_near e tube hk X jets agree R rep A endA,push graph] with v moved gv
      exact e.chart.symm.injOn gv.2.1 moved.1 ((gv.2.2 _).mp moved.2).symm
    have aeq : A (RC 0) = k := by simp [a0]
    have da : HasFDerivAt A (fderiv ℝ A 0) (RC 0) := by simpa only [map_zero] using (smA.differentiableAt (by decide)).hasFDerivAt
    have l := (show DifferentiableAt ℝ G (k,u+0) by simpa using dg).hasFDerivAt.comp 0 rv
    have right := (aeq.symm ▸ ev).comp 0 (da.comp 0 RC.hasFDerivAt)
    have eq := (l.congr_of_eventuallyEq same.symm).unique right
    intro h
    have eval := congrArg (fun D : Control 2 →L[ℝ] State => η (D h)) eq
    change η (fderiv ℝ G (k,u+0) (0,h)) = out (fderiv ℝ A 0 (R h)) at eval
    rw [add_zero,integral_endpoint_first X jets k A endA (R h)] at eval
    rw [eval]
    let coef (t : Time) := ((ContinuousLinearMap.proj (0 : Fin 2) : Fiber 2 →L[ℝ] ℝ).smulRight (X.Y 0 t k)) +
      ((ContinuousLinearMap.proj (1 : Fin 2) : Fiber 2 →L[ℝ] ℝ).smulRight (X.Y 1 t k))
    have cc : Continuous coef := by
      have cX (i : Fin 2) : Continuous (fun t : Time => X.Y i t k) :=
        (X.continuous i).comp (continuous_subtype_val.prodMk continuous_const)
      let S (i : Fin 2) := ContinuousLinearMap.smulRightL ℝ (Fiber 2) State (ContinuousLinearMap.proj i)
      exact ((S 0).continuous.comp (cX 0)).add ((S 1).continuous.comp (cX 1))
    let C : C(Time,Fiber 2 →L[ℝ] State) := ⟨coef,cc⟩
    have it := Volterra.intervalIntegrable C (R h)
    change IntervalIntegrable (fun t => X.velocity (clamp t) k (R h t)) volume 0 1 at it
    rw [← out.intervalIntegral_comp_comm it]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [Columns.velocity,map_add,map_smul,rep,Fin.sum_univ_two,
      agree.self_of_nhds,smul_eq_mul,show clamp (clamp t : ℝ) = clamp t from projIcc_of_mem _ (clamp t).property]
    rfl

#print axioms tube_adjoint_endpoints
#print axioms tube_adjoint_ode
#print axioms tube_endpoint_first_variation
end MinimizingSard.Five
