import PulledFieldJets

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace MinimizingSard.Five
open Volterra PulseGeometry

private theorem linear_path_jets {U V W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (F : U → W) (C : U → V) (k : U)
    (K : U →L[ℝ] W) (L : V →L[ℝ] W) (cC : ContDiff ℝ 2 C)
    (same : F =ᶠ[𝓝 k] fun x => K x + L (C x)) :
    (∀ h, fderiv ℝ F k h = K h + L (fderiv ℝ C k h)) ∧
    ∀ h l, fderiv ℝ (fderiv ℝ F) k h l = L (fderiv ℝ (fderiv ℝ C) k h l) := by
  have form (x : U) := K.hasFDerivAt.add (L.hasFDerivAt.comp x ((cC.differentiable (by decide)) x).hasFDerivAt)
  have first : fderiv ℝ F =ᶠ[𝓝 k] fun x => K + L.comp (fderiv ℝ C x) := by
    filter_upwards [same.fderiv (𝕜 := ℝ)] with x hx
    exact hx.trans (form x).fderiv
  refine ⟨fun h => congrArg (fun B : U →L[ℝ] W => B h) first.self_of_nhds,?_⟩
  let post := ContinuousLinearMap.compL ℝ U V W L
  have d := (post.hasFDerivAt.comp k (((cC.fderiv_right (m := 1) (by decide)).differentiable (by decide)) k).hasFDerivAt).const_add K
  have result := (d.congr_of_eventuallyEq first).fderiv
  intro h l
  exact congrArg (fun B : U →L[ℝ] U →L[ℝ] W => B h l) result

private abbrev Coeff := C(Time,Fiber 2 →L[ℝ] State)
private def integralMap (v : Controls) : Coeff →L[ℝ] C(Time,State) :=
  (ContinuousLinearMap.apply ℝ C(Time,State) v).comp (Volterra.operator (Fiber 2) State)

private theorem time_derivative (v : Controls) (B : Coeff) :
    ∀ᵐ t ∂volume.restrict (Ioo (0:ℝ) 1), HasDerivAt
      (fun s => integralMap v B (clamp s)) (B (clamp t) (v t)) t := by
  apply path_ae_velocity _ _ (Volterra.intervalIntegrable B v)
  intro t ht
  have eq (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      integralMap v B (clamp s) = ∫ r in (0:ℝ)..s, B (clamp r) (v r) := by
    rw [show clamp s = ⟨s,hs⟩ from projIcc_of_mem _ hs]
    exact Volterra.operator_eq_interval B v _
  simp only [eq t ht,eq 0 (by norm_num),intervalIntegral.integral_same,zero_add]

private theorem path_germ {M : Type*} [TopologicalSpace M] [ChartedSpace State M]
    (e : Frame M 2) {q r u P} (tube : ReferenceTube e q r u P) {k : State}
    (hk : k ∈ Metric.ball q r) (C : State → Coeff)
    (agree : ∀ᶠ x in 𝓝 k, ∀ t a, C x t a = e.velocity (P x t) a)
    (v : Controls) (rep : ∀ s, v s = u s) :
    P =ᶠ[𝓝 k] fun x => ContinuousMap.const Time x + integralMap v (C x) := by
    filter_upwards [agree,Metric.isOpen_ball.mem_nhds hk] with x hx mem
    ext t i
    have eq := tube.flow x (Metric.ball_subset_closedBall mem) (t:ℝ) t.2
    rw [show clamp (t:ℝ) = t from projIcc_of_mem _ t.2] at eq
    change P x t i = (x + Volterra.operator (Fiber 2) State (C x) v t) i
    rw [eq,Volterra.operator_eq_interval]
    apply congrArg (fun z : State => (x+z) i)
    apply intervalIntegral.integral_congr
    intro s _
    change e.velocity (P x (clamp s)) (u s) = C x (clamp s) (v s)
    rw [hx,rep]

set_option maxHeartbeats 1000000 in
private theorem differentiated_paths (P : State → C(Time,State)) (C : State → Coeff) (k : State)
    (cC : ContDiff ℝ 2 C) (v : Controls)
    (near : P =ᶠ[𝓝 k] fun x => ContinuousMap.const Time x + integralMap v (C x))
    (V : ℝ → State → State) (vel : ∀ t, V t =ᶠ[𝓝 k] fun x => C x (clamp t) (v t))
    (h l : State) :
    ∀ᵐ t ∂volume.restrict (Ioo (0:ℝ) 1),
      HasDerivAt (fun s => fderiv ℝ P k h (clamp s)) (fderiv ℝ (V t) k h) t ∧
      HasDerivAt (fun s => fderiv ℝ (fderiv ℝ P) k h l (clamp s)) (fderiv ℝ (fderiv ℝ (V t)) k h l) t := by
  let K : State →L[ℝ] C(Time,State) := ContinuousLinearMap.const ℝ Time
  obtain ⟨first,second⟩ := linear_path_jets P C k K (integralMap v) cC near
  let B := fderiv ℝ C k h
  let D := fderiv ℝ (fderiv ℝ C) k h l
  filter_upwards [time_derivative v B,time_derivative v D] with t db dd
  let T : Coeff →L[ℝ] State :=
    (ContinuousLinearMap.apply ℝ State (v t)).comp (ContinuousMap.evalCLM ℝ (clamp t))
  have eq : V t =ᶠ[𝓝 k] fun x => (0 : State →L[ℝ] State) x + T (C x) := by
    simpa only [ContinuousLinearMap.zero_apply,zero_add] using vel t
  obtain ⟨dV,dV2⟩ := linear_path_jets (V t) C k 0 T cC eq
  rw [first h,second h l,dV h,dV2 h l,ContinuousLinearMap.zero_apply,zero_add]
  exact ⟨db.const_add h,dd⟩

/-- The entire fundamental matrix is a primitive with an integrable matrix
density. In particular its time variation has no singular component. -/
theorem reference_jacobian_primitive {M : Type*} [TopologicalSpace M] [ChartedSpace State M]
    (e : Frame M 2) {q r u P} (tube : ReferenceTube e q r u P) {k : State}
    (hk : k ∈ Metric.ball q r) :
    ∃ V : ℝ → State →L[ℝ] State, IntervalIntegrable V volume 0 1 ∧
      ∀ t : Time, (ContinuousMap.evalCLM ℝ t).comp (fderiv ℝ P k) =
        ContinuousLinearMap.id ℝ State + ∫ s in (0:ℝ)..(t:ℝ), V s := by
  obtain ⟨C,reg,agree⟩ := reference_velocity_family e tube hk
  obtain ⟨R,rep⟩ := control_signal_equiv
  let K : State →L[ℝ] C(Time,State) := ContinuousLinearMap.const ℝ Time
  let D := fderiv ℝ C k
  have first := (linear_path_jets P C k K (integralMap (R u)) reg (path_germ e tube hk C agree (R u) (rep u))).1
  let A (t : Time) := ((ContinuousMap.evalCLM ℝ t).comp D).flip
  have ca : Continuous A := by
    apply continuous_clm_apply.mpr
    intro a
    apply continuous_clm_apply.mpr
    intro h
    exact continuous_clm_apply.mp (D h).continuous a
  let B : C(Time,(Fiber 2) →L[ℝ] (State →L[ℝ] State)) := ⟨A,ca⟩
  let V (t : ℝ) := B (clamp t) (R u t)
  have integ : IntervalIntegrable V volume 0 1 := Volterra.intervalIntegrable B (R u)
  refine ⟨V,integ,?_⟩
  intro t
  apply ContinuousLinearMap.ext
  intro h
  let ev := ContinuousLinearMap.apply ℝ State h
  have sub : IntervalIntegrable V volume 0 t := integ.mono_set (by
    rw [uIcc_of_le t.2.1,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc_right t.2.2)
  change fderiv ℝ P k h t = h + ev (∫ s in (0:ℝ)..(t:ℝ), V s)
  rw [← ev.intervalIntegral_comp_comm sub,first h]
  change h + Volterra.operator (Fiber 2) State (D h) (R u) t = _
  rw [Volterra.operator_eq_interval]
  rfl

#print axioms reference_jacobian_primitive

/-- At an interior initial point the first and second spatial variations
of the same reference flow have time derivatives given by the first and
second spatial variations of the actual velocity. Controls are only L². -/
theorem reference_variation_time_derivatives {M : Type*} [TopologicalSpace M] [ChartedSpace State M]
    (e : Frame M 2) {q r u P} (tube : ReferenceTube e q r u P) {k : State}
    (hk : k ∈ Metric.ball q r) (h l : State) :
    ∀ᵐ t ∂volume.restrict (Ioo (0:ℝ) 1),
      let V := fun x => e.velocity (P x (clamp t)) (u t)
      HasDerivAt (fun s => fderiv ℝ P k h (clamp s)) (fderiv ℝ V k h) t ∧
      HasDerivAt (fun s => fderiv ℝ (fderiv ℝ P) k h l (clamp s))
        (fderiv ℝ (fderiv ℝ V) k h l) t := by
  obtain ⟨C,cC,agree⟩ := reference_velocity_family e tube hk
  obtain ⟨R,rep⟩ := control_signal_equiv
  let V := fun t x => e.velocity (P x (clamp t)) (u t)
  have vel (t : ℝ) : V t =ᶠ[𝓝 k] fun x => C x (clamp t) ((R u) t) := by
    filter_upwards [agree] with x hx
    rw [rep,hx]
  exact differentiated_paths P C k cC (R u) (path_germ e tube hk C agree (R u) (rep u)) V vel h l

#print axioms reference_variation_time_derivatives

theorem matrix_derivative {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (J : ℝ → State →L[ℝ] F) (A : State →L[ℝ] F) (t : ℝ)
    (cols : ∀ i : Fin 5, HasDerivAt (fun s => J s (Pi.single i 1)) (A (Pi.single i 1)) t) :
    HasDerivAt J A t := by
  let E : (State →L[ℝ] F) ≃L[ℝ] (Fin 5 → F) := ContinuousLinearEquiv.piRing (Fin 5)
  have d : HasDerivAt (fun s => E (J s)) (E A) t := hasDerivAt_pi.mpr cols
  simpa only [Function.comp_def,ContinuousLinearEquiv.coe_coe,E.symm_apply_apply]
    using E.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t d

/-- Time derivative of the fundamental matrix along the original rough input. -/
theorem reference_jacobian_ode {M : Type*} [TopologicalSpace M] [ChartedSpace State M]
    (e : Frame M 2) {q r u P} (tube : ReferenceTube e q r u P) {k : State}
    (hk : k ∈ Metric.ball q r) :
    let z := fun t : ℝ => P k (clamp t)
    let J := fun s : ℝ => (ContinuousMap.evalCLM ℝ (clamp s)).comp (fderiv ℝ P k)
    ∀ᵐ t ∂volume.restrict (Ioo (0:ℝ) 1), (J t).IsInvertible ∧
      HasDerivAt J ((fderiv ℝ (fun x => e.velocity x (u t)) (z t)).comp (J t)) t := by
  let z := fun t : ℝ => P k (clamp t)
  let J := fun s : ℝ => (ContinuousMap.evalCLM ℝ (clamp s)).comp (fderiv ℝ P k)
  have kc := Metric.ball_subset_closedBall hk
  have cols (i : Fin 5) := reference_variation_time_derivatives e tube hk (Pi.single i 1) 0
  have vari : ∀ᵐ t ∂volume.restrict (Ioo (0:ℝ) 1), (J t).IsInvertible ∧
      HasDerivAt J ((fderiv ℝ (fun x => e.velocity x (u t)) (z t)).comp (J t)) t := by
    filter_upwards [ae_all_iff.mpr cols] with t dt
    refine ⟨tube.invertible k kc _,matrix_derivative J _ t (fun i => ?_)⟩
    have diff (i : Fin 2) : DifferentiableAt ℝ (e.X i) (z t) :=
      ((e.smooth i).contDiffAt (e.chart.open_target.mem_nhds (tube.chart k kc _))).differentiableAt (by simp)
    have dv : DifferentiableAt ℝ (fun x => e.velocity x (u t)) (z t) := by
      simpa only [Frame.velocity,Fin.sum_univ_two] using
        ((diff 0).const_smul (u t 0)).add ((diff 1).const_smul (u t 1))
    have dp := (ContinuousMap.evalCLM ℝ (clamp t)).hasFDerivAt.comp k
      ((tube.regular k kc).differentiableAt (by decide)).hasFDerivAt
    have chain := (dv.hasFDerivAt.comp k dp).fderiv
    exact (congrArg (fun L : State →L[ℝ] State => L (Pi.single i 1)) chain) ▸ (dt i).1
  exact vari

#print axioms reference_jacobian_ode

/-- Time evolution of the actual transported frame values, with the
Jacobian ODE derived from the same reference tube and rough control. -/
theorem reference_frame_value_derivatives {M : Type*} [TopologicalSpace M] [ChartedSpace State M]
    (e : Frame M 2) {q r u P} (tube : ReferenceTube e q r u P) {k : State}
    (hk : k ∈ Metric.ball q r) :
    let J := fun s : ℝ => (ContinuousMap.evalCLM ℝ (clamp s)).comp (fderiv ℝ P k)
    let B := fun s : ℝ => (J s).inverse (VectorField.lieBracket ℝ (e.X 0) (e.X 1) (P k (clamp s)))
    ∀ᵐ t ∂volume.restrict (Ioo (0:ℝ) 1),
      HasDerivAt (fun s => pulledField e P 0 (clamp s) k) (-(u t 1) • B t) t ∧
      HasDerivAt (fun s => pulledField e P 1 (clamp s) k) (u t 0 • B t) t := by
  let z := fun t : ℝ => P k (clamp t)
  let J := fun s : ℝ => (ContinuousMap.evalCLM ℝ (clamp s)).comp (fderiv ℝ P k)
  have kc := Metric.ball_subset_closedBall hk
  have vari := reference_jacobian_ode e tube hk
  obtain ⟨C,_,agree⟩ := reference_velocity_family e tube hk
  obtain ⟨R,rep⟩ := control_signal_equiv
  have agree' (t : ℝ) : C k (clamp t) ((R u) t) = e.velocity (z t) (u t) := by
    rw [rep,agree.self_of_nhds]
  have hi : IntervalIntegrable (fun t => e.velocity (z t) (u t)) volume 0 1 := by
    simpa only [← agree'] using Volterra.intervalIntegrable (C k) (R u)
  exact transported_frame_values e u z J (fun t _ => tube.chart k kc _) hi
    (fun t ht => by simpa only [z,tube.initial k kc] using tube.flow k kc t ht) vari

#print axioms reference_frame_value_derivatives
end MinimizingSard.Five
