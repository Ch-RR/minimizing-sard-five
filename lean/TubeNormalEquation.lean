import TubeAdjoint
import IntegralClock
import SupportedControlDensity

noncomputable section
open Set Filter MeasureTheory IsManifold Metric
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
open Volterra PulseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M]

private theorem inverse_difference (L K : State ≃L[ℝ] State) :
    (L.symm : State →L[ℝ] State) - (K.symm : State →L[ℝ] State) =
    (L.symm : State →L[ℝ] State).comp (((K : State →L[ℝ] State) - (L : State →L[ℝ] State)).comp K.symm.toContinuousLinearMap) := by
  apply ContinuousLinearMap.ext
  intro x
  change L.symm x-K.symm x = L.symm (K (K.symm x)-L (K.symm x))
  simp

/-- The actual adjoint has integrable bounds on all increments; the bound
uses the fundamental-matrix primitive and uniform invertibility on compact time. -/
theorem tube_adjoint_dominated (e : Frame M 2) {q r u P} (tube : ReferenceTube e q r u P)
    {k : State} (hk : k ∈ Metric.ball q r) (η : State →L[ℝ] ℝ) :
    DominatedPath (fun t => tubeAdjoint P k η (clamp t)) := by
  let J := stateJacobian P k
  let row := η.comp (J (clamp 1))
  have inv (t : Time) : (J t).IsInvertible := tube.invertible k (Metric.ball_subset_closedBall hk) t
  have cont : Continuous J := continuous_clm_apply.mpr (fun h => (fderiv ℝ P k h).continuous)
  let N : C(Time,State →L[ℝ] State) := ⟨fun t => (J t).inverse,continuous_iff_continuousAt.mpr fun t =>
    ((inv t).contDiffAt_map_inverse (n := 1)).continuousAt.comp (x := t) cont.continuousAt⟩
  obtain ⟨V,vi,form⟩ := reference_jacobian_primitive e tube hk
  have j0 : J (clamp 0) = ContinuousLinearMap.id ℝ State := by
    simpa [J,clamp] using form (clamp 0)
  have dom := dominatedPath_of_primitive (fun s => J (clamp s)) V vi (by
    intro t ht
    change J (clamp t) = J (clamp 0) + _
    rw [j0,show clamp t = ⟨t,ht⟩ from projIcc_of_mem _ ht]
    exact form ⟨t,ht⟩)
  apply dom.map_bound _ (‖row‖*‖N‖*‖N‖) (by positivity)
  intro s _ t _ _
  let a := clamp s
  let b := clamp t
  obtain ⟨L,hL⟩ := inv b
  obtain ⟨K,hK⟩ := inv a
  have nb (t : Time) : ‖(J t).inverse‖ ≤ ‖N‖ := N.norm_coe_le_norm t
  have eq : (J b).inverse-(J a).inverse =
      (J b).inverse.comp (((J a)-(J b)).comp (J a).inverse) := by
    rw [← hL,← hK,ContinuousLinearMap.inverse_equiv,ContinuousLinearMap.inverse_equiv]
    exact inverse_difference L K
  change dist (row.comp (J b).inverse) (row.comp (J a).inverse) ≤ _*dist (J b) (J a)
  rw [dist_eq_norm,← ContinuousLinearMap.comp_sub,eq,dist_comm,dist_eq_norm]
  calc
    _ ≤ ‖row‖*(‖(J b).inverse‖*(‖J a-J b‖*‖(J a).inverse‖)) :=
      (row.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left (((J b).inverse.opNorm_comp_le _).trans
        (mul_le_mul_of_nonneg_left ((J a-J b).opNorm_comp_le _) (norm_nonneg _))) (norm_nonneg _))
    _ ≤ ‖row‖*(‖N‖*(‖J a-J b‖*‖N‖)) := by gcongr <;> exact nb _
    _ = _ := by ring

private theorem state_primitive (e : Frame M 2) {q r u P} (tube : ReferenceTube e q r u P)
    {k : State} (hk : k ∈ ball q r) :
    let z (t : ℝ) := P k (clamp t)
    let vel (t : ℝ) := e.velocity (z t) (u t)
    IntervalIntegrable vel volume 0 1 ∧ ∀ t ∈ Icc (0:ℝ) 1, z t = z 0+∫ s in (0:ℝ)..t, vel s := by
  intro z vel
  obtain ⟨C,_,agree⟩ := reference_velocity_family e tube hk
  obtain ⟨R,rep⟩ := control_signal_equiv
  have same (t : ℝ) : C k (clamp t) (R u t) = vel t := by rw [rep,agree.self_of_nhds]
  have kc := Metric.ball_subset_closedBall hk
  exact ⟨(funext same) ▸ Volterra.intervalIntegrable (C k) (R u),
    fun t ht => by simpa only [z,vel,tube.initial k kc] using tube.flow k kc t ht⟩

/-- An aligned original control yields the integral Hamilton equations on
the entire reference tube, including times of zero speed. -/
theorem tube_normal_integral (e : Frame M 2) {q r u P} (tube : ReferenceTube e q r u P)
    {k : State} (hk : k ∈ ball q r) (η : State →L[ℝ] ℝ) (ν : ℝ → ℝ)
    (iv : IntervalIntegrable ν volume 0 1)
    (aligned : ∀ᵐ t ∂volume.restrict (Ioo (0:ℝ) 1),
      u t = ν t • normalCoefficients e.X (P k (clamp t),tubeAdjoint P k η (clamp t))) :
    let Z (t : ℝ) : Phase := (P k (clamp t),tubeAdjoint P k η (clamp t))
    ∀ t ∈ Icc (0:ℝ) 1, Z t = Z 0 + ∫ s in (0:ℝ)..t, ν s • hamiltonianField e.X (Z s) := by
  intro Z
  let z (t : ℝ) := P k (clamp t)
  let p (t : ℝ) := tubeAdjoint P k η (clamp t)
  let U (t : ℝ) := fun x => e.velocity x (u t)
  obtain ⟨iU,form⟩ := state_primitive e tube hk
  have D := (dominatedPath_of_primitive z _ iU form).prod (tube_adjoint_dominated e tube hk η)
  have kc := Metric.ball_subset_closedBall hk
  have contZ : Continuous Z := ((P k).continuous.comp continuous_projIcc).prodMk
    ((tube_adjoint_endpoints e tube hk η).1.comp continuous_projIcc)
  have cf (i : Fin 2) (s : ℝ) : ContDiffAt ℝ ∞ (e.X i) (z s) :=
    (e.smooth i).contDiffAt (e.chart.open_target.mem_nhds (tube.chart k kc _))
  have ch : Continuous (fun s => hamiltonianField e.X (Z s)) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    have a (i : Fin 2) : ContinuousAt (fun t => normalCoefficients e.X (Z t) i) s :=
      contZ.continuousAt.snd.clm_apply ((cf i s).continuousAt.comp (x := s) contZ.continuousAt.fst)
    have base (i : Fin 2) := (a i).smul ((cf i s).continuousAt.comp (x := s) contZ.continuousAt.fst)
    let C := ContinuousLinearMap.compL ℝ State State ℝ
    have fiber (i : Fin 2) := (a i).smul ((C.continuous.continuousAt.comp (x := s) contZ.continuousAt.snd).clm_apply
      (((cf i s).fderiv_right (m := 1) (by decide)).continuousAt.comp (x := s) contZ.continuousAt.fst))
    simpa only [hamiltonianField,Fin.sum_univ_two] using ((base 0).add (base 1)).prodMk ((fiber 0).add (fiber 1)).neg
  apply D.integral
  · exact iv.smul_continuousOn ch.continuousOn
  · filter_upwards [path_ae_velocity z _ iU form,tube_adjoint_ode e tube hk η,aligned] with t st adj align
    have eqd : fderiv ℝ (U t) (z t) = ∑ i, u t i • fderiv ℝ (e.X i) (z t) := by
      exact (HasFDerivAt.sum (u := Finset.univ) (fun i _ =>
        ((cf i t).differentiableAt (by simp)).hasFDerivAt.const_smul (u t i))).fderiv
    have joint := st.prodMk adj
    convert joint using 1
    ext1
    · change ν t • (∑ i, normalCoefficients e.X (Z t) i • e.X i (z t)) = e.velocity (z t) (u t)
      rw [align]
      simp only [Z,Frame.velocity,Finset.smul_sum,Pi.smul_apply,smul_eq_mul,mul_smul]
    · change ν t • (-(∑ i, normalCoefficients e.X (Z t) i • (p t).comp (fderiv ℝ (e.X i) (z t)))) =
        -((p t).comp (fderiv ℝ (U t) (z t)))
      rw [eqd,align]
      simp only [Z,Fin.sum_univ_two,smul_neg,smul_add,Pi.smul_apply,smul_eq_mul,mul_smul,
        ContinuousLinearMap.comp_add,ContinuousLinearMap.comp_smul]

#print axioms tube_adjoint_dominated
#print axioms tube_normal_integral

/-- A supporting terminal covector produces the genuine integral Hamilton
orbit on each small chart piece. The speed and the adjoint come from the
original path, and zero-speed times are allowed. -/
theorem supported_tube_hamiltonian (e : Frame M 2) {q r u P} (tube : ReferenceTube e q r u P)
    {k : State} (hk : k ∈ ball q r) (G : State × Control 2 → State)
    (dg : DifferentiableAt ℝ G (k,u))
    (graph : ∀ᶠ b in 𝓝 (k,u), b.1 ∈ e.chart.target ∧ G b ∈ e.chart.target ∧
      ∀ y, Segment e b.2 (e.chart.symm b.1) y ↔ y = e.chart.symm (G b))
    (η : State →L[ℝ] ℝ)
    (support : ∀ v, pieceLength u+η (fderiv ℝ G (k,u) (0,v-u)) ≤ pieceLength v) :
    let Z (t : ℝ) : Phase := (P k (clamp t),tubeAdjoint P k η (clamp t))
    let ν (t : ℝ) := Real.sqrt (speedSq (u t))
    (∀ᵐ t ∂controlMeasure, u t = ν t • normalCoefficients e.X (Z t)) ∧
    ∀ t ∈ Icc (0:ℝ) 1, Z t = Z 0 + ∫ s in (0:ℝ)..t, ν s • hamiltonianField e.X (Z s) := by
  intro Z ν
  let B := (η.comp (fderiv ℝ G (k,u))).comp (ContinuousLinearMap.inr ℝ State (Control 2))
  have kc := Metric.ball_subset_closedBall hk
  have coord (i : Fin 2) : Continuous (fun t : Time => e.X i (P k t)) :=
    (e.smooth i).continuousOn.comp_continuous (P k).continuous (fun t => tube.chart k kc t)
  let b : C(Time,Fiber 2) := ⟨fun t i => tubeAdjoint P k η t (e.X i (P k t)),
    continuous_pi fun i => (tube_adjoint_endpoints e tube hk η).1.clm_apply (coord i)⟩
  have rep := (tube_endpoint_first_variation e tube hk G dg graph η).2
  have align := explicit_support_alignment u B b support rep
  refine ⟨align,tube_normal_integral e tube hk η ν (original_speed_integrable u) ?_⟩
  exact ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self align

#print axioms supported_tube_hamiltonian

end MinimizingSard.Five
