import ArbitraryFrameEndpoint
import PrimitivePairing

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace MinimizingSard.Five
open Volterra
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] {m : ℕ}

set_option maxHeartbeats 800000 in
/-- Simultaneous linearization of the original state and L² input in a
single arbitrary chart segment. The endpoint can be any representative
of the actual local graph. -/
theorem frame_segment_differential (e : Frame M m) (u : Control m) {x y : M} (seg : Segment e u x y)
    (G : State × Control m → State) (dg : DifferentiableAt ℝ G (e.chart x,u))
    (gr : ∀ᶠ b in 𝓝 (e.chart x,u), b.1 ∈ e.chart.target ∧ G b ∈ e.chart.target ∧
      ∀ t, Segment e b.2 (e.chart.symm b.1) t ↔ t = e.chart.symm (G b)) :
    ∃ w : C(Time,State), e.Solves u (e.chart x) w ∧ w (clamp 1) = e.chart y ∧
      ∃ D : C(Time,State →L[ℝ] Fiber m →L[ℝ] State), (∀ t, D t = fderiv ℝ e.coefficient (w t)) ∧
      ∀ h : State × Control m, ∃ z : C(Time,State), z (clamp 1) = fderiv ℝ G (e.chart x,u) h ∧
        TimePrimitive z h.1 (fun r => D (clamp r) (z (clamp r)) (u r) + e.velocity (w (clamp r)) (h.2 r)) := by
  obtain ⟨ex,_,w,hw,wy⟩ := (segment_iff_frame_path e u x y).mp seg
  let a := (e.chart x,u)
  obtain ⟨S,sw,cs,near⟩ := frame_path_family e u _ w hw 1 (by decide)
  have ds : DifferentiableAt ℝ S a := cs.differentiableAt (by decide)
  obtain ⟨Y,V,cy,ov,contains,_,agree⟩ := compact_smooth_extension e.chart.target (range w) e.chart.open_target
    (isCompact_range w.continuous) (range_nonempty _) (range_subset_iff.mpr hw.1) e.coefficient
    (e.coefficient_smooth.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by decide))
  let N := pathField Y cy.continuous
  have cd := (cy.fderiv_right (m := 0) (by decide)).continuous
  let D := pathField (fderiv ℝ Y) cd w
  let A := Volterra.operator (Fiber m) State
  let R := (frameSignal m).toContinuousLinearEquiv.toContinuousLinearMap
  let I : State →L[ℝ] C(Time,State) := ContinuousLinearMap.const ℝ Time
  let ev : C(Time,State) →L[ℝ] State := ContinuousMap.evalCLM ℝ (clamp 1)
  have reg (t : Time) : D t = fderiv ℝ e.coefficient (w t) := by
    have eq : Y =ᶠ[𝓝 (w t)] e.coefficient := Filter.mem_of_superset (ov.mem_nhds (contains (mem_range_self t))) (fun z hz => agree hz)
    exact eq.fderiv_eq
  have dN : HasFDerivAt N (PathCalculus.multiplier Time State (Fiber m →L[ℝ] State) D) w :=
    PathCalculus.hasFDerivAt_subst (liftField Y cy.continuous) (liftField (fderiv ℝ Y) cd)
      (fun _ x => (cy.differentiable (by decide) x).hasFDerivAt) w
  have eqS : S a = w := sw
  letI : NormedAddCommGroup (Causal.Signals (Fiber m) →L[ℝ] C(Time,State)) := inferInstance
  letI : NormedSpace ℝ (Causal.Signals (Fiber m) →L[ℝ] C(Time,State)) := inferInstance
  have opD := @ContinuousLinearMap.hasFDerivAt ℝ _ C(Time,Fiber m →L[ℝ] State) _ _
    (Causal.Signals (Fiber m) →L[ℝ] C(Time,State)) _ _ A (N (S a))
  have dN₀ : HasFDerivAt N (PathCalculus.multiplier Time State (Fiber m →L[ℝ] State) D) (S a) := by rw [eqS]; exact dN
  have dB : HasFDerivAt (A ∘ N) (A.comp (PathCalculus.multiplier Time State (Fiber m →L[ℝ] State) D)) (S a) :=
    opD.comp (S a) dN₀
  have cB := (dB.comp a ds.hasFDerivAt).clm_apply (R.hasFDerivAt.comp a (hasFDerivAt_snd (𝕜 := ℝ) (p := a)))
  have rhs := (I.hasFDerivAt.comp a (hasFDerivAt_fst (𝕜 := ℝ) (p := a))).add cB
  have tube : {z : C(Time,State) | MapsTo z univ V} ∈ 𝓝 (S a) := by
    rw [eqS]
    exact (ContinuousMap.isOpen_setOf_mapsTo isCompact_univ ov).mem_nhds (fun t _ => contains (mem_range_self t))
  have germ : S =ᶠ[𝓝 a] fun p => I p.1 + A (N (S p)) (R p.2) := by
    filter_upwards [near,ds.continuousAt tube] with p hp tube
    ext t : 1
    change S p t = p.1 + Volterra.operator (Fiber m) State (N (S p)) (R p.2) t
    rw [operator_eq_interval]
    have same (r : ℝ) : N (S p) (clamp r) = e.coefficient (S p (clamp r)) := agree (tube (mem_univ _))
    simp_rw [same]
    exact hp.1.2 t
  have deq := (rhs.congr_of_eventuallyEq germ).fderiv
  have fG : ev ∘ S =ᶠ[𝓝 a] G := by
    filter_upwards [near,gr] with p hp gp
    have out := hp.1.1 (clamp 1)
    have walk := (segment_iff_frame_path e p.2 (e.chart.symm p.1) (e.chart.symm (ev (S p)))).mpr
      ⟨e.chart.map_target gp.1,e.chart.map_target out,S p,by rw [e.chart.right_inv gp.1]; exact hp.1,(e.chart.right_inv out).symm⟩
    exact e.chart.symm.injOn out gp.2.1 ((gp.2.2 _).mp walk)
  have endD := ((ev.hasFDerivAt.comp a ds.hasFDerivAt).congr_of_eventuallyEq fG.symm).unique dg.hasFDerivAt
  refine ⟨w,hw,wy,D,reg,fun h => ?_⟩
  let z := fderiv ℝ S a h
  let B := PathCalculus.multiplier Time State (Fiber m →L[ℝ] State) D z
  have hb := Volterra.intervalIntegrable B (R u)
  have hwc := Volterra.intervalIntegrable (N w) (R h.2)
  have repr₁ (r : ℝ) : B (clamp r) (R u r) = D (clamp r) (z (clamp r)) (u r) := by
    change D (clamp r) (z (clamp r)) (frameSignal m u r) = _
    rw [frameSignal_apply]
  have repr₂ (r : ℝ) : N w (clamp r) (R h.2 r) = e.velocity (w (clamp r)) (h.2 r) := by
    change Y (w (clamp r)) (frameSignal m h.2 r) = _
    rw [agree (contains (mem_range_self _)),frameSignal_apply,Frame.coefficient_apply]
  have sum := hb.add hwc
  refine ⟨z,DFunLike.congr_fun endD h,by simpa only [repr₁,repr₂] using sum,fun t => ?_⟩
  have value := DFunLike.congr_fun deq h
  change z = I h.1 + (A (N (S a)) (R h.2) + A B (R u)) at value
  rw [eqS] at value
  have vt := congrArg (fun b : C(Time,State) => b t) value
  change z t = h.1 + (Volterra.operator (Fiber m) State (N w) (R h.2) t + Volterra.operator (Fiber m) State B (R u) t) at vt
  have intsub {f : ℝ → State} (hi : IntervalIntegrable f volume 0 1) : IntervalIntegrable f volume 0 (t:ℝ) :=
    hi.mono_set (by rw [uIcc_of_le t.property.1,uIcc_of_le zero_le_one]; exact Icc_subset_Icc le_rfl t.property.2)
  rw [operator_eq_interval,operator_eq_interval,add_comm (∫ r in (0:ℝ)..(t:ℝ), _),← intervalIntegral.integral_add (intsub hb) (intsub hwc)] at vt
  simpa only [repr₁,repr₂] using vt

#print axioms frame_segment_differential
end MinimizingSard.Five
