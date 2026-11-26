import PulledFieldJets
import IntrinsicHessianTransport

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace MinimizingSard.Five
open Volterra PulseGeometry

variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M]

private theorem original_of_localized (e : Frame M 2) {q r u P} (tube : ReferenceTube e q r u P)
    (X : Columns State) (k : State) (v : Control 2) (w : Controls) (same : ∀ t, w t = v t)
    (a : ℝ → State) (path : X.Path k w a)
    (inside : ∀ t, a t ∈ Metric.closedBall q r)
    (agree : ∀ t i, X.Y i t (a t) = pulledField e P i (clamp t) (a t)) :
    Segment e (u+v) (e.chart.symm k) (e.chart.symm (P (a 1) (clamp 1))) := by
  have start : a 0 = k := by simpa using path.2.2 0 (by norm_num)
  let b (t : ℝ) := X.velocity t (a t) (w t)
  have vel (t : ℝ) (_ : t ∈ Icc (0:ℝ) 1) :
      b t = ((ContinuousMap.evalCLM ℝ (clamp t)).comp (fderiv ℝ P (a t))).inverse
        (e.velocity (P (a t) (clamp t)) (v t)) := by
    simp only [b,Columns.velocity,agree t,pulledField,same,Frame.velocity,Fin.sum_univ_two,
      map_add,map_smul]
  obtain ⟨L,lip⟩ := tube.lipschitz
  have pert := pulled_path_gives_segment e u v (Metric.closedBall q r) P L lip
    (fun z hz => (tube.regular z hz).differentiableAt (by decide)) tube.chart tube.initial tube.flow
    a path.1 (fun t _ => inside t) (fun t _ => tube.invertible _ (inside t) _)
    b path.2.1 (fun t ht => (path.2.2 t ht).trans (by rw [start])) vel
  rwa [start] at pert

private theorem buffered_paths (X : Columns State) (jets : SpatialJets X)
    (k : State) {N : Set State} (near : N ∈ 𝓝 k)
    (A : Controls → State) (endpoint : X.Endpoint k A) :
    ∀ᶠ w in 𝓝 (0 : Controls), ∃ a : ℝ → State, X.Path k w a ∧
      (∀ t, a t ∈ N) ∧ A w = a 1 := by
  obtain ⟨S,s0,cs,paths⟩ := smooth_path_family X jets k
  obtain ⟨ε,hε,within⟩ := Metric.mem_nhds_iff.mp near
  have tiny : ∀ᶠ v in 𝓝 (0:Controls), ‖S v‖ < ε :=
    cs.continuousAt.norm.eventually_lt continuousAt_const (by simpa [s0] using hε)
  filter_upwards [paths,tiny,endpoint] with w path small endA
  let a (t : ℝ) := k + S w (clamp t)
  refine ⟨a,path.1,fun t => within ?_,endA a path.1⟩
  simpa [a,Metric.mem_ball,dist_eq_norm] using ((S w).norm_coe_le_norm (clamp t)).trans_lt small

private theorem lift_neighborhood {U W : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (R : U ≃ₗᵢ[ℝ] W) {p : W → Prop}
    (hp : ∀ᶠ w in 𝓝 0, p w) : ∀ᶠ v in 𝓝 0, p (R v) := by
  have t : Tendsto R (𝓝 0) (𝓝 0) := R.map_zero ▸ R.continuous.tendsto 0
  exact t hp

theorem moving_segments_near (e : Frame M 2) {q r u P} (tube : ReferenceTube e q r u P)
    {k : State} (kr : k ∈ Metric.ball q r) (X : Columns State) (jets : SpatialJets X)
    (agree : ∀ᶠ x in 𝓝 k, ∀ i t, X.Y i t x = pulledField e P i (clamp t) x)
    (R : Control 2 ≃ₗᵢ[ℝ] Controls) (hR : ∀ v t, (R v) t = v t)
    (A : Controls → State) (endpoint : X.Endpoint k A) :
    ∀ᶠ v in 𝓝 (0 : Control 2), P (A (R v)) (clamp 1) ∈ e.chart.target ∧
      Segment e (u+v) (e.chart.symm k) (e.chart.symm (P (A (R v)) (clamp 1))) := by
  have near := buffered_paths X jets k (inter_mem (Metric.isOpen_ball.mem_nhds kr) agree) A endpoint
  filter_upwards [lift_neighborhood R near] with v paths
  obtain ⟨a,pathA,within,stopA⟩ := paths
  have inside (t : ℝ) : a t ∈ Metric.closedBall q r := Metric.ball_subset_closedBall (within t).1
  have agree' (t : ℝ) (i : Fin 2) := (within t).2 i t
  rw [stopA]
  exact ⟨tube.chart _ (inside 1) _,original_of_localized e tube X k v (R v) (hR v) a pathA inside agree'⟩

theorem finite_range_of_kernel {U V W : Type*}
    [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup W] [Module ℝ W] (Q : U →ₗ[ℝ] V) (T : U →ₗ[ℝ] W)
    (sub : LinearMap.ker Q ≤ LinearMap.ker T) : FiniteDimensional ℝ (LinearMap.range T) := by
  letI : FiniteDimensional ℝ (U ⧸ LinearMap.ker Q) := Q.quotKerEquivRange.symm.finiteDimensional
  letI : FiniteDimensional ℝ (U ⧸ LinearMap.ker T) :=
    FiniteDimensional.of_surjective (Submodule.factor sub) (Submodule.factor_surjective sub)
  exact T.quotKerEquivRange.finiteDimensional

private theorem finite_transport_row (A B : Controls → State) (ψ : State → State) (k : State)
    (eq : ∀ h l : Controls, fderiv ℝ (fderiv ℝ B) 0 h l =
      fderiv ℝ ψ k (fderiv ℝ (fderiv ℝ A) 0 h l) +
      fderiv ℝ (fderiv ℝ ψ) k (fderiv ℝ A 0 h) (fderiv ℝ A 0 l))
    (p : State →L[ℝ] ℝ) [FiniteDimensional ℝ (LinearMap.range (restrictedHessianRow B p))] :
    FiniteDimensional ℝ (LinearMap.range (hessianRow A (p.comp (fderiv ℝ ψ k)))) := by
  let H := hessianRow B p
  let T := hessianRow A (p.comp (fderiv ℝ ψ k))
  letI : FiniteDimensional ℝ (LinearMap.range H) := full_rank_finite_of_restricted B p
  let Q := H.rangeRestrict.prod (fderiv ℝ A 0).toLinearMap
  have sub : LinearMap.ker Q ≤ LinearMap.ker T := by
    intro h hh
    have v : Q h = 0 := hh
    have row : H h = 0 := congrArg (fun z : LinearMap.range H × State => z.1.val) v
    have dh : fderiv ℝ A 0 h = 0 := congrArg Prod.snd v
    apply ContinuousLinearMap.ext
    intro l
    have hz : p (fderiv ℝ (fderiv ℝ B) 0 h l) = 0 :=
      congrArg (fun f : Controls →L[ℝ] ℝ => f l) row
    rw [eq h l,dh,map_zero,ContinuousLinearMap.zero_apply,add_zero] at hz
    exact hz
  exact finite_range_of_kernel Q T sub

theorem nonzero_pullback {J : State →L[ℝ] State} (inv : J.IsInvertible)
    {p : State →L[ℝ] ℝ} (hp : p ≠ 0) : p.comp J ≠ 0 := by
  obtain ⟨T,hT⟩ := inv
  change T.toContinuousLinearMap = J at hT
  rintro zero
  apply hp
  ext y
  have h := congrArg (fun f : State →L[ℝ] ℝ => f (T.symm y)) zero
  simpa only [← hT,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    T.apply_symm_apply,ContinuousLinearMap.zero_apply] using h

/-- Every representative obtained from the original segment equation has
the same germ. The full vector Hessian includes the state-change term,
and finite rank on the kernel of the original segment gives finite rank
of the full transported scalar row on the moving control space. -/
def TerminalHessian (e : Frame M 2) (u : Control 2) (k : State)
    (R : Control 2 ≃ₗᵢ[ℝ] Controls) (A : Controls → State) (ψ : State → State) : Prop :=
  ∀ B : Controls → State,
    (∀ᶠ w in 𝓝 0, B w ∈ e.chart.target ∧
      Segment e (u+R.symm w) (e.chart.symm k) (e.chart.symm (B w))) →
    B =ᶠ[𝓝 0] ψ ∘ A ∧ (∀ h l : Controls,
      fderiv ℝ (fderiv ℝ B) 0 h l =
        fderiv ℝ ψ k (fderiv ℝ (fderiv ℝ A) 0 h l) +
        fderiv ℝ (fderiv ℝ ψ) k (fderiv ℝ A 0 h) (fderiv ℝ A 0 l)) ∧
    ∀ p : State →L[ℝ] ℝ,
      (p ≠ 0 → p.comp (fderiv ℝ ψ k) ≠ 0) ∧
      ((∀ h, p (fderiv ℝ B 0 h) = 0) → ∀ h, (p.comp (fderiv ℝ ψ k)) (fderiv ℝ A 0 h) = 0) ∧
      (FiniteDimensional ℝ (LinearMap.range (restrictedHessianRow B p)) →
        FiniteDimensional ℝ (LinearMap.range (hessianRow A (p.comp (fderiv ℝ ψ k)))))

private theorem actual_hessian (e : Frame M 2) (u : Control 2) (k : State)
    (R : Control 2 ≃ₗᵢ[ℝ] Controls) (A : Controls → State) (ψ : State → State)
    (a0 : A 0 = k) (ca : ContDiffAt ℝ 2 A 0) (cs : ContDiffAt ℝ 2 ψ k) (inv : (fderiv ℝ ψ k).IsInvertible)
    (graph : ∀ᶠ v in 𝓝 (0 : Control 2), ψ (A (R v)) ∈ e.chart.target ∧
      ∀ z, Segment e (u+v) (e.chart.symm k) z ↔ z = e.chart.symm (ψ (A (R v)))) :
    TerminalHessian e u k R A ψ := by
  intro B rep
  have eq : B =ᶠ[𝓝 0] ψ ∘ A := by
    filter_upwards [lift_neighborhood R.symm graph,rep] with w actual hB
    have z := congrArg e.chart ((actual.2 _).mp hB.2)
    rw [e.chart.right_inv hB.1,e.chart.right_inv actual.1,R.apply_symm_apply] at z
    exact z
  have chain (h l : Controls) := Transport.second_comp A ψ 0 h l ca (a0.symm ▸ cs)
  have same := (eq.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  rw [← same,a0] at chain
  have first := eq.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp 0 ((a0.symm ▸ cs).differentiableAt (by decide)) (ca.differentiableAt (by decide)),a0] at first
  refine ⟨eq,chain,fun p => ⟨nonzero_pullback inv,?_,fun hp => @finite_transport_row A B ψ k chain p hp⟩⟩
  intro annih h
  simpa only [first,ContinuousLinearMap.comp_apply] using annih h

/-- From any original rank-two chart segment, restrict to a nonempty final
interval and identify its endpoint for a full neighborhood of L² variations
with the time-one reference map applied to the moving ODE endpoint. The
moving columns have the spatial jets used by integral_endpoint_hessian. -/
theorem terminal_moving_endpoint_germ (e : Frame M 2) (w : Control 2) {x y : M}
    (seg : Segment e w x y) :
    ∃ (d r : ℝ) (u : Control 2) (k : State) (P : State → C(Time,State))
      (R : Control 2 ≃ₗᵢ[ℝ] Controls) (X : Columns State) (A : Controls → State),
      0 < d ∧ d ≤ 1 ∧ 0 < r ∧ k ∈ Metric.ball (e.chart y) (r/2) ∧
      (∀ᵐ t ∂volume.restrict (Icc (0:ℝ) 1), u t = d • w ((1-d)+d*t)) ∧
      ReferenceTube e (e.chart y) r u P ∧ P k (clamp 1) = e.chart y ∧
      (∀ v t, (R v) t = v t) ∧ Nonempty (SpatialJets X) ∧
      (∀ᶠ z in 𝓝 k, ∀ i t, X.Y i t z = pulledField e P i (clamp t) z) ∧
      A 0 = k ∧ X.Endpoint k A ∧ ContDiffAt ℝ 2 A 0 ∧
      (∀ᶠ v in 𝓝 (0 : Control 2), P (A (R v)) (clamp 1) ∈ e.chart.target ∧
        ∀ z, Segment e (u+v) (e.chart.symm k) z ↔
          z = e.chart.symm (P (A (R v)) (clamp 1))) ∧
      TerminalHessian e u k R A (fun z => P z (clamp 1)) ∧ d < 1 ∧ ∃ pre : Control 2,
        (∀ᵐ t ∂volume.restrict (Icc (0:ℝ) 1), pre t = (1-d) • w ((1-d)*t)) ∧
        Segment e pre x (e.chart.symm k) := by
  obtain ⟨d,r,u,k,P,hd,d1,hr,hk,rep,base,tube,stop,strict,pre⟩ := terminal_reference_tube e w seg
  have kr : k ∈ Metric.ball (e.chart y) r := (show dist k (e.chart y) < r/2 from hk).trans (half_lt_self hr)
  obtain ⟨X,⟨jets⟩,agree⟩ := localized_pulled_columns e tube kr
  obtain ⟨R,hR⟩ := control_signal_equiv
  obtain ⟨A,a0,endpoint,cA⟩ := exists_smooth_integral_endpoint X jets k
  let K := Metric.closedBall (e.chart y) r
  have kc : k ∈ K := Metric.ball_subset_closedBall kr
  have kt : k ∈ e.chart.target := tube.initial k kc ▸ tube.chart k kc (clamp 0)
  obtain ⟨G,_,graph⟩ := arbitrary_segment_graph e u _ y base 2 (by decide)
  rw [e.chart.right_inv kt] at graph
  have push : Tendsto (fun v : Control 2 => (k,u+v)) (𝓝 0) (𝓝 (k,u)) := by
    have c : Continuous (fun v : Control 2 => (k,u+v)) :=
      continuous_const.prodMk (continuous_const.add continuous_id)
    simpa only [add_zero] using c.tendsto (0 : Control 2)
  let ψ := fun z => P z (clamp 1)
  have result : ∀ᶠ v in 𝓝 (0 : Control 2), ψ (A (R v)) ∈ e.chart.target ∧
      ∀ z, Segment e (u+v) (e.chart.symm k) z ↔ z = e.chart.symm (ψ (A (R v))) := by
    filter_upwards [moving_segments_near e tube kr X jets agree R hR A endpoint,push graph] with v pert gr
    have onlyEnd := (gr.2.2 _).mp pert.2
    exact ⟨pert.1,fun z => (gr.2.2 z).trans (by rw [onlyEnd])⟩
  have eval : ContDiffAt ℝ 2 ψ k :=
    (@ContinuousLinearMap.contDiff ℝ _ C(Time,State) _ _ State _ _ 2
      (ContinuousMap.evalCLM ℝ (clamp 1))).contDiffAt.comp k ((tube.regular k kc).of_le (by decide))
  have inv : (fderiv ℝ ψ k).IsInvertible := by
    let E := (ContinuousMap.evalCLM ℝ (clamp 1) : C(Time,State) →L[ℝ] State)
    have der := E.hasFDerivAt.comp k ((tube.regular k kc).differentiableAt (by decide)).hasFDerivAt
    rw [show fderiv ℝ ψ k = E.comp (fderiv ℝ P k) from der.fderiv]
    exact tube.invertible k kc (clamp 1)
  exact ⟨d,r,u,k,P,R,X,A,hd,d1,hr,hk,rep,tube,stop,hR,⟨jets⟩,agree,a0,endpoint,cA,result,
    actual_hessian e u k R A ψ a0 cA eval inv result,strict,pre⟩

#print axioms terminal_moving_endpoint_germ
end MinimizingSard.Five
