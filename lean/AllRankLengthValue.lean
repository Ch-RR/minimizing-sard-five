import ArbitraryFrameEndpoint
import CorankOneLength

noncomputable section
open Set Filter MeasureTheory IsManifold Metric
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
open Volterra
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] {m : ℕ}

private theorem const_frame_path (e : Frame M m) (q : State) (hq : q ∈ e.chart.target) :
    e.Solves 0 q (ContinuousMap.const Time q) := by
  refine ⟨fun _ => hq,fun t => ?_⟩
  let B := ContinuousMap.const Time (e.coefficient q)
  change q = q + ∫ r in (0:ℝ)..(t:ℝ), B (clamp r) ((frameSignal m 0) r)
  rw [← operator_eq_interval,map_zero,map_zero]
  simp

theorem all_frame_generator_profiles (e : Frame M m) : HasGeneratorProfiles e := by
  intro q hq i n hn
  obtain ⟨S,s₀,cs,near⟩ := frame_path_family e 0 q _ (const_frame_path e q hq) n (by exact_mod_cast hn)
  obtain ⟨Y,cy,agree⟩ := smooth_germ_extension e.chart.open_target hq (e.X i) (e.smooth i)
  let T (p : State × ℝ) := (p.1,framePulse i p.2)
  have t₀ : T (q,0) = (q,0) := by simp [T,pulse_zero]
  have ct : ContDiff ℝ n T := contDiff_fst.prodMk ((smooth_pulse i n).comp contDiff_snd)
  have push : Tendsto T (𝓝 (q,0)) (𝓝 (q,0)) := t₀ ▸ ct.continuous.tendsto (q,0)
  let P := S ∘ T
  have cp : ContDiffAt ℝ n P (q,0) := (t₀.symm ▸ cs).comp _ ct.contDiffAt
  have p₀ : P (q,0) = ContinuousMap.const Time q := (congrArg S t₀).trans s₀
  let Z := meanPath ∘ pathField Y cy.continuous ∘ P
  have cz : ContDiffAt ℝ n Z (q,0) := meanPath.contDiff.contDiffAt.comp _
    ((pathField_smooth Y (cy.of_le (mod_cast (le_top : (n:ℕ∞) ≤ ⊤)))).contDiffAt.comp _ cp)
  let F (p : State × ℝ) := P p (clamp 1)
  let ev : C(Time,State) →L[ℝ] State := ContinuousMap.evalCLM ℝ (clamp 1)
  have cf : ContDiffAt ℝ n F (q,0) := ev.contDiff.contDiffAt.comp (q,0) cp
  have tIdle : Tendsto (fun z : State => (z,(0:Control m))) (𝓝 q) (𝓝 (q,0)) :=
    tendsto_id.prodMk_nhds tendsto_const_nhds
  refine ⟨F,Z,cf,cz,by simp [F,p₀],?_,?_⟩
  · filter_upwards [tIdle near,agree,e.chart.open_target.mem_nhds hq] with z h hz ins
    have idle : P (z,0) = ContinuousMap.const Time z := by
      simpa only [P,Function.comp_apply,T,pulse_zero] using (h.2 _ (const_frame_path e z ins)).symm
    change (∫ s in (0:ℝ)..1, Y (P (z,0) (clamp s))) = _
    simp [idle,hz]
  obtain ⟨r,rp,ball⟩ := Metric.mem_nhds_iff.mp agree
  have close : ∀ᶠ p in 𝓝 (q,(0:ℝ)), dist (P p) (ContinuousMap.const Time q) < r :=
    (cp.continuousAt.dist continuousAt_const).eventually_lt_const (by simpa [p₀] using rp)
  filter_upwards [push near,close,continuousAt_fst (e.chart.open_target.mem_nhds hq)] with p hp around src
  have same (t : Time) : Y (P p t) = e.X i (P p t) := ball ((ContinuousMap.dist_apply_le_dist t).trans_lt around)
  have out := hp.1.1 (clamp 1)
  have val := hp.1.2 (clamp 1)
  have t₁ : ((clamp 1):ℝ) = 1 := by simp [clamp]
  rw [t₁] at val
  have vel : (fun r => e.coefficient (P p (clamp r)) (frameSignal m (framePulse i p.2) r)) =ᵐ[volume.restrict (uIoc (0:ℝ) 1)]
      (fun r => p.2 • Y (P p (clamp r))) := by
    rw [uIoc_of_le zero_le_one,Measure.restrict_congr_set Ioc_ae_eq_Icc]
    filter_upwards [Lp.coeFn_const 2 (volume.restrict (Icc (0:ℝ) 1)) ((Pi.single i p.2 : Fiber m))] with r h
    change framePulse i p.2 r = (Pi.single i p.2 : Fiber m) at h
    simp [Frame.coefficient_apply,frameSignal_apply,h,Frame.velocity,Pi.single_apply,ite_smul,same]
  refine ⟨?_,out,fun y => ?_⟩
  · change F p = p.1 + ∫ r in (0:ℝ)..1, e.coefficient (P p (clamp r)) (frameSignal m (framePulse i p.2) r) at val
    rwa [intervalIntegral.integral_congr_ae_restrict vel,intervalIntegral.integral_smul] at val
  · rw [segment_iff_frame_path,e.chart.right_inv src]
    constructor
    · rintro ⟨_,ey,v,hv,vy⟩
      rw [hp.2 v hv] at vy
      exact (e.chart.left_inv ey).symm.trans (congrArg e.chart.symm vy.symm)
    · rintro rfl
      exact ⟨e.chart.map_target src,e.chart.map_target out,P p,hp.1,(e.chart.right_inv out).symm⟩

theorem all_rank_value_repair [IsManifold 𝓘(ℝ,State) ∞ M] (Γ : Geometry M m) (hm : 2 ≤ m)
    (c : OpenPartialHomeomorph M State) (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) :
    ∀ᵐ q : State, q ∈ c.target → ∀ x : M, (attainableLengths Γ x (c.symm q)).Nonempty →
      let D := fun z => pointedLengthValue Γ x (c.symm z)
      (∃ V : Set State, IsOpen V ∧ q ∈ V ∧ ContinuousOn D V) ∧
      ∃ K : ℝ, ∀ᶠ p : State × State in 𝓝 (q,q), |D p.2-D p.1| ≤ K*‖p.2-p.1‖^(1/4:ℝ) :=
  ae_compatible_chart_value_of_profiles Γ hm (fun e _ => all_frame_generator_profiles e) c hc

#print axioms all_frame_generator_profiles
#print axioms all_rank_value_repair
theorem all_rank_corank_one_multiplier
    [IsManifold 𝓘(ℝ,State) ∞ M] (Γ : Geometry M m) (hm : 2 ≤ m) (x : M)
    (chart : OpenPartialHomeomorph M State) (hc : chart ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) :
    ∀ᵐ q : State, q ∈ chart.target → ∀ {n : ℕ} (d : Fin (n+1) → Frame M m)
      (w : Fin (n+1) → Control m) (G : (Fin (n+1) → Control m) → State),
      let y := chart.symm q
      (∀ i, d i ∈ Γ.frames) → Joins d w x y →
      (∀ (k : ℕ) (a : Fin (k+1) → Frame M m) (b : Fin (k+1) → Control m),
        (∀ i, a i ∈ Γ.frames) → Joins a b x y → length w ≤ length b) →
      (∀ᶠ b in 𝓝 w, G b ∈ chart.target ∧ ∀ z, Joins d b x z ↔ z = chart.symm (G b)) →
      Module.finrank ℝ (LinearMap.range (fderiv ℝ G w).toLinearMap) = 4 →
      HasCostMultiplier length (fderiv ℝ G w) w :=
  ae_corank_one_of_germs Γ x chart hc ((all_rank_value_repair Γ hm chart hc).mono
    (fun _ h hq reach => (h hq x reach).1)) (fun e v a b seg => frame_segment_graph e v a b seg 4 (by decide))

#print axioms all_rank_corank_one_multiplier
end MinimizingSard.Five
