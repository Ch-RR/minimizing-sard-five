import BracketWordRepair
import ActualFrameFlow

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace MinimizingSard.Five
open Volterra

private abbrev μ := volume.restrict (Icc (0:ℝ) 1)
variable {m : ℕ}
private def unitInput (i : Fin m) (s : ℝ) : Fiber m := Pi.single i s
def framePulse (i : Fin m) (s : ℝ) : Control m := Lp.const 2 μ (unitInput i s)

theorem smooth_pulse (i : Fin m) (n : ℕ) : ContDiff ℝ n (framePulse i) := by
  apply (Lp.constL 2 μ ℝ : Fiber m →L[ℝ] Control m).contDiff.comp
  apply contDiff_pi.mpr
  intro j
  by_cases h : j = i
  · subst j
    simpa [unitInput] using (contDiff_id : ContDiff ℝ n (id : ℝ → ℝ))
  · simpa [unitInput,Pi.single_eq_of_ne h] using (contDiff_const : ContDiff ℝ n (fun _ : ℝ => (0:ℝ)))

theorem pulse_zero (i : Fin m) : framePulse i 0 = 0 := by simp [framePulse,unitInput]

theorem reverse_pulse (i : Fin m) (t : ℝ) : reverseControl (framePulse i t) = framePulse i (-t) := by
  rw [framePulse,reverseControl_const]
  congr 1
  ext j
  by_cases h : j = i <;> simp [unitInput,Pi.single_apply,h]

theorem pulse_length (i : Fin m) (t : ℝ) : length (fun _ : Fin 1 => framePulse i t) = |t| := by
  have hs : ∀ᵐ s ∂volume.restrict (uIoc (0:ℝ) 1), Real.sqrt (speedSq (framePulse i t s)) = |t| := by
    rw [uIoc_of_le zero_le_one,Measure.restrict_congr_set Ioc_ae_eq_Icc]
    filter_upwards [Lp.coeFn_const 2 μ (unitInput i t)] with s h
    change framePulse i t s = unitInput i t at h
    rw [h]
    simp [unitInput,speedSq,Pi.single_apply,ite_pow,Real.sqrt_sq_eq_abs]
  simp only [length,Fin.sum_univ_one,intervalIntegral.integral_congr_ae_restrict hs]
  simp

def meanPath : C(Time,State) →L[ℝ] State := by
  let m : C(Time,State) →ₗ[ℝ] State := {
    toFun := fun z => ∫ s in (0:ℝ)..1, z (clamp s)
    map_add' := fun f g => intervalIntegral.integral_add
      ((f.continuous.comp continuous_projIcc).intervalIntegrable _ _) ((g.continuous.comp continuous_projIcc).intervalIntegrable _ _)
    map_smul' := fun c z => intervalIntegral.integral_smul c (fun s => z (clamp s))
  }
  apply m.mkContinuous 1
  intro z
  simpa [m] using intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 1) (fun s _ => z.norm_coe_le_norm (clamp s))

def liftField {V G : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (f : V → G) (cf : Continuous f) : C(Time × V,G) :=
  ⟨fun p => f p.2,cf.comp continuous_snd⟩

theorem field_order {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ) {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : V → G) (cf : ContDiff ℝ n f) : PathCalculus.SpatialOrder n (liftField f cf.continuous) := by
  induction n generalizing G with
  | zero => trivial
  | succ n ih =>
    have cd : ContDiff ℝ n (fderiv ℝ f) := cf.fderiv_right (by simp)
    exact ⟨liftField _ cd.continuous,fun _ z => (cf.differentiable (by simp) z).hasFDerivAt,ih _ cd⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M]

/-- Actual endpoint and normalized displacement along each signed generator pulse. -/
def HasGeneratorProfiles {m : ℕ} (e : Frame M m) : Prop :=
  ∀ {q : State}, q ∈ e.chart.target → ∀ (i : Fin m) (n : ℕ), 1 ≤ (n : WithTop ℕ∞) →
    ∃ F Z : State × ℝ → State, ContDiffAt ℝ n F (q,0) ∧ ContDiffAt ℝ n Z (q,0) ∧
      F (q,0) = q ∧ (∀ᶠ z in 𝓝 q, Z (z,0) = e.X i z) ∧
      ∀ᶠ p in 𝓝 (q,(0:ℝ)), F p = p.1+p.2 • Z p ∧ F p ∈ e.chart.target ∧
        ∀ y, Segment e (framePulse i p.2) (e.chart.symm p.1) y ↔ y = e.chart.symm (F p)

/-- A smooth normalized displacement for an actual frame generator, with the initial
coefficient equal to the generator at the center. The graph quantifies over every
endpoint of the original integral equation for the constant coordinate control. -/
theorem generator_flow_profile (e : Frame M 2) {q : State} (inside : q ∈ e.chart.target) (i : Fin 2)
    (n : ℕ) (hn : 1 ≤ (n : WithTop ℕ∞)) :
    ∃ F Z : State × ℝ → State, ContDiffAt ℝ n F (q,0) ∧ ContDiffAt ℝ n Z (q,0) ∧
      F (q,0) = q ∧ (∀ᶠ z in 𝓝 q, Z (z,0) = e.X i z) ∧
      ∀ᶠ p in 𝓝 (q,(0:ℝ)), F p = p.1+p.2 • Z p ∧ F p ∈ e.chart.target ∧
        ∀ y, Segment e (framePulse i p.2) (e.chart.symm p.1) y ↔ y = e.chart.symm (F p) := by
  obtain ⟨S,cs,rest,run⟩ := small_chart_path_family e inside n hn
  obtain ⟨G,g0,cg,graph⟩ := small_segment_endpoint e inside n hn
  obtain ⟨Y,cy,matchY⟩ := smooth_germ_extension e.chart.open_target inside (e.X i) (e.smooth i)
  let T (p : State × ℝ) := (p.1-q,framePulse i p.2)
  have t0 : T (q,0) = 0 := by simp [T,pulse_zero]
  have ct : ContDiff ℝ n T := (contDiff_fst.sub contDiff_const).prodMk ((smooth_pulse i n).comp contDiff_snd)
  have push : Tendsto T (𝓝 (q,0)) (𝓝 0) := t0 ▸ ct.continuous.tendsto (q,0)
  let P := S ∘ T
  have cp : ContDiffAt ℝ n P (q,0) := (t0.symm ▸ cs).comp (q,0) ct.contDiffAt
  have s0 : P (q,0) = ContinuousMap.const Time q := by
    simpa [P,t0] using rest.self_of_nhds
  let Z := meanPath ∘ PathCalculus.subst (liftField Y cy.continuous) ∘ P
  have cz : ContDiffAt ℝ n Z (q,0) := meanPath.contDiff.contDiffAt.comp (q,0)
    ((PathCalculus.contDiff_subst_of_spatialOrder n _ (field_order n Y (cy.of_le (mod_cast (le_top : (n : ℕ∞) ≤ ⊤))))).contDiffAt.comp (q,0) cp)
  have shift : Tendsto (fun z : State => z-q) (𝓝 q) (𝓝 0) := by
    simpa using (continuous_id.sub (continuous_const (y := q))).tendsto q
  have z0 : ∀ᶠ z in 𝓝 q, Z (z,0) = e.X i z := by
    filter_upwards [shift rest,matchY] with z h hy
    have idle : P (z,0) = ContinuousMap.const Time z := by simpa [P,T,pulse_zero] using h
    change (∫ s in (0:ℝ)..1, Y (P (z,0) (clamp s))) = _
    simp [idle,hy]
  let F := G ∘ T
  refine ⟨F,Z,(t0.symm ▸ cg).comp (q,0) ct.contDiffAt,cz,by simp [F,t0,g0],z0,?_⟩
  obtain ⟨r,hr,ball⟩ := Metric.mem_nhds_iff.mp matchY
  have close : ∀ᶠ p in 𝓝 (q,(0:ℝ)), dist (P p) (ContinuousMap.const Time q) < r :=
    (cp.continuousAt.dist continuousAt_const).eventually_lt_const (by simpa [s0] using hr)
  filter_upwards [push graph,push run,close] with p h run near
  change _ ∧ F p ∈ e.chart.target ∧ ∀ y, Segment e (framePulse i p.2) (e.chart.symm (q+(p.1-q))) y ↔ _ at h
  rw [add_sub_cancel] at h
  have same (t : Time) : Y (P p t) = e.X i (P p t) := ball ((ContinuousMap.dist_apply_le_dist t).trans_lt near)
  let z (s : ℝ) := P p (clamp s)
  have cont : Continuous z := (P p).continuous.comp continuous_projIcc
  have vel : ∀ᵐ s ∂μ, e.velocity (z s) (framePulse i p.2 s) = p.2 • Y (z s) := by
    filter_upwards [Lp.coeFn_const 2 μ (unitInput i p.2)] with s hs
    change framePulse i p.2 s = unitInput i p.2 at hs
    simp [hs,Frame.velocity,unitInput,Pi.single_apply,← same (clamp s),z,ite_smul]
  have eq (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : z t = p.1 + ∫ s in (0:ℝ)..t, e.velocity (z s) (framePulse i p.2 s) := by
    simpa [z,P,T] using run.2 t ht
  have start : z 0 = p.1 := by simpa using eq 0 (by norm_num)
  have rv : (fun s => e.velocity (z s) (framePulse i p.2 s)) =ᵐ[volume.restrict (uIoc (0:ℝ) 1)] (fun s => p.2 • Y (z s)) := by
    simpa only [uIoc_of_le zero_le_one,Measure.restrict_congr_set Ioc_ae_eq_Icc] using vel
  have hEnd : z 1 ∈ e.chart.target := run.1 (clamp 1)
  have seg : Segment e (framePulse i p.2) (e.chart.symm p.1) (e.chart.symm (z 1)) :=
    ⟨e.chart.map_target h.1,e.chart.map_target hEnd,z,cont.continuousOn,fun t _ => run.1 (clamp t),
      start.trans (e.chart.right_inv h.1).symm,(e.chart.right_inv hEnd).symm,
      (intervalIntegrable_congr_ae rv).mpr (((cy.continuous.comp cont).const_smul p.2).intervalIntegrable 0 1),
      fun t ht => by rw [start]; exact eq t ht⟩
  have id := e.chart.symm.injOn hEnd h.2.1 ((h.2.2 _).mp seg)
  refine ⟨id ▸ ?_,h.2⟩
  rw [eq 1 (by norm_num),intervalIntegral.integral_congr_ae_restrict rv,intervalIntegral.integral_smul]
  rfl

#print axioms generator_flow_profile

/-- Each original generator supplies a repair word of order one, at unit cost
per unit of time, without any local-flow or length assumptions. -/
theorem generator_repair_word (Γ : Geometry M 2) (e : Frame M 2) (he : e ∈ Γ.frames)
    {q : State} (inside : q ∈ e.chart.target) (i : Fin 2) :
    ∃ W : RepairWord Γ e.chart q, W.order = 1 ∧ W.cost = 1 ∧
      ∀ᶠ z in 𝓝 q, W.profile (z,0) = e.X i z := by
  obtain ⟨F,Z,cf,cz,f0,z0,near⟩ := generator_flow_profile e inside i 1 (by simp)
  let rev (p : State × ℝ) := (p.1,-p.2)
  let B := F ∘ rev
  have r0 : rev (q,0) = (q,0) := by simp [rev]
  have cr : ContDiff ℝ 1 rev := contDiff_fst.prodMk contDiff_snd.neg
  have cb : ContDiffAt ℝ 1 B (q,0) := (r0.symm ▸ cf).comp (q,0) cr.contDiffAt
  have b0 : B (q,0) = q := by simp [B,r0,f0]
  have tr : Tendsto rev (𝓝 (q,0)) (𝓝 (q,0)) := by simpa only [r0] using cr.continuous.tendsto (q,0)
  have tb : Tendsto (fun p : State × ℝ => (B p,p.2)) (𝓝 (q,0)) (𝓝 (q,0)) := by
    simpa only [b0] using cb.continuousAt.tendsto.prodMk_nhds (continuous_snd.continuousAt (x := (q,(0:ℝ)))).tendsto
  have undo : ∀ᶠ p in 𝓝 (q,(0:ℝ)), F (B p,p.2) = p.1 := by
    filter_upwards [tr near,tb near,continuous_fst.continuousAt.tendsto (e.chart.open_target.mem_nhds inside)]
      with p backward forward hp
    have path : Segment e (framePulse i (-p.2)) (e.chart.symm p.1) (e.chart.symm (B p)) := (backward.2.2 _).mpr rfl
    have back := segment_reverse path
    rw [reverse_pulse,neg_neg] at back
    exact e.chart.symm.injOn forward.2.1 hp ((forward.2.2 _).mp back).symm
  refine ⟨⟨1,by decide,by decide,F,B,Z,cz,cb,b0,?_,undo,1,zero_le_one,?_⟩,rfl,rfl,z0⟩
  · filter_upwards [near] with p h using by simpa using h.1
  · filter_upwards [near] with p h
    intro pos
    have seg := (h.2.2 _).mpr rfl
    refine ⟨|p.2|,⟨0,fun _ => e,fun _ => framePulse i p.2,fun _ => he,
      ⟨![e.chart.symm p.1,e.chart.symm (F p)],rfl,rfl,?_⟩,pulse_length i p.2⟩,by simp [abs_of_nonneg pos]⟩
    intro j
    fin_cases j
    exact seg

#print axioms generator_repair_word
end MinimizingSard.Five
