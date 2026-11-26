import ControlledPathUniqueness
import EndpointComposition

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology ContDiff Manifold
namespace MinimizingSard.Five
open Volterra
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] {m n : ℕ}

private theorem transport_signals (U : Type) [NormedAddCommGroup U] [NormedSpace ℝ U]
    {μ ν : Measure ℝ} (eq : μ = ν) :
    ∃ R : Lp U 2 μ ≃ₗᵢ[ℝ] Lp U 2 ν, ∀ (v : Lp U 2 μ) (r : ℝ), (R v) r = v r := by
  subst ν
  exact ⟨LinearIsometryEquiv.refl _ _,fun _ _ => rfl⟩

private opaque frameSignalData (m : ℕ) :
    {R : Control m ≃ₗᵢ[ℝ] Causal.Signals (Fiber m) // ∀ (v : Control m) (r : ℝ), R v r = v r} :=
  let h := transport_signals (Fiber m) (show volume.restrict (Icc (0:ℝ) 1) = Causal.timeMeasure from
    Measure.restrict_congr_set Ioo_ae_eq_Icc.symm)
  ⟨h.choose,h.choose_spec⟩

def frameSignal (m : ℕ) : Control m ≃ₗᵢ[ℝ] Causal.Signals (Fiber m) := (frameSignalData m).val

theorem frameSignal_apply (v : Control m) (r : ℝ) : frameSignal m v r = v r := (frameSignalData m).property v r

def Frame.coefficient (e : Frame M m) (z : State) : Fiber m →L[ℝ] State :=
  ∑ i : Fin m, (ContinuousLinearMap.proj i).smulRight (e.X i z)

theorem Frame.coefficient_apply (e : Frame M m) (z : State) (a : Fiber m) :
    e.coefficient z a = e.velocity z a := by
  simp [Frame.coefficient,Frame.velocity,ContinuousLinearMap.sum_apply]

theorem Frame.coefficient_smooth (e : Frame M m) : ContDiffOn ℝ ∞ e.coefficient e.chart.target := by
  apply ContDiffOn.sum
  intro i _
  exact contDiffOn_const.smulRight (e.smooth i)

def Frame.Solves (e : Frame M m) (v : Control m) (q : State) (w : C(Time,State)) : Prop :=
  IsControlledPath e.chart.target e.coefficient (frameSignal m v) q w

theorem Frame.solves_unique (e : Frame M m) (u : Control m) (a : State) (w z : C(Time,State))
    (hw : e.Solves u a w) (hz : e.Solves u a z) : w = z :=
  controlled_path_unique _ e.chart.open_target e.coefficient (e.coefficient_smooth.of_le (by simp))
    (frameSignal m u) a w z hw hz

set_option maxHeartbeats 1000000 in
theorem segment_iff_frame_path (e : Frame M m) (u : Control m) (x y : M) :
    Segment e u x y ↔ x ∈ e.chart.source ∧ y ∈ e.chart.source ∧
      ∃ w : C(Time,State), e.Solves u (e.chart x) w ∧ w (clamp 1) = e.chart y := by
  constructor
  · rintro ⟨ex,ey,z,cz,inside,start,stop,_,eq⟩
    let w : C(Time,State) := ⟨fun t => z t,continuousOn_iff_continuous_restrict.mp cz⟩
    refine ⟨ex,ey,w,⟨fun t => inside t.property,?_⟩,?_⟩
    · intro t
      change z t = _
      rw [eq t t.property,start]
      congr 1
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le t.property.1] at hr
      have unit : r ∈ Icc (0:ℝ) 1 := ⟨hr.1,hr.2.trans t.property.2⟩
      simp only [frameSignal_apply,Frame.coefficient_apply,clamp,projIcc_of_mem zero_le_one unit]
      rfl
    · change z ((clamp 1):ℝ) = _
      simpa [clamp] using stop
  · rintro ⟨ex,ey,w,hw,stop⟩
    let f (r : ℝ) := w (clamp r)
    have start := hw.2 (clamp 0)
    have atZero : f 0 = e.chart x := by simpa [f,clamp] using start
    have co : Continuous (fun t : Time => e.coefficient (w t)) :=
      e.coefficient_smooth.continuousOn.comp_continuous w.continuous hw.1
    let D : C(Time,Fiber m →L[ℝ] State) := ⟨_,co⟩
    have integ := Volterra.intervalIntegrable D (frameSignal m u)
    have vel (r : ℝ) : D (clamp r) ((frameSignal m u) r) = e.velocity (f r) (u r) := by
      change e.coefficient (f r) _ = _
      rw [frameSignal_apply,Frame.coefficient_apply]
    refine ⟨ex,ey,f,(w.continuous.comp (show Continuous clamp from continuous_projIcc)).continuousOn,
      fun t _ => hw.1 (clamp t),atZero,stop,by simpa only [vel] using integ,?_⟩
    intro t ht
    have path := hw.2 (clamp t)
    have tr : ((clamp t):ℝ) = t := congrArg Subtype.val (projIcc_of_mem zero_le_one ht)
    rw [tr] at path
    simpa only [f,atZero,Frame.coefficient_apply,frameSignal_apply] using path

private theorem pull_path_family {Q U V Z : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {k : ℕ} (R : U ≃L[ℝ] V)
    (H : V → Q → Z → Prop) (q : Q) (u : U) (w : Z)
    (one : ∀ v a y z, H v a y → H v a z → y = z)
    (family : ∃ F : Q × V → Z, F (q,R u) = w ∧ ContDiffAt ℝ k F (q,R u) ∧
      ∀ᶠ p in 𝓝 (q,R u), H p.2 p.1 (F p)) :
    ∃ S : Q × U → Z, S (q,u) = w ∧ ContDiffAt ℝ k S (q,u) ∧
      ∀ᶠ p in 𝓝 (q,u), H (R p.2) p.1 (S p) ∧ ∀ z, H (R p.2) p.1 z → z = S p := by
  obtain ⟨F,fw,df,near⟩ := family
  let T : Q × U →L[ℝ] Q × V := (ContinuousLinearMap.id ℝ Q).prodMap R.toContinuousLinearMap
  have value : T (q,u) = (q,R u) := rfl
  have push : Tendsto T (𝓝 (q,u)) (𝓝 (q,R u)) := T.continuous.tendsto _
  refine ⟨F ∘ T,fw,df.comp (q,u) T.contDiff.contDiffAt,?_⟩
  filter_upwards [push near] with p h
  exact ⟨h,fun z hz => one _ _ z _ hz h⟩

set_option maxHeartbeats 1000000 in
/-- All smooth finite orders of dependence hold at the given original control
and moving initial state, in any horizontal rank. The family contains the
entire trajectory and is unique among all original-domain solutions. -/
theorem frame_path_family (e : Frame M m) (u : Control m) (q : State) (w : C(Time,State))
    (hw : e.Solves u q w) (k : ℕ) (hk : 1 ≤ k) :
    ∃ S : State × Control m → C(Time,State), S (q,u) = w ∧ ContDiffAt ℝ k S (q,u) ∧
      ∀ᶠ p in 𝓝 (q,u), e.Solves p.2 p.1 (S p) ∧ ∀ z, e.Solves p.2 p.1 z → z = S p := by
  have zero : w (clamp 0) = q := by simpa [clamp] using hw.2 (clamp 0)
  apply pull_path_family (frameSignal m).toContinuousLinearEquiv (IsControlledPath e.chart.target e.coefficient) q u w
  · exact fun v a y z => controlled_path_unique _ e.chart.open_target _ (e.coefficient_smooth.of_le (by simp)) v a y z
  · have family := controlled_path_family hk _ e.chart.open_target e.coefficient
      (e.coefficient_smooth.of_le (mod_cast (le_top : (k:ℕ∞) ≤ ⊤))) (frameSignal m u) w hw.1
      (fun t => by rw [zero]; exact hw.2 t)
    rwa [zero] at family

theorem frame_segment_graph (e : Frame M m) (u : Control m) (x y : M) (seg : Segment e u x y)
    (k : ℕ) (hk : 1 ≤ k) : HasSmoothSegmentGraph e k (e.chart x,u) := by
  obtain ⟨ex,_,w,hw,_⟩ := (segment_iff_frame_path e u x y).mp seg
  obtain ⟨S,root,ds,near⟩ := frame_path_family e u (e.chart x) w hw k hk
  let F (p : State × Control m) := S p (clamp 1)
  let ev : C(Time,State) →L[ℝ] State := ContinuousMap.evalCLM ℝ (clamp 1)
  have df : ContDiffAt ℝ k F (e.chart x,u) := ev.contDiff.contDiffAt.comp (e.chart x,u) ds
  refine ⟨F,df,?_⟩
  filter_upwards [near,continuousAt_fst (e.chart.open_target.mem_nhds (e.chart.map_source ex))] with p hp inside
  have out : F p ∈ e.chart.target := hp.1.1 (clamp 1)
  refine ⟨inside,out,fun z => ?_⟩
  rw [segment_iff_frame_path,e.chart.right_inv inside]
  constructor
  · rintro ⟨_,ez,v,hv,vz⟩
    rw [hp.2 v hv] at vz
    exact (e.chart.left_inv ez).symm.trans (congrArg e.chart.symm vz.symm)
  · rintro rfl
    exact ⟨e.chart.map_target inside,e.chart.map_target out,S p,hp.1,(e.chart.right_inv out).symm⟩

theorem all_rank_path_endpoint [IsManifold 𝓘(ℝ,State) ∞ M]
    (e : Fin n → Frame M m) (u : Fin n → Control m) (x y : M) (path : Joins e u x y)
    (c : OpenPartialHomeomorph M State) (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (hy : y ∈ c.source)
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ F : (Fin n → Control m) → State, F u = c y ∧ ContDiffAt ℝ k F u ∧
      (∀ᶠ v in 𝓝 u, F v ∈ c.target ∧ ∀ z, Joins e v x z ↔ z = c.symm (F v)) ∧
      (Singular e u x y ↔ ¬ Function.Surjective (fderiv ℝ F u)) :=
  path_endpoint_of_segment_graphs e u x y path c hc hy k (by exact_mod_cast hk)
    (fun d v s t h => frame_segment_graph d v s t h k hk)

#print axioms segment_iff_frame_path
#print axioms frame_path_family
#print axioms all_rank_path_endpoint
end MinimizingSard.Five
