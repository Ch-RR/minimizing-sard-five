import MovingIntegralEquation

noncomputable section
open Set
open scoped Topology
namespace MinimizingSard.Five
open Volterra

variable {V W Z : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
variable {K : Set State}

private abbrev Joint (K : Set State) (f : Time → State → V) :=
  Continuous (fun p : Time × K => f p.1 p.2)

private structure First (K : Set State) (f : Time → State → V) where
  D : Time → State → State →L[ℝ] V
  value : Joint K f
  derivative : Joint K D
  rule : ∀ t x, x ∈ K → HasFDerivAt (f t) (D t x) x

private def First.pair {f : Time → State → V} {g : Time → State → W}
    (a : First K f) (b : First K g) : First K (fun t x => (f t x,g t x)) where
  D t x := (a.D t x).prod (b.D t x)
  value := a.value.prodMk b.value
  derivative := continuous_clm_apply.mpr fun h =>
    (a.derivative.clm_apply (continuous_const (y := h))).prodMk (b.derivative.clm_apply continuous_const)
  rule t x hx := (a.rule t x hx).prodMk (b.rule t x hx)

private def First.post {f : Time → State → V} (a : First K f) (g : V → W)
    (hg : ∀ t x, x ∈ K → ContDiffAt ℝ 1 g (f t x)) :
    First K (fun t x => g (f t x)) where
  D t x := (fderiv ℝ g (f t x)).comp (a.D t x)
  value := continuous_iff_continuousAt.mpr fun p =>
    (hg p.1 p.2 p.2.2).continuousAt.comp (f := fun p : Time × K => f p.1 p.2) a.value.continuousAt
  derivative := by
    have c : Joint K (fun t x => fderiv ℝ g (f t x)) :=
      continuous_iff_continuousAt.mpr fun p =>
        ((hg p.1 p.2 p.2.2).fderiv_right (m := 0) (by decide)).continuousAt.comp
          (f := fun p : Time × K => f p.1 p.2) a.value.continuousAt
    exact c.clm_comp a.derivative
  rule t x hx := ((hg t x hx).differentiableAt (by decide)).hasFDerivAt.comp x (a.rule t x hx)

/-- The finite-dimensional input allows operator-norm continuity in time
to be tested on fixed vectors. Evaluation need not itself vary in norm. -/
private def sliceMap (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    (State →L[ℝ] C(Time,V)) →L[ℝ] C(Time,State →L[ℝ] V) := by
  let L : (State →L[ℝ] C(Time,V)) →ₗ[ℝ] C(Time,State →L[ℝ] V) :=
    { toFun := fun A => ⟨fun t => (ContinuousMap.evalCLM ℝ t).comp A,
        continuous_clm_apply.mpr fun h => (A h).continuous⟩
      map_add' := fun A B => by ext t h; rfl
      map_smul' := fun c A => by ext t h; rfl }
  have bound (A) : ‖L A‖ ≤ 1 * ‖A‖ := by
    rw [one_mul]
    apply (ContinuousMap.norm_le (L A) (norm_nonneg A)).mpr
    intro t
    exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun h =>
      ((A h).norm_coe_le_norm t).trans (A.le_opNorm h)
  exact LinearMap.mkContinuous (E := State →L[ℝ] C(Time,V)) (F := C(Time,State →L[ℝ] V))
    (σ := RingHom.id ℝ) L 1 bound

private theorem sliceSmooth (n : ℕ) : ContDiff ℝ n (sliceMap V) :=
  @ContinuousLinearMap.contDiff ℝ _ (State →L[ℝ] C(Time,V)) _ _ (C(Time,State →L[ℝ] V)) _ _ n _

private def pathFirst (P : State → C(Time,V)) (hp : ∀ x ∈ K, ContDiffAt ℝ 1 P x) :
    First K (fun t x => P x t) where
  D t x := (ContinuousMap.evalCLM ℝ t).comp (fderiv ℝ P x)
  value := by
    have c : Continuous (fun x : K => P x) := continuousOn_iff_continuous_restrict.mp
      fun x hx => (hp x hx).continuousAt.continuousWithinAt
    exact continuous_eval.comp ((c.comp continuous_snd).prodMk continuous_fst)
  derivative := by
    let B := fun x => sliceMap V (fderiv ℝ P x)
    have c : Continuous (fun x : K => B x) := continuousOn_iff_continuous_restrict.mp
      fun x hx => ((sliceMap V).continuous.continuousAt.comp
        ((hp x hx).fderiv_right (m := 0) (by decide)).continuousAt).continuousWithinAt
    exact continuous_eval.comp ((c.comp continuous_snd).prodMk continuous_fst)
  rule t x hx := (ContinuousMap.evalCLM ℝ t : C(Time,V) →L[ℝ] V).hasFDerivAt.comp x
    ((hp x hx).differentiableAt (by decide)).hasFDerivAt

private structure Second (K : Set State) (f : Time → State → V) where
  first : First K f
  next : First K first.D

private def pathSecond (P : State → C(Time,V)) (hp : ∀ x ∈ K, ContDiffAt ℝ 2 P x) :
    Second K (fun t x => P x t) :=
  ⟨pathFirst P (fun x hx => (hp x hx).of_le (by decide)),
   pathFirst (fun x => sliceMap V (fderiv ℝ P x)) (fun x hx =>
     (sliceSmooth 1).contDiffAt.comp x ((hp x hx).fderiv_right (m := 1) (by decide)))⟩

private def Second.pair {f : Time → State → V} {g : Time → State → W}
    (a : Second K f) (b : Second K g) : Second K (fun t x => (f t x,g t x)) := by
  refine ⟨a.first.pair b.first,?_⟩
  let pack := fun p : (State →L[ℝ] V) × (State →L[ℝ] W) => p.1.prod p.2
  have smooth : ContDiff ℝ 1 pack := by
    let left := ContinuousLinearMap.inl ℝ V W
    let right := ContinuousLinearMap.inr ℝ V W
    have h : ContDiff ℝ 1 (fun p : (State →L[ℝ] V) × (State →L[ℝ] W) =>
        left.comp p.1 + right.comp p.2) :=
      (contDiff_const.clm_comp contDiff_fst).add (contDiff_const.clm_comp contDiff_snd)
    have eq : pack = fun p : (State →L[ℝ] V) × (State →L[ℝ] W) => left.comp p.1 + right.comp p.2 := by
      funext p
      ext v <;> simp [pack,left,right]
    rwa [eq]
  exact (a.next.pair b.next).post pack (fun _ _ _ => smooth.contDiffAt)

private def Second.post {f : Time → State → V} (a : Second K f) (g : V → W)
    (hg : ∀ t x, x ∈ K → ContDiffAt ℝ 2 g (f t x)) :
    Second K (fun t x => g (f t x)) := by
  refine ⟨a.first.post g (fun t x hx => (hg t x hx).of_le (by decide)),?_⟩
  let left := a.first.post (fderiv ℝ g) (fun t x hx => (hg t x hx).fderiv_right (by decide))
  let combine := fun p : (V →L[ℝ] W) × (State →L[ℝ] V) => p.1.comp p.2
  have smooth : ContDiff ℝ 1 combine := contDiff_fst.clm_comp contDiff_snd
  exact (left.pair a.next).post combine (fun _ _ _ => smooth.contDiffAt)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M]

def pulledField (e : Frame M 2) (P : State → C(Time, State)) (i : Fin 2)
    (t : Time) (x : State) : State :=
  ((ContinuousMap.evalCLM ℝ t).comp (fderiv ℝ P x)).inverse (e.X i (P x t))

private def pulledSecond (e : Frame M 2) {q r u P} (tube : ReferenceTube e q r u P)
    (i : Fin 2) (b : State → State) (cb : ContDiff ℝ 2 b)
    (inside : MapsTo b K (Metric.closedBall q r)) : Second K (fun t x => pulledField e P i t (b x)) := by
  let val := pathSecond (fun x => P (b x)) (fun x hx =>
    ((tube.regular _ (inside hx)).of_le (show (2 : WithTop ℕ∞) ≤ 3 by decide)).comp x cb.contDiffAt)
  let jac := pathSecond (K := K) (fun x => sliceMap State (fderiv ℝ P (b x)))
    (fun x hx => (sliceSmooth 2).contDiffAt.comp x
      (((tube.regular _ (inside hx)).fderiv_right (m := 2) (by decide)).comp x cb.contDiffAt))
  let data := val.pair jac
  let g := fun p : State × (State →L[ℝ] State) => p.2.inverse (e.X i p.1)
  have sm (t x) (hx : x ∈ K) :
      ContDiffAt ℝ 2 g (P (b x) t, (ContinuousMap.evalCLM ℝ t).comp (fderiv ℝ P (b x))) := by
    have sx : ContDiffAt ℝ 2 (e.X i) (P (b x) t) :=
      ((e.smooth i).contDiffAt (e.chart.open_target.mem_nhds (tube.chart _ (inside hx) t))).of_le (by decide)
    let p : State × (State →L[ℝ] State) := (P (b x) t,(ContinuousMap.evalCLM ℝ t).comp (fderiv ℝ P (b x)))
    exact (((tube.invertible _ (inside hx) t).contDiffAt_map_inverse.comp p contDiffAt_snd).clm_apply
      (sx.comp p contDiffAt_fst))
  exact data.post g sm

/-- On the entire reference ball the actual pulled columns have two spatial
derivatives jointly continuous with time. No time derivative is required. -/
theorem pulled_field_spatial_jets (e : Frame M 2) {q r u P} (tube : ReferenceTube e q r u P)
    (i : Fin 2) :
    ∃ (J : Time → State → State →L[ℝ] State) (H : Time → State → State →L[ℝ] State →L[ℝ] State),
      Continuous (fun p : Time × Metric.closedBall q r => pulledField e P i p.1 p.2) ∧
      Continuous (fun p : Time × Metric.closedBall q r => J p.1 p.2) ∧
      Continuous (fun p : Time × Metric.closedBall q r => H p.1 p.2) ∧
      ∀ t x, x ∈ Metric.closedBall q r →
        HasFDerivAt (pulledField e P i t) (J t x) x ∧ HasFDerivAt (J t) (H t x) x := by
  let a := pulledSecond e tube i id contDiff_id (mapsTo_id _)
  exact ⟨a.first.D,a.next.D,a.first.value,a.first.derivative,a.next.derivative,
    fun t x hx => ⟨a.first.rule t x hx,a.next.rule t x hx⟩⟩

#print axioms pulled_field_spatial_jets

open PulseGeometry

/-- A smooth change of the spatial argument keeps all points inside the
reference ball and agrees with the identity on a neighborhood of k. -/
private theorem localize_argument {q k : State} {r : ℝ} (hk : k ∈ Metric.ball q r) :
    ∃ b : State → State, ContDiff ℝ 2 b ∧ (∀ x, b x ∈ Metric.closedBall q r) ∧ b =ᶠ[𝓝 k] id := by
  obtain ⟨w,supp,_,cw,_,wk⟩ := exists_smooth_tsupport_subset (Metric.isOpen_ball.mem_nhds hk)
  let a : ContDiffBump (1:ℝ) := ⟨1/4,1/2,by norm_num,by norm_num⟩
  have a0 : a 0 = 0 := a.zero_of_le_dist (by change (1/2:ℝ) ≤ dist 0 1; norm_num)
  let b (x : State) := q + a (w x) • (x-q)
  have hr : 0 < r := (dist_nonneg.trans_lt (show dist k q < r from hk))
  refine ⟨b,contDiff_const.add ((a.contDiff.comp cw).of_le (by decide) |>.smul
    (contDiff_id.sub contDiff_const)),?_,?_⟩
  · intro x
    by_cases h : x ∈ tsupport w
    · have small : ‖x-q‖ ≤ r := (show dist x q < r from supp h).le
      change ‖q + a (w x) • (x-q) - q‖ ≤ r
      rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg a.nonneg]
      exact (mul_le_of_le_one_left (norm_nonneg _) a.le_one).trans small
    · have wx := image_eq_zero_of_notMem_tsupport h
      simpa [b,wx,a0,Metric.mem_closedBall] using hr.le
  · have near := (show Filter.Tendsto w (𝓝 k) (𝓝 1) by simpa only [wk] using cw.continuous.tendsto k).eventually a.eventuallyEq_one
    filter_upwards [near] with x hx
    simp [b,show a (w x) = 1 from hx]

/-- Actual pulled columns admit an extension in the format required by the
integral endpoint Hessian. The extension agrees for all times on one
spatial neighborhood of the starting point. -/
theorem localized_pulled_columns (e : Frame M 2) {q r u P} (tube : ReferenceTube e q r u P)
    {k : State} (hk : k ∈ Metric.ball q r) :
    ∃ X : Columns State, Nonempty (SpatialJets X) ∧
      ∀ᶠ x in 𝓝 k, ∀ i t, X.Y i t x = pulledField e P i (clamp t) x := by
  obtain ⟨b,cb,inside,agree⟩ := localize_argument hk
  let A (i) := pulledSecond (K := univ) e tube i b cb (fun x _ => inside x)
  let full (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : Time → State → V) (hf : Joint univ f) : C(Time × State,V) :=
    ⟨fun p => f p.1 p.2,hf.comp (continuous_fst.prodMk
      (continuous_snd.subtype_mk (fun x => mem_univ _)))⟩
  let tc : ℝ × State → Time × State := fun p => (clamp p.1,p.2)
  have ctc : Continuous tc := (continuous_projIcc.comp continuous_fst).prodMk continuous_snd
  let X : Columns State :=
    { Y := fun i t x => pulledField e P i (clamp t) (b x)
      continuous := fun i => (full _ _ (A i).first.value).continuous.comp ctc
      differentiable := fun i t _ x => ((A i).first.rule (clamp t) x (mem_univ _)).differentiableAt
      jacobian := fun i => by
        have eq (t : ℝ) (x : State) := ((A i).first.rule (clamp t) x (mem_univ _)).fderiv
        simp_rw [eq]
        exact (full _ _ (A i).first.derivative).continuous.comp ctc }
  let jets : SpatialJets X :=
    { J := fun i => full _ _ (A i).first.derivative
      H := fun i => full _ _ (A i).next.derivative
      first := fun i t x => by
        change HasFDerivAt (fun y => pulledField e P i (clamp t) (b y)) _ x
        rw [show clamp (t:ℝ) = t from projIcc_of_mem _ t.2]
        exact (A i).first.rule t x (mem_univ _)
      second := fun i t x => (A i).next.rule t x (mem_univ _) }
  refine ⟨X,⟨jets⟩,?_⟩
  filter_upwards [agree] with x hx
  intro i t
  exact congrArg (pulledField e P i (clamp t)) hx

#print axioms localized_pulled_columns

/-- The true pair of frame velocities sampled along the reference flow is
a twice differentiable function of the starting point in the supremum
path norm on a neighborhood of every interior point. -/
theorem reference_velocity_family (e : Frame M 2) {q r u P} (tube : ReferenceTube e q r u P)
    {k : State} (hk : k ∈ Metric.ball q r) :
    ∃ C : State → C(Time,Fiber 2 →L[ℝ] State), ContDiff ℝ 2 C ∧
      ∀ᶠ x in 𝓝 k, ∀ (t : Time) v, C x t v = e.velocity (P x t) v := by
  obtain ⟨b,cb,inside,agree⟩ := localize_argument hk
  let full (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : Time → State → V) (hf : Joint univ f) : C(Time × State,V) :=
    ⟨fun p => f p.1 p.2,hf.comp (continuous_fst.prodMk
      (continuous_snd.subtype_mk (fun _ => mem_univ _)))⟩
  let v := pathSecond (K := univ) (fun x => P (b x)) (fun x _ =>
    ((tube.regular _ (inside x)).of_le (show (2 : WithTop ℕ∞) ≤ 3 by decide)).comp x cb.contDiffAt)
  let S (i : Fin 2) := v.post (e.X i) (fun t x _ =>
    ((e.smooth i).contDiffAt (e.chart.open_target.mem_nhds (tube.chart _ (inside x) t))).of_le (by decide))
  let Y (i : Fin 2) := full _ _ (S i).first.value
  let D (i : Fin 2) := full _ _ (S i).first.derivative
  let H (i : Fin 2) := full _ _ (S i).next.derivative
  let K0 : State →L[ℝ] C(Time,State) := ContinuousLinearMap.const ℝ Time
  let T (i : Fin 2) := PathCalculus.subst (Y i) ∘ K0
  have sm (i : Fin 2) : ContDiff ℝ 2 (T i) :=
    (PathCalculus.contDiff_two_subst (Y i) (D i) (H i)
      (fun t x => (S i).first.rule t x (mem_univ _))
      (fun t x => (S i).next.rule t x (mem_univ _))).comp K0.contDiff
  let channel (i : Fin 2) : C(Time,State) →L[ℝ] C(Time,Fiber 2 →L[ℝ] State) := (ContinuousLinearMap.smulRightL ℝ (Fiber 2) State
    (ContinuousLinearMap.proj i)).compLeftContinuous ℝ Time
  let C := fun x => channel 0 (T 0 x) + channel 1 (T 1 x)
  have c (i : Fin 2) : ContDiff ℝ 2 (fun x => channel i (T i x)) := by
    have cl : ContDiff ℝ 2 (⇑(channel i)) :=
      @ContinuousLinearMap.contDiff ℝ _ C(Time,State) _ _ C(Time,Fiber 2 →L[ℝ] State) _ _ 2 (channel i)
    exact cl.comp (sm i)
  refine ⟨C,(c 0).add (c 1),?_⟩
  filter_upwards [agree] with x hx
  intro t a
  change a 0 • e.X 0 (P (b x) t) + a 1 • e.X 1 (P (b x) t) = _
  rw [show b x = x from hx]
  simp [Frame.velocity,Fin.sum_univ_two]

#print axioms reference_velocity_family
end MinimizingSard.Five
