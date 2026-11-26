import ReferencePathJets

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace MinimizingSard.Five
open Volterra

private abbrev Tangent := State × State
private abbrev Matrix := State →L[ℝ] State
private abbrev Hess := State →L[ℝ] Matrix


private theorem lifted_invertible (φ : State → State) (k h : State) (sm : ContDiffAt ℝ 2 φ k)
    (inv : (fderiv ℝ φ k).IsInvertible) : (fderiv ℝ (tangentLift φ) (k,h)).IsInvertible := by
  obtain ⟨A,ha⟩ := inv
  refine ⟨A.skewProd A ((ContinuousLinearMap.apply ℝ State h).comp (fderiv ℝ (fderiv ℝ φ) k)),?_⟩
  apply ContinuousLinearMap.ext
  rintro ⟨a,b⟩
  rw [tangent_derivative φ k h sm]
  change ((A : Matrix) a,(A : Matrix) b + _) = _
  rw [ha]
  rfl

private theorem tangent_comp_germ (g f : State → State) (k h : State)
    (sf : ContDiffAt ℝ 2 f k) (sg : ContDiffAt ℝ 2 g (f k)) :
    tangentLift (g ∘ f) =ᶠ[𝓝 (k,h)] tangentLift g ∘ tangentLift f := by
  have d := sf.differentiableAt (by decide)
  have loc : ∀ᶠ x in 𝓝 k, ContDiffAt ℝ 2 g (f x) := d.continuousAt.tendsto (sg.eventually (by simp))
  have fst : Tendsto (Prod.fst : Tangent → State) (𝓝 (k,h)) (𝓝 k) := continuous_fst.continuousAt
  have near := fst.eventually (loc.and (sf.eventually (by simp)))
  filter_upwards [near] with p hp
  change (g (f p.1), fderiv ℝ (g ∘ f) p.1 p.2) = _
  rw [fderiv_comp p.1 (hp.1.differentiableAt (by decide)) (hp.2.differentiableAt (by decide))]
  rfl

private theorem smooth_lift (f : State → State) (k h : State) (s : ContDiffAt ℝ 2 f k) :
    DifferentiableAt ℝ (tangentLift f) (k,h) := by
  have diff := s.differentiableAt (by decide)
  have jac := (s.fderiv_right (m := 1) (by decide)).differentiableAt (by decide)
  exact (diff.comp (k,h) differentiableAt_fst).prodMk
    ((jac.comp (k,h) differentiableAt_fst).clm_apply differentiableAt_snd)


private theorem operator_derivative {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (J : ℝ → E →L[ℝ] F) (A : E →L[ℝ] F) (t : ℝ)
    (all : ∀ h, HasDerivAt (fun s => J s h) (A h) t) : HasDerivAt J A t := by
  let ι := Fin (Module.finrank ℝ E)
  let b : E ≃L[ℝ] (ι → ℝ) := (Module.finBasis ℝ E).equivFunL
  let c : (E →L[ℝ] F) ≃L[ℝ] (ι → F) :=
    (b.arrowCongr (ContinuousLinearEquiv.refl ℝ F)).trans (ContinuousLinearEquiv.piRing ι)
  have d : HasDerivAt (fun s => c (J s)) (c A) t :=
    hasDerivAt_pi.mpr (fun i => all (b.symm (Pi.single i 1)))
  simpa only [Function.comp_def,ContinuousLinearEquiv.coe_coe,c.symm_apply_apply]
    using c.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t d

private theorem time_eval {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (A : ℝ → E →L[ℝ] F) (D : E →L[ℝ] F) (t : ℝ)
    (a : E) (d : HasDerivAt A D t) : HasDerivAt (fun s => A s a) (D a) t :=
  (ContinuousLinearMap.apply ℝ F a).hasFDerivAt.comp_hasDerivAt t d

private theorem lifted_state_time (φ : ℝ → State → State) (U : State → State) (k h : State) (t : ℝ)
    (same : tangentLift (U ∘ φ t) (k,h) = tangentLift U (tangentLift (φ t) (k,h)))
    (dz : HasDerivAt (fun s => φ s k) (U (φ t k)) t)
    (dj : HasDerivAt (fun s => fderiv ℝ (φ s) k) (fderiv ℝ (U ∘ φ t) k) t) :
    HasDerivAt (fun s => tangentLift (φ s) (k,h)) (tangentLift U (tangentLift (φ t) (k,h))) t := by
  rw [← same]
  exact dz.prodMk ((ContinuousLinearMap.apply ℝ State h).hasFDerivAt.comp_hasDerivAt t dj)

set_option maxHeartbeats 2400000 in
private theorem lift_time (φ : ℝ → State → State) (U : State → State) (k h : State) (t : ℝ)
    (sf : ∀ s, ContDiffAt ℝ 2 (φ s) k) (sg : ContDiffAt ℝ 2 U (φ t k))
    (dz : HasDerivAt (fun s => φ s k) (U (φ t k)) t)
    (dj : HasDerivAt (fun s => fderiv ℝ (φ s) k) (fderiv ℝ (U ∘ φ t) k) t)
    (dh : HasDerivAt (fun s => fderiv ℝ (fderiv ℝ (φ s)) k) (fderiv ℝ (fderiv ℝ (U ∘ φ t)) k) t) :
    let z := fun s => tangentLift (φ s) (k,h)
    let J := fun s => fderiv ℝ (tangentLift (φ s)) (k,h)
    HasDerivAt z (tangentLift U (z t)) t ∧
      HasDerivAt J ((fderiv ℝ (tangentLift U) (z t)).comp (J t)) t := by
  have germ := tangent_comp_germ U (φ t) k h (sf t) sg
  have sm := sg.comp k (sf t)
  constructor
  · exact lifted_state_time φ U k h t germ.self_of_nhds dz dj
  · have dd := (germ.fderiv_eq (𝕜 := ℝ)).trans
      (fderiv_comp (k,h) (smooth_lift U _ _ sg) (smooth_lift (φ t) k h (sf t)))
    apply operator_derivative
    rintro ⟨a,b⟩
    rw [← dd,tangent_derivative _ _ _ sm]
    simp_rw [fun s => tangent_derivative (φ s) k h (sf s) a b]
    have jac (v : State) := time_eval (E := State) (F := State) _ _ t v dj
    have hes := time_eval (E := State) (F := Matrix) (fun s => fderiv ℝ (fderiv ℝ (φ s)) k)
      (fderiv ℝ (fderiv ℝ (U ∘ φ t)) k) t a dh
    exact (jac a).prodMk ((jac b).add (time_eval _ _ t h hes))

private theorem slice_jets (P : State → C(Time,State)) (k : State)
    (near : ∀ᶠ x in 𝓝 k, ContDiffAt ℝ 2 P x) (t : Time) :
    let φ := fun x => P x t
    let E := (ContinuousMap.evalCLM ℝ t : C(Time,State) →L[ℝ] State)
    fderiv ℝ φ k = E.comp (fderiv ℝ P k) ∧ ∀ h l,
      fderiv ℝ (fderiv ℝ φ) k h l = fderiv ℝ (fderiv ℝ P) k h l t := by
  let E := (ContinuousMap.evalCLM ℝ t : C(Time,State) →L[ℝ] State)
  let post := ContinuousLinearMap.compL ℝ State C(Time,State) State E
  have g : fderiv ℝ (fun x => P x t) =ᶠ[𝓝 k] fun x => post (fderiv ℝ P x) := by
    filter_upwards [near] with x dx
    exact (E.hasFDerivAt.comp x (dx.differentiableAt (by decide)).hasFDerivAt).fderiv
  have d := post.hasFDerivAt.comp k
    ((near.self_of_nhds.fderiv_right (m := 1) (by decide)).differentiableAt (by decide)).hasFDerivAt
  exact ⟨g.self_of_nhds,fun h l => congrArg (fun A : Hess => A h l) (d.congr_of_eventuallyEq g).fderiv⟩

private theorem tube_time {M : Type*} [TopologicalSpace M] [ChartedSpace State M]
    (e : Frame M 2) {q r u P} (tube : ReferenceTube e q r u P) {k : State}
    (hk : k ∈ Metric.ball q r) :
    let φ := fun (s : ℝ) x => P x (clamp s)
    let U := fun (t : ℝ) x => e.velocity x (u t)
    ∀ᵐ t ∂volume.restrict (Ioo (0:ℝ) 1),
      HasDerivAt (fun s => φ s k) (U t (φ t k)) t ∧
      HasDerivAt (fun s => fderiv ℝ (φ s) k) (fderiv ℝ (U t ∘ φ t) k) t ∧
      HasDerivAt (fun s => fderiv ℝ (fderiv ℝ (φ s)) k) (fderiv ℝ (fderiv ℝ (U t ∘ φ t)) k) t := by
  let φ := fun (s : ℝ) x => P x (clamp s)
  let U := fun (t : ℝ) x => e.velocity x (u t)
  obtain ⟨C,_,agree⟩ := reference_velocity_family e tube hk
  obtain ⟨R,rep⟩ := control_signal_equiv
  have a (s : ℝ) : C k (clamp s) ((R u) s) = U s (φ s k) := by rw [rep,agree.self_of_nhds]
  have hi : IntervalIntegrable (fun s => U s (φ s k)) volume 0 1 := by
    simpa only [← a] using Volterra.intervalIntegrable (C k) (R u)
  have kc := Metric.ball_subset_closedBall hk
  have dz := path_ae_velocity (fun s => φ s k) (fun s => U s (φ s k)) hi
    (fun t ht => by simpa only [φ,tube.initial k kc] using tube.flow k kc t ht)
  have near : ∀ᶠ x in 𝓝 k, ContDiffAt ℝ 2 P x := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hk] with x hx
    exact (tube.regular _ (Metric.ball_subset_closedBall hx)).of_le (by decide)
  have c1 (s : ℝ) (h : State) : fderiv ℝ (φ s) k h = fderiv ℝ P k h (clamp s) :=
    congrArg (fun L : Matrix => L h) (slice_jets P k near (clamp s)).1
  have c2 (s : ℝ) (h l : State) := (slice_jets P k near (clamp s)).2 h l
  let b := fun i : Fin 5 => (Pi.single i 1 : State)
  have cols (i j : Fin 5) := reference_variation_time_derivatives e tube hk (b i) (b j)
  filter_upwards [dz,ae_all_iff.mpr (fun i => ae_all_iff.mpr (cols i))] with t z data
  refine ⟨z,matrix_derivative _ _ t (fun i => ?_),matrix_derivative _ _ t (fun i => matrix_derivative _ _ t (fun j => ?_))⟩
  · change HasDerivAt (fun s => fderiv ℝ (φ s) k (b i)) (fderiv ℝ (U t ∘ φ t) k (b i)) t
    simp_rw [c1]
    exact (data i 0).1
  · change HasDerivAt (fun s => fderiv ℝ (fderiv ℝ (φ s)) k (b i) (b j))
      (fderiv ℝ (fderiv ℝ (U t ∘ φ t)) k (b i) (b j)) t
    have eq (s) : fderiv ℝ (fderiv ℝ (φ s)) k (b i) (b j) = _ := c2 s (b i) (b j)
    simp_rw [eq]
    exact (data i j).2

private theorem lifted_pull (φ X : State → State) (k h : State) (sf : ContDiffAt ℝ 2 φ k)
    (iv : (fderiv ℝ φ k).IsInvertible) (dx : DifferentiableAt ℝ X (φ k)) :
    (fderiv ℝ (tangentLift φ) (k,h)).inverse (tangentLift X (tangentLift φ (k,h))) =
      tangentLift (VectorField.pullback ℝ φ X) (k,h) :=
  (lifted_invertible φ k h sf iv).inverse_apply_eq.mpr (tangentLift_pullback φ X k h sf iv dx).symm

private theorem pull_time (φ : ℝ → State → State) (U X : State → State) (k h : State) (t : ℝ)
    (sf : ∀ s, ContDiffAt ℝ 2 (φ s) k) (iv : ∀ s, (fderiv ℝ (φ s) k).IsInvertible)
    (sg : ContDiffAt ℝ 2 U (φ t k)) (sx : ∀ s, ContDiffAt ℝ 2 X (φ s k))
    (dz : HasDerivAt (fun s => φ s k) (U (φ t k)) t)
    (dj : HasDerivAt (fun s => fderiv ℝ (φ s) k) (fderiv ℝ (U ∘ φ t) k) t)
    (dh : HasDerivAt (fun s => fderiv ℝ (fderiv ℝ (φ s)) k) (fderiv ℝ (fderiv ℝ (U ∘ φ t)) k) t) :
    HasDerivAt (fun s => tangentLift (VectorField.pullback ℝ (φ s) X) (k,h))
      (tangentLift (VectorField.pullback ℝ (φ t) (VectorField.lieBracket ℝ U X)) (k,h)) t := by
  obtain ⟨z,j⟩ := lift_time φ U k h t sf sg dz dj dh
  let Z := fun s => tangentLift (φ s) (k,h)
  let J := fun s => fderiv ℝ (tangentLift (φ s)) (k,h)
  have d := pulled_field_derivative Z J (tangentLift U) (tangentLift X) t z j
    (lifted_invertible _ _ _ (sf t) (iv t)) (smooth_lift X _ _ (sx t))
  have br := tangentLift_bracket U X (φ t k) (fderiv ℝ (φ t) k h) sg (sx t)
  have sb : ContDiffAt ℝ 1 (VectorField.lieBracket ℝ U X) (φ t k) :=
    sg.lieBracket_vectorField (sx t) (by decide)
  have val (s) := lifted_pull (φ s) X k h (sf s) (iv s) ((sx s).differentiableAt (by decide))
  have target : (J t).inverse (VectorField.lieBracket ℝ (tangentLift U) (tangentLift X) (Z t)) =
      tangentLift (VectorField.pullback ℝ (φ t) (VectorField.lieBracket ℝ U X)) (k,h) := by
    rw [show VectorField.lieBracket ℝ (tangentLift U) (tangentLift X) (Z t) = _ from br]
    exact lifted_pull _ _ k h (sf t) (iv t) (sb.differentiableAt (by decide))
  rw [target] at d
  simpa only [Z,J,val] using d

/-- The full first spatial jet of each pulled original frame field
evolves by the pullback of its Lie bracket with the frozen velocity.
Both derivatives concern the same reference control and initial point. -/
theorem reference_pulled_jet_time {M : Type*} [TopologicalSpace M] [ChartedSpace State M]
    (e : Frame M 2) {q r u P} (tube : ReferenceTube e q r u P) {k : State}
    (hk : k ∈ Metric.ball q r) :
    let φ := fun (s : ℝ) x => P x (clamp s)
    let U := fun (t : ℝ) x => e.velocity x (u t)
    ∀ᵐ t ∂volume.restrict (Ioo (0:ℝ) 1), ∀ i,
      HasDerivAt (fun s => (pulledField e P i (clamp s) k,fderiv ℝ (pulledField e P i (clamp s)) k))
        (let B := VectorField.pullback ℝ (φ t) (VectorField.lieBracket ℝ (U t) (e.X i))
         (B k,fderiv ℝ B k)) t := by
  let φ := fun (s : ℝ) x => P x (clamp s)
  let U := fun (t : ℝ) x => e.velocity x (u t)
  have kc := Metric.ball_subset_closedBall hk
  have sf (s : ℝ) : ContDiffAt ℝ 2 (φ s) k :=
    (ContinuousMap.evalCLM ℝ (clamp s)).contDiff.contDiffAt.comp k ((tube.regular k kc).of_le (by decide))
  have eq (s : ℝ) : ∀ᶠ x in 𝓝 k, fderiv ℝ (φ s) x =
      (ContinuousMap.evalCLM ℝ (clamp s)).comp (fderiv ℝ P x) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hk] with x hx
    exact ((ContinuousMap.evalCLM ℝ (clamp s)).hasFDerivAt.comp x
      ((tube.regular _ (Metric.ball_subset_closedBall hx)).differentiableAt (by decide)).hasFDerivAt).fderiv
  have iv (s : ℝ) : (fderiv ℝ (φ s) k).IsInvertible := (eq s).self_of_nhds ▸ tube.invertible k kc _
  have sx (i : Fin 2) (s : ℝ) : ContDiffAt ℝ 2 (e.X i) (φ s k) :=
    ((e.smooth i).contDiffAt (e.chart.open_target.mem_nhds (tube.chart k kc _))).of_le (by decide)
  have su (t : ℝ) : ContDiffAt ℝ 2 (U t) (φ t k) := by
    simpa only [U,Frame.velocity,Fin.sum_univ_two] using ((sx 0 t).const_smul (u t 0)).add ((sx 1 t).const_smul (u t 1))
  have agree (i : Fin 2) (s : ℝ) : pulledField e P i (clamp s) =ᶠ[𝓝 k]
      VectorField.pullback ℝ (φ s) (e.X i) := by
    filter_upwards [eq s] with x hx
    change _ = (fderiv ℝ (φ s) x).inverse _
    rw [hx]
    rfl
  filter_upwards [tube_time e tube hk] with t ht
  intro i
  let B := VectorField.pullback ℝ (φ t) (VectorField.lieBracket ℝ (U t) (e.X i))
  have result (h : State) := pull_time φ (U t) (e.X i) k h t sf iv (su t) (sx i) ht.1 ht.2.1 ht.2.2
  have base : HasDerivAt (fun s => pulledField e P i (clamp s) k) (B k) t := by
    simp_rw [fun s => (agree i s).self_of_nhds]
    exact (result 0).fst
  refine base.prodMk (matrix_derivative _ _ t (fun j => ?_))
  simp_rw [fun s => (agree i s).fderiv_eq (𝕜 := ℝ)]
  exact (result (Pi.single j 1)).snd

#print axioms reference_pulled_jet_time

private theorem scalar_jet (f g : State → State) (k : State) (a : ℝ)
    (same : f =ᶠ[𝓝 k] a • g) : (f k,fderiv ℝ f k) = a • (g k,fderiv ℝ g k) := by
  rw [same.self_of_nhds,same.fderiv_eq (𝕜 := ℝ),fderiv_const_smul_of_field]
  rfl

/-- The two signed first-jet equations on the original rank-two tube. -/
theorem reference_signed_jet_time {M : Type*} [TopologicalSpace M] [ChartedSpace State M]
    (e : Frame M 2) {q r u P} (tube : ReferenceTube e q r u P) {k : State}
    (hk : k ∈ Metric.ball q r) :
    let φ := fun (s : ℝ) x => P x (clamp s)
    let Y := fun (i : Fin 2) (s : ℝ) => pulledField e P i (clamp s)
    let B := fun (s : ℝ) => VectorField.pullback ℝ (φ s) (VectorField.lieBracket ℝ (e.X 0) (e.X 1))
    let jet := fun (X : State → State) => (X k,fderiv ℝ X k)
    ∀ᵐ t ∂volume.restrict (Ioo (0:ℝ) 1),
      HasDerivAt (fun s => jet (Y 0 s)) (-(u t 1) • jet (B t)) t ∧
      HasDerivAt (fun s => jet (Y 1 s)) (u t 0 • jet (B t)) t := by
  let φ := fun (s : ℝ) x => P x (clamp s)
  let U := fun (t : ℝ) x => e.velocity x (u t)
  let B := VectorField.lieBracket ℝ (e.X 0) (e.X 1)
  have vel (t : ℝ) : U t = u t 0 • e.X 0 + u t 1 • e.X 1 := by funext x; simp [U,Frame.velocity,Fin.sum_univ_two]
  have brackets (t) (y : State) (hy : y ∈ e.chart.target) (i : Fin 2) :
      VectorField.lieBracket ℝ (U t) (e.X i) y = u t 0 • VectorField.lieBracket ℝ (e.X 0) (e.X i) y +
        u t 1 • VectorField.lieBracket ℝ (e.X 1) (e.X i) y := by
    have d (j) := ((e.smooth j).contDiffAt (e.chart.open_target.mem_nhds hy)).differentiableAt (by simp)
    rw [vel,VectorField.lieBracket_add_left ((d 0).const_smul _) ((d 1).const_smul _),
      VectorField.lieBracket_const_smul_left (d 0),VectorField.lieBracket_const_smul_left (d 1)]
  filter_upwards [reference_pulled_jet_time e tube hk] with t d
  have pair : ∀ᶠ x in 𝓝 k,
      VectorField.pullback ℝ (φ t) (VectorField.lieBracket ℝ (U t) (e.X 0)) x =
        -(u t 1) • VectorField.pullback ℝ (φ t) B x ∧
      VectorField.pullback ℝ (φ t) (VectorField.lieBracket ℝ (U t) (e.X 1)) x =
        u t 0 • VectorField.pullback ℝ (φ t) B x := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hk] with x hx
    have hy := tube.chart x (Metric.ball_subset_closedBall hx) (clamp t)
    change (fderiv ℝ (φ t) x).inverse (VectorField.lieBracket ℝ (U t) (e.X 0) (φ t x)) = _ ∧
      (fderiv ℝ (φ t) x).inverse (VectorField.lieBracket ℝ (U t) (e.X 1) (φ t x)) = _
    rw [brackets t _ hy 0,brackets t _ hy 1,VectorField.lieBracket_swap (V := e.X 1) (W := e.X 0)]
    simp [VectorField.pullback,B,φ]
  have a := scalar_jet _ _ k (-(u t 1)) (pair.mono (fun _ h => h.1))
  have b := scalar_jet _ _ k (u t 0) (pair.mono (fun _ h => h.2))
  exact ⟨a ▸ d 0,b ▸ d 1⟩

#print axioms reference_signed_jet_time

/-- Continuity of both entries of the transported bracket jet in time. -/
theorem reference_bracket_jet_continuous {M : Type*} [TopologicalSpace M] [ChartedSpace State M]
    (e : Frame M 2) {q r u P} (tube : ReferenceTube e q r u P) {k : State}
    (hk : k ∈ Metric.ball q r) :
    let φ := fun (s : ℝ) x => P x (clamp s)
    let B := fun s => VectorField.pullback ℝ (φ s) (VectorField.lieBracket ℝ (e.X 0) (e.X 1))
    Continuous (fun s => (B s k,fderiv ℝ (B s) k)) := by
  let φ := fun (s : ℝ) x => P x (clamp s)
  let X := VectorField.lieBracket ℝ (e.X 0) (e.X 1)
  let B := fun s => VectorField.pullback ℝ (φ s) X
  have kc := Metric.ball_subset_closedBall hk
  have near : ∀ᶠ x in 𝓝 k, ContDiffAt ℝ 2 P x := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hk] with x hx
    exact (tube.regular _ (Metric.ball_subset_closedBall hx)).of_le (by decide)
  have sf (s : ℝ) : ContDiffAt ℝ 2 (φ s) k :=
    (@ContinuousLinearMap.contDiff ℝ _ C(Time,State) _ _ State _ _ 2
      (ContinuousMap.evalCLM ℝ (clamp s))).contDiffAt.comp k near.self_of_nhds
  have iv (s : ℝ) : (fderiv ℝ (φ s) k).IsInvertible :=
    (slice_jets P k near (clamp s)).1 ▸ tube.invertible k kc _
  have sx (s : ℝ) : ContDiffAt ℝ 2 X (φ s k) := by
    have d (i) : ContDiffAt ℝ 3 (e.X i) (φ s k) :=
      ((e.smooth i).contDiffAt (e.chart.open_target.mem_nhds (tube.chart k kc (clamp s)))).of_le (by decide)
    exact (d 0).lieBracket_vectorField (d 1) (by decide)
  have pos : Continuous (fun s => φ s k) := (P k).continuous.comp continuous_projIcc
  have jac : Continuous (fun s => fderiv ℝ (φ s) k) := by
    apply continuous_clm_apply.mpr
    intro h
    have eq (s : ℝ) := congrArg (fun L : Matrix => L h) (slice_jets P k near (clamp s)).1
    simp_rw [show ∀ s, fderiv ℝ (φ s) k h = fderiv ℝ P k h (clamp s) from eq]
    exact (fderiv ℝ P k h).continuous.comp continuous_projIcc
  have hess : Continuous (fun s => fderiv ℝ (fderiv ℝ (φ s)) k) := by
    apply continuous_clm_apply.mpr
    intro h
    apply continuous_clm_apply.mpr
    intro l
    have eq (s : ℝ) : fderiv ℝ (fderiv ℝ (φ s)) k h l = _ := (slice_jets P k near (clamp s)).2 h l
    simp_rw [eq]
    exact (fderiv ℝ (fderiv ℝ P) k h l).continuous.comp continuous_projIcc
  have lift (h : State) : Continuous (fun s => tangentLift (B s) (k,h)) := by
    have z : Continuous (fun s => tangentLift (φ s) (k,h)) :=
      pos.prodMk (jac.clm_apply (continuous_const (y := h)))
    have j : Continuous (fun s => fderiv ℝ (tangentLift (φ s)) (k,h)) := by
      apply continuous_clm_apply.mpr
      rintro ⟨a,b⟩
      simp_rw [fun s => tangent_derivative (φ s) k h (sf s) a b]
      exact (jac.clm_apply (continuous_const (y := a))).prodMk
        ((jac.clm_apply (continuous_const (y := b))).add
          ((hess.clm_apply (continuous_const (y := a))).clm_apply (continuous_const (y := h))))
    have val (s : ℝ) := lifted_pull (φ s) X k h (sf s) (iv s) ((sx s).differentiableAt (by decide))
    apply continuous_iff_continuousAt.mpr
    intro s
    have inv := (lifted_invertible (φ s) k h (sf s) (iv s)).contDiffAt_map_inverse (𝕜 := ℝ) (n := 1)
    have dx := (smooth_lift X (φ s k) (fderiv ℝ (φ s) k h) (sx s)).continuousAt.comp (x := s) z.continuousAt
    have dh := ((inv.continuousAt.comp (x := s) j.continuousAt).clm_apply dx)
    simpa only [Function.comp_def,val,B] using dh
  exact (lift 0).fst.prodMk (continuous_clm_apply.mpr (fun h => (lift h).snd))

#print axioms reference_bracket_jet_continuous
end MinimizingSard.Five
