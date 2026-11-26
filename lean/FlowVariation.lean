import L2MovingEndpoint

/-! Differentiate the original state-dependent integral equation
in an initial-state direction at a fixed, possibly nonzero, L² input. -/
noncomputable section
open Set Filter
open scoped Topology
namespace MinimizingSard.Volterra
open PathCalculus
variable {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup U] [NormedSpace ℝ U]

/-- A smooth family of genuine integral trajectories satisfies the
linearized integral equation along the reference path. -/
theorem initial_state_variation (f : C(Time × E,U →L[ℝ] E))
    (D : C(Time × E,E →L[ℝ] U →L[ℝ] E))
    (der : ∀ t x, HasFDerivAt (fun y => f (t,y)) (D (t,x)) x)
    (u : Causal.Signals U) (S : E → C(Time,E)) (q a h : E)
    (smooth : DifferentiableAt ℝ S a)
    (path : ∀ᶠ x in 𝓝 a, S x = ContinuousMap.const Time (q+x) + operator U E (subst f (S x)) u) :
    ∀ t : Time, (fderiv ℝ S a h) t =
      h + ∫ s in (0:ℝ)..(t:ℝ), D (clamp s,S a (clamp s)) ((fderiv ℝ S a h) (clamp s)) (u s) := by
  let H := (ContinuousLinearMap.apply ℝ C(Time,E) u).comp (operator U E)
  let I : E →L[ℝ] C(Time,E) := ContinuousLinearMap.const ℝ Time
  have d := (hasFDerivAt_subst f D der (S a)).comp a smooth.hasFDerivAt
  have init := I.hasFDerivAt.comp a ((hasFDerivAt_id a).const_add q)
  have rhs := init.add (H.hasFDerivAt.comp a d)
  have lhs := rhs.congr_of_eventuallyEq path
  have jac := congrArg (fun L : E →L[ℝ] C(Time,E) => L h) lhs.fderiv
  intro t
  have atTime := congrArg (fun w : C(Time,E) => w t) jac
  change (fderiv ℝ S a h) t = h +
    operator U E (multiplier Time E (U →L[ℝ] E) (subst D (S a)) (fderiv ℝ S a h)) u t at atTime
  rw [operator_eq_interval] at atTime
  exact atTime

#print axioms initial_state_variation

/-- All sufficiently small references in a joint path family satisfy
the variational equation, with the input fixed at its reference value. -/
theorem nearby_initial_variations (f : C(Time × E,U →L[ℝ] E))
    (D : C(Time × E,E →L[ℝ] U →L[ℝ] E))
    (der : ∀ t x, HasFDerivAt (fun y => f (t,y)) (D (t,x)) x)
    (S : E × Causal.Signals U → C(Time,E)) (q : E) (smooth : ContDiffAt ℝ 1 S 0)
    (path : ∀ᶠ p in 𝓝 0, S p = ContinuousMap.const Time (q+p.1) + operator U E (subst f (S p)) p.2) :
    ∀ᶠ p : E × Causal.Signals U in 𝓝 0, ∀ h : E,
      let T := fun x => S (x,p.2)
      ∀ t : Time, (fderiv ℝ T p.1 h) t =
        h + ∫ s in (0:ℝ)..(t:ℝ), D (clamp s,S p (clamp s)) ((fderiv ℝ T p.1 h) (clamp s)) (p.2 s) := by
  have localPath := eventually_eventually_nhds.mpr path
  filter_upwards [localPath,smooth.eventually (by simp)] with p eq cs
  let T (x : E) := S (x,p.2)
  have incl : DifferentiableAt ℝ (fun x : E => (x,p.2)) p.1 :=
    differentiableAt_id.prodMk (differentiableAt_const p.2)
  have dT : DifferentiableAt ℝ T p.1 := (cs.differentiableAt (by norm_num)).comp p.1 incl
  have pathT : ∀ᶠ x in 𝓝 p.1, T x = ContinuousMap.const Time (q+x) + operator U E (subst f (T x)) p.2 :=
    incl.continuousAt.tendsto eq
  exact fun h => initial_state_variation f D der p.2 T q p.1 h dT pathT

#print axioms nearby_initial_variations

/-- Uniform-in-time invertibility of the actual state Jacobian follows
from the constant-input slice and joint finite-order differentiability. -/
theorem nearby_state_jacobian_invertible [CompleteSpace E] (S : E × U → C(Time,E)) (q : E)
    (cs : ContDiffAt ℝ 1 S 0) (zeroSlice : ∀ᶠ x in 𝓝 (0:E), S (x,0) = ContinuousMap.const Time (q+x)) :
    ∀ᶠ p in 𝓝 0, ∀ t : Time, ((ContinuousMap.evalCLM ℝ t).comp
      ((fderiv ℝ S p).comp (ContinuousLinearMap.inl ℝ E U))).IsInvertible := by
  let I : E →L[ℝ] C(Time,E) := ContinuousLinearMap.const ℝ Time
  let ins := ContinuousLinearMap.inl ℝ E U
  let K (p : E × U) := (fderiv ℝ S p).comp ins
  have root : K 0 = I := by
    have ds := (cs.differentiableAt (by norm_num)).hasFDerivAt.comp (0:E) ins.hasFDerivAt
    have alt := I.hasFDerivAt.comp (0:E) ((hasFDerivAt_id (0:E)).const_add q)
    exact ds.unique (alt.congr_of_eventuallyEq zeroSlice)
  have ck : ContinuousAt K 0 :=
    ((cs.fderiv_right (m := 0) (by norm_num)).clm_comp contDiffAt_const).continuousAt
  have near : ∀ᶠ p in 𝓝 0, ‖I-K p‖ < 1 := by
    filter_upwards [ck.tendsto (Metric.ball_mem_nhds (K 0) zero_lt_one)] with p hp
    change dist (K p) (K 0) < 1 at hp
    rw [dist_comm] at hp
    change ‖K 0-K p‖ < 1 at hp
    rwa [root] at hp
  filter_upwards [near] with p hp
  intro t
  let J := (ContinuousMap.evalCLM ℝ t).comp (K p)
  have bound : ‖(1 : E →L[ℝ] E)-J‖ ≤ ‖I-K p‖ := by
    apply ContinuousLinearMap.opNorm_le_bound (1-J) (I-K p).opNorm_nonneg
    intro h
    exact (((I-K p) h).norm_coe_le_norm t).trans ((I-K p).le_opNorm h)
  have unit : IsUnit J := by
    simpa using isUnit_one_sub_of_norm_lt_one (bound.trans_lt hp)
  obtain ⟨g,hg⟩ := unit
  exact ⟨ContinuousLinearEquiv.unitsEquiv ℝ E g,hg⟩

#print axioms nearby_state_jacobian_invertible
end MinimizingSard.Volterra

namespace MinimizingSard.Volterra
open PulseGeometry PathCalculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A selected solution of the two-channel horizontal ODE and the
initial-state response along its nearby nonzero reference controls. -/
theorem column_flow_variation (X : Columns E) (q : E) (jets : ∀ i, SpatialOrder 1 (X.spatialField i)) :
    ∃ S : E × Controls → C(Time,E), ContDiffAt ℝ 1 S 0 ∧
      ∀ᶠ p in 𝓝 0, X.Path (q+p.1) p.2 (fun s => S p (clamp s)) ∧
        (∀ t : Time, ((ContinuousMap.evalCLM ℝ t).comp
          ((fderiv ℝ S p).comp (ContinuousLinearMap.inl ℝ E Controls))).IsInvertible) ∧ ∀ h : E,
        let T := fun x => S (x,p.2)
        let H := fderiv ℝ T p.1 h
        ∀ t : Time, H t = h + ∫ s in (0:ℝ)..(t:ℝ),
          p.2 s 0 • fderiv ℝ (X.Y 0 (clamp s)) (S p (clamp s)) (H (clamp s)) +
          p.2 s 1 • fderiv ℝ (X.Y 1 (clamp s)) (S p (clamp s)) (H (clamp s)) := by
  let U := Fin 2 → ℝ
  let L (i : Fin 2) : E →L[ℝ] U →L[ℝ] E :=
    ContinuousLinearMap.smulRightL ℝ U E (ContinuousLinearMap.proj i)
  obtain ⟨W,_,cw,pw⟩ := joint_path_family X 1 (by norm_num) jets q
  choose J first _ using jets
  let f : C(Time × E,U →L[ℝ] E) :=
    ⟨fun p => L 0 (X.Y 0 p.1 p.2) + L 1 (X.Y 1 p.1 p.2),
      ((L 0).continuous.comp (X.spatialField 0).continuous).add ((L 1).continuous.comp (X.spatialField 1).continuous)⟩
  let D : C(Time × E,E →L[ℝ] U →L[ℝ] E) := ⟨fun p => (L 0).comp (J 0 p) + (L 1).comp (J 1 p),
    (continuous_const.clm_comp (J 0).continuous).add (continuous_const.clm_comp (J 1).continuous)⟩
  have der (t : Time) (x : E) : HasFDerivAt (fun y => f (t,y)) (D (t,x)) x :=
    ((L 0).hasFDerivAt.comp x (first 0 t x)).add ((L 1).hasFDerivAt.comp x (first 1 t x))
  let S (p : E × Controls) := ContinuousMap.const Time q + W p
  have cs : ContDiffAt ℝ 1 S 0 := contDiffAt_const.add cw
  have fixed : ∀ᶠ p : E × Controls in 𝓝 0, S p = ContinuousMap.const Time (q+p.1) + operator U E (subst f (S p)) p.2 := by
    filter_upwards [pw] with p hp
    ext t
    have ht := hp.1.2.2 t t.2
    dsimp only at ht
    rw [show clamp (t:ℝ) = t from projIcc_of_mem _ t.2] at ht
    change q + W p t = (q+p.1) + operator U E (subst f (S p)) p.2 t
    rw [ht,operator_eq_interval]
    apply congrArg ((q+p.1)+ ·)
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le t.2.1] at hs
    have sc : clamp s = ⟨s,hs.1,hs.2.trans t.2.2⟩ := projIcc_of_mem _ _
    change X.velocity s (q+ W p (clamp s)) (p.2 s) = f (clamp s,S p (clamp s)) (p.2 s)
    rw [sc]; rfl
  refine ⟨S,cs,?_⟩
  have zin : Tendsto (fun x : E => (x,(0:Controls))) (𝓝 0) (𝓝 0) :=
    (continuous_id.prodMk continuous_const).tendsto 0
  have slice : ∀ᶠ x in 𝓝 (0:E), S (x,0) = ContinuousMap.const Time (q+x) := by
    filter_upwards [zin fixed] with x eq
    simpa using eq
  filter_upwards [pw,nearby_initial_variations f D der S q cs fixed,
    nearby_state_jacobian_invertible S q cs slice] with p hp hv inv
  refine ⟨hp.1,inv,?_⟩
  intro h T H t
  have hj (i : Fin 2) (s : Time) (x : E) : J i (s,x) = fderiv ℝ (X.Y i s) x := (first i s x).fderiv.symm
  rw [hv h t]
  apply congrArg (h+ ·)
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  change p.2 s 0 • (J 0 _) _ + p.2 s 1 • (J 1 _) _ = _
  rw [hj,hj]

#print axioms column_flow_variation
end MinimizingSard.Volterra
