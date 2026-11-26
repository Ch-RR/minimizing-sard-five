import L2Volterra

/-! An exit estimate for all fixed paths, including paths outside the
local inverse chart. The coefficient at time t depends only on the value
of the state at t. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace MinimizingSard.Volterra

variable {U E : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

private def past (w : C(Time,E)) (t : ℝ) : C(Time,E) :=
  ⟨fun s => w (min s (clamp t)), w.continuous.comp (continuous_id.min continuous_const)⟩

omit [NormedSpace ℝ E] in
private theorem past_continuous (w : C(Time,E)) : Continuous (past w) :=
  ContinuousMap.continuous_of_continuous_uncurry _ (w.continuous.comp
    (continuous_snd.min (continuous_projIcc.comp continuous_fst)))

/-- An integral path cannot exit a ball on which its coefficient is bounded.
Only the actual coefficient along that path enters the estimate. -/
theorem path_stays_in_ball (w : C(Time,E)) (a : E) (A : C(Time,U →L[ℝ] E))
    (u : Causal.Signals U) {R M : ℝ} (hM : 0 ≤ M)
    (eq : ∀ t, w t = a + primitive A u t)
    (bound : ∀ t, ‖w t‖ ≤ R → ‖A t‖ ≤ M)
    (small : ‖a‖ + M * ‖u‖ < R) : ‖w‖ < R := by
  let l : Time := ⟨0,le_rfl,zero_le_one⟩
  let h : Time := ⟨1,zero_le_one,le_rfl⟩
  have wl : w l = a := by rw [eq]; simp [primitive,l]
  have start : ‖past w 0‖ ≤ ‖a‖ := by
    apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro s
    change ‖w (min s (clamp 0))‖ ≤ ‖a‖
    rw [show clamp 0 = l from projIcc_of_mem _ l.2,min_eq_right (show l ≤ s from s.2.1),wl]
  have stop : past w 1 = w := by
    ext s
    change w (min s (clamp 1)) = w s
    rw [show clamp 1 = h from projIcc_of_mem _ h.2,min_eq_left (show s ≤ h from s.2.2)]
  by_contra! bad
  obtain ⟨t,_,hit⟩ := intermediate_value_Icc zero_le_one (past_continuous w).norm.continuousOn
    (show R ∈ Icc ‖past w 0‖ ‖past w 1‖ by
      rw [stop]; exact ⟨start.trans (by linarith [mul_nonneg hM (norm_nonneg u)]),bad⟩)
  change ‖past w t‖ = R at hit
  have est : ‖past w t‖ ≤ ‖a‖ + M * ‖u‖ := by
    apply (ContinuousMap.norm_le _ (add_nonneg (norm_nonneg _) (mul_nonneg hM (norm_nonneg _)))).mpr
    intro s
    change ‖w (min s (clamp t))‖ ≤ _
    rw [eq]
    apply (norm_add_le _ _).trans
    apply add_le_add_left
    apply primitive_estimate _ _ _ M hM
    intro v hv
    apply bound
    have h := (past w t).norm_coe_le_norm v
    change ‖w (min v (clamp t))‖ ≤ _ at h
    rwa [min_eq_left (hv.trans (min_le_right _ _)),hit] at h
  exact (not_le_of_gt small) (hit ▸ est)

#print axioms path_stays_in_ball

/-- A common exit estimate also holds while the coefficient varies
with an auxiliary parameter near zero. -/
theorem fixed_paths_small_with_parameter {P : Type*} [NormedAddCommGroup P]
    (C : P → C(Time,E) → C(Time,U →L[ℝ] E))
    (hc : ContinuousAt (fun p : P × C(Time,E) => C p.1 p.2) 0)
    (pointwise : ∀ a w z t, w t = z t → C a w t = C a z t) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ p : P × Causal.Signals U in 𝓝 0, ∀ w : C(Time,E), w = operator U E (C p.1 w) p.2 → ‖w‖ < r := by
  let M := ‖C 0 0‖ + 1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  obtain ⟨δ,hδ,osc⟩ := (Metric.continuousAt_iff (f := fun p : P × C(Time,E) => C p.1 p.2) (a := 0)).mp hc 1 zero_lt_one
  let a := min r δ / 2
  have ha : 0 < a := half_pos (lt_min hr hδ)
  have ar : a < r := (half_lt_self (lt_min hr hδ)).trans_le (min_le_left _ _)
  have ad : a < δ := (half_lt_self (lt_min hr hδ)).trans_le (min_le_right _ _)
  have small : ∀ᶠ u : Causal.Signals U in 𝓝 0, M * ‖u‖ < a := by
    have c : ContinuousAt (fun u : Causal.Signals U => M * ‖u‖) 0 := by fun_prop
    exact c.eventually_lt continuousAt_const (by simpa using ha)
  have pin : ∀ᶠ x : P × Causal.Signals U in 𝓝 0, ‖x.1‖ < δ :=
    continuousAt_fst.norm.eventually_lt continuousAt_const (by simpa using hδ)
  filter_upwards [continuousAt_snd.tendsto small,pin] with p hu pa
  let u := p.2
  intro w eq
  have atTime (t : Time) : w t = primitive (C p.1 w) u t := congrArg (fun z : C(Time,E) => z t) eq
  let l : Time := ⟨0,le_rfl,zero_le_one⟩
  let h : Time := ⟨1,zero_le_one,le_rfl⟩
  have l0 : clamp 0 = l := projIcc_of_mem _ l.2
  have h1 : clamp 1 = h := projIcc_of_mem _ h.2
  have wl : w l = 0 := by rw [atTime]; simp [primitive,l]
  have start : past w 0 = 0 := by
    ext s
    change w (min s (clamp 0)) = 0
    rw [l0,min_eq_right (show l ≤ s from s.2.1),wl]
  have stop : past w 1 = w := by
    ext s
    change w (min s (clamp 1)) = w s
    rw [h1,min_eq_left (show s ≤ h from s.2.2)]
  by_contra! bad
  obtain ⟨t,_,hit⟩ := intermediate_value_Icc zero_le_one (past_continuous w).norm.continuousOn
    (show a ∈ Icc ‖past w 0‖ ‖past w 1‖ by rw [start,stop,norm_zero]; exact ⟨ha.le,ar.le.trans bad⟩)
  change ‖past w t‖ = a at hit
  have close := osc (show dist (p.1,past w t) (0 : P × C(Time,E)) < δ by simpa [Prod.dist_eq,hit] using And.intro pa ad)
  change dist (C p.1 (past w t)) (C 0 0) < 1 at close
  have cb : ‖C p.1 (past w t)‖ ≤ M := by
    have le := dist_triangle (C p.1 (past w t)) (C 0 0) (0 : C(Time,U →L[ℝ] E))
    rw [dist_zero_right (C p.1 (past w t)),dist_zero_right (C 0 0)] at le
    exact le.trans (by dsimp [M]; linarith)
  have est : ‖past w t‖ ≤ M * ‖u‖ := by
    apply (ContinuousMap.norm_le _ (mul_nonneg hM (norm_nonneg u))).mpr
    intro s
    change ‖w (min s (clamp t))‖ ≤ _
    rw [atTime]
    apply primitive_estimate _ _ _ M hM
    intro v hv
    have vle : v ≤ clamp t := hv.trans (min_le_right _ _)
    have cv := pointwise p.1 w (past w t) v (by change w v = w (min v (clamp t)); rw [min_eq_left vle])
    rw [cv]
    exact ((C p.1 (past w t)).norm_coe_le_norm v).trans cb
  exact (not_le.mpr hu) (hit ▸ est)

/-- Every solution of the Volterra equation stays in any prescribed
sup-norm ball for all sufficiently small L² inputs. The neighborhood is
independent of the solution. -/
theorem fixed_paths_small (C : C(Time,E) → C(Time,U →L[ℝ] E)) (hc : ContinuousAt C 0)
    (pointwise : ∀ w z t, w t = z t → C w t = C z t) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ u : Causal.Signals U in 𝓝 0, ∀ w : C(Time,E), w = operator U E (C w) u → ‖w‖ < r := by
  have h := fixed_paths_small_with_parameter (P := ℝ) (fun _ => C)
    (ContinuousAt.comp (f := Prod.snd) hc continuousAt_snd) (fun _ => pointwise) hr
  have push : Tendsto (fun u : Causal.Signals U => ((0:ℝ),u)) (𝓝 0) (𝓝 0) :=
    (continuous_const.prodMk continuous_id).tendsto 0
  exact push h

#print axioms fixed_paths_small_with_parameter

#print axioms fixed_paths_small
end MinimizingSard.Volterra
