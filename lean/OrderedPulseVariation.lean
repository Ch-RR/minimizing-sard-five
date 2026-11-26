import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! Amplitude variations for the integral equation on one moving-frame
time patch. Time is only a continuous parameter of the pulled-back
fields. No differentiability of a solution in its amplitude is input. -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology Interval
namespace MinimizingSard.Pulse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A trajectory during a constant-amplitude pulse of a time-dependent field.
The reference is the zero-amplitude trajectory in moving coordinates. -/
def Solves (Y : ℝ → E → E) (x : E) (a b h : ℝ) (z : ℝ → E) : Prop :=
  ContinuousOn z (Icc a b) ∧ ∀ t ∈ Icc a b, z t = x + h • ∫ s in a..t, Y s (z s)

private theorem stays_in_ball {Y : ℝ → E → E} {x : E} {a b h R C : ℝ} {z : ℝ → E}
    (hab : a ≤ b) (hR : 0 < R) (hC : 0 ≤ C) (sol : Solves Y x a b h z)
    (bound : ∀ s ∈ Icc a b, ∀ y ∈ closedBall x R, ‖Y s y‖ ≤ C)
    (small : |h| * (C * (b-a)) < R) : ∀ t ∈ Icc a b, dist (z t) x < R := by
  let f : ℝ → ℝ := fun t => dist (z t) x
  have zc : ContinuousOn z (Icc a b) := sol.1
  have fc : ContinuousOn f (Icc a b) :=
    continuous_dist.comp_continuousOn (zc.prodMk continuousOn_const)
  have fa : f a = 0 := by simp [f, sol.2 a (left_mem_Icc.mpr hab)]
  have crossing (t : ℝ) (ht : t ∈ Icc a b) (bad : R ≤ f t) :
      ∃ k ∈ Icc a t, f k = R :=
    intermediate_value_Icc ht.1 (fc.mono (Icc_subset_Icc_right ht.2))
      (show R ∈ Icc (f a) (f t) from ⟨fa ▸ hR.le,bad⟩)
  intro t ht
  by_contra! bad
  obtain ⟨k,hk,he⟩ := crossing t ht bad
  let S := {k : Icc a b | f k = R}
  have closedS : IsClosed S := isClosed_eq (continuousOn_iff_continuous_restrict.mp fc) continuous_const
  obtain ⟨u,hu,first⟩ := closedS.isCompact.exists_isMinOn
    (show S.Nonempty from ⟨⟨k,hk.1,hk.2.trans ht.2⟩,he⟩) continuous_subtype_val.continuousOn
  have before (s : ℝ) (hs : s ∈ Icc a (u : ℝ)) : f s ≤ R := by
    by_contra! hs'
    obtain ⟨k',hk',hit⟩ := crossing s ⟨hs.1,hs.2.trans u.2.2⟩ hs'.le
    let v : Icc a b := ⟨k',hk'.1,hk'.2.trans (hs.2.trans u.2.2)⟩
    have earlier : (u : ℝ) ≤ k' := first (show v ∈ S from hit)
    have eq : k' = s := le_antisymm hk'.2 (hs.2.trans earlier)
    exact hs'.ne' (eq ▸ hit)
  have est := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := (u : ℝ))
    (f := fun s => Y s (z s)) (C := C) (by
      intro s hs
      rw [uIoc_of_le u.2.1] at hs
      exact bound s ⟨hs.1.le,hs.2.trans u.2.2⟩ _ (before s ⟨hs.1.le,hs.2⟩))
  rw [abs_of_nonneg (sub_nonneg.mpr u.2.1)] at est
  have normAt : f u = |h| * ‖∫ s in a..(u : ℝ), Y s (z s)‖ := by
    simp [f, dist_eq_norm, sol.2 u u.2, norm_smul]
  change f u = R at hu
  rw [← hu, normAt] at small
  exact small.not_ge (mul_le_mul_of_nonneg_left (est.trans (mul_le_mul_of_nonneg_left
    (sub_le_sub_right u.2.2 a) hC)) (abs_nonneg h))

omit [NormedSpace ℝ E] in
private theorem compact_bound {F : Type*} [NormedAddCommGroup F] [ProperSpace E]
    (Y : ℝ → E → F) (hc : Continuous Y.uncurry) (q : E) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a b, ∀ y ∈ closedBall q 1, ‖Y t y‖ ≤ C := by
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod (isCompact_closedBall q 1)).bddAbove_image
    hc.norm.continuousOn
  exact ⟨max 0 C, le_max_left _ _, fun t ht y hy =>
    (hC ⟨(t,y),⟨ht,hy⟩,rfl⟩).trans (le_max_right _ _)⟩

/-- The first amplitude derivative of an actual pulse endpoint. The
solution may be selected separately for each small positive or negative
amplitude. The integral equation is only required near zero. -/
theorem amplitude_derivative [ProperSpace E] (Y : ℝ → E → E)
    (hc : Continuous Y.uncurry) (q : E) {a b : ℝ} (hab : a ≤ b)
    (Z : ℝ → ℝ → E) (sol : ∀ᶠ h in 𝓝 (0 : ℝ), Solves Y q a b h (Z h)) :
    HasDerivAt (fun h => Z h b) (∫ s in a..b, Y s q) 0 := by
  obtain ⟨C,hC,bd⟩ := compact_bound Y hc q a b
  have close (r : ℝ) (hr : 0 < r) (h1 : r ≤ 1) :
      ∀ᶠ h in 𝓝 (0 : ℝ), ∀ s ∈ Icc a b, dist (Z h s) q < r := by
    have lim : ContinuousAt (fun h : ℝ => |h| * (C * (b-a))) 0 := by fun_prop
    have sm : ∀ᶠ h in 𝓝 (0 : ℝ), |h| * (C * (b-a)) < r :=
      lim.eventually_lt continuousAt_const (by simpa using hr)
    filter_upwards [sol,sm] with h hz hs using stays_in_ball hab hr hC hz
      (fun s hst y hy => bd s hst y (closedBall_subset_closedBall h1 hy)) hs
  have limit : Tendsto (fun h => ∫ s in a..b, Y s (Z h s)) (𝓝 0)
      (𝓝 (∫ s in a..b, Y s q)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε he
    let η := ε / (b-a+1)
    have pos : 0 < b-a+1 := by linarith
    have hη : 0 < η := div_pos he pos
    have uni := ((isCompact_Icc (a := a) (b := b)).prod (isCompact_closedBall q 1)).uniformContinuousOn_of_continuous
      hc.continuousOn
    obtain ⟨δ,hδ,modulus⟩ := Metric.uniformContinuousOn_iff.mp uni η hη
    filter_upwards [close (min 1 δ) (lt_min one_pos hδ) (min_le_left _ _),sol] with h near hz
    have c1 : ContinuousOn (fun s => Y s (Z h s)) (Icc a b) :=
      hc.comp_continuousOn (continuousOn_id.prodMk hz.1)
    have c2 : Continuous (fun s => Y s q) := hc.comp (continuous_id.prodMk continuous_const)
    rw [dist_eq_norm, ← intervalIntegral.integral_sub (c1.intervalIntegrable_of_Icc hab)
      (c2.intervalIntegrable a b)]
    have est := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
      (f := fun s => Y s (Z h s) - Y s q) (C := η) (by
        intro s hs
        rw [uIoc_of_le hab] at hs
        have hs' : s ∈ Icc a b := ⟨hs.1.le,hs.2⟩
        have hnear := near s hs'
        have one : dist (Z h s) q < 1 := hnear.trans_le (min_le_left _ _)
        have delta := hnear.trans_le (min_le_right _ _)
        have diff := modulus (x := (s,Z h s)) ⟨hs',one.le⟩
          (y := (s,q)) ⟨hs', mem_closedBall_self zero_le_one⟩ (by simpa [Prod.dist_eq] using delta)
        simpa only [dist_eq_norm] using
          (le_of_lt diff : dist (Y s (Z h s)) (Y s q) ≤ η))
    rw [abs_of_nonneg (sub_nonneg.mpr hab)] at est
    exact est.trans_lt (by
      have e : η * (b-a+1) = ε := div_mul_cancel₀ _ pos.ne'
      linarith)
  have base := (sol.self_of_nhds).2 b (right_mem_Icc.mpr hab)
  simp only [zero_smul, add_zero] at base
  apply hasDerivAt_iff_tendsto_slope.mpr
  apply (limit.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [sol.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with h hz hn
  have hne : h ≠ 0 := hn
  simp [slope, base, hz.2 b (right_mem_Icc.mpr hab), hne]

#print axioms amplitude_derivative

/-- Coordinate field for one pulse interval. In the target application
it is a local extension of a column transported by the reference flow. -/
structure Window (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  a : ℝ
  b : ℝ
  ordered : a ≤ b
  Y : ℝ → E → E
  value_cont : Continuous Y.uncurry
  space_diff : ∀ t ∈ Icc a b, Differentiable ℝ (Y t)
  jac_cont : Continuous (fun p : ℝ × E => fderiv ℝ (Y p.1) p.2)

def Window.average (P : Window E) (x : E) := ∫ t in P.a..P.b, P.Y t x

theorem Window.average_derivative [ProperSpace E] (P : Window E) (x : E) :
    HasFDerivAt P.average (∫ t in P.a..P.b, fderiv ℝ (P.Y t) x) x := by
  have val (y : E) : Continuous (fun t => P.Y t y) :=
    P.value_cont.comp (continuous_id.prodMk continuous_const)
  have jac : Continuous (fun t => fderiv ℝ (P.Y t) x) :=
    P.jac_cont.comp (continuous_id.prodMk continuous_const)
  obtain ⟨C,_,bound⟩ := compact_bound (fun t y => fderiv ℝ (P.Y t) y) P.jac_cont x P.a P.b
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun y t => P.Y t y) (F' := fun y t => fderiv ℝ (P.Y t) y)
    (bound := fun _ => C) (ε := 1) one_pos (.of_forall fun y => (val y).aestronglyMeasurable)
    ((val x).intervalIntegrable _ _) jac.aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro t ht y hy
    rw [uIoc_of_le P.ordered] at ht
    exact bound t ⟨ht.1.le,ht.2⟩ y (ball_subset_closedBall hy)
  · exact intervalIntegrable_const
  · apply Filter.Eventually.of_forall
    intro t ht y _
    rw [uIoc_of_le P.ordered] at ht
    exact (P.space_diff t ⟨ht.1.le,ht.2⟩ y).hasFDerivAt

def Window.FamilyNear (P : Window E) (q : E) (Z : E → ℝ → ℝ → E) : Prop :=
  ∀ᶠ x in 𝓝 q, ∀ᶠ h in 𝓝 (0 : ℝ), Solves P.Y x P.a P.b h (Z x h)

/-- Endpoint after traversing the two indicated pulse windows in order.
This is also defined for the reversed experiment without extending its
chronology to the original control problem. -/
def orderedEndpoint (P Q : Window E) (Z W : E → ℝ → ℝ → E) (q : E) (h k : ℝ) : E :=
  W (Z q h P.b) k Q.b

theorem ordered_mixed_derivative [ProperSpace E] (P Q : Window E) (q : E)
    (Z W : E → ℝ → ℝ → E) (hZ : P.FamilyNear q Z) (hW : Q.FamilyNear q W) :
    HasDerivAt (fun h => deriv (orderedEndpoint P Q Z W q h) 0)
      (fderiv ℝ Q.average q (P.average q)) 0 := by
  have hz := hZ.self_of_nhds
  have first := amplitude_derivative P.Y P.value_cont q P.ordered (Z q) hz
  have base := hz.self_of_nhds.2 P.b (right_mem_Icc.mpr P.ordered)
  simp only [zero_smul, add_zero] at base
  have hit : Tendsto (fun h => Z q h P.b) (𝓝 0) (𝓝 q) := by
    have lim : Tendsto (fun h => Z q h P.b) (𝓝 0) (𝓝 (Z q 0 P.b)) := first.continuousAt
    rwa [base] at lim
  have near : (fun h => deriv (orderedEndpoint P Q Z W q h) 0) =ᶠ[𝓝 0]
      (fun h => Q.average (Z q h P.b)) := by
    filter_upwards [hit.eventually hW] with h hw
    exact (amplitude_derivative Q.Y Q.value_cont _ Q.ordered _ hw).deriv
  have dQ := (Q.average_derivative (Z q 0 P.b)).differentiableAt.hasFDerivAt
  have mixed := (dQ.comp_hasDerivAt 0 first).congr_of_eventuallyEq near
  rw [base] at mixed
  exact mixed

private theorem Window.bracket_average_left [ProperSpace E] (P : Window E) (W : E → E) (q : E) :
    VectorField.lieBracket ℝ P.average W q =
      ∫ t in P.a..P.b, VectorField.lieBracket ℝ (P.Y t) W q := by
  have val : Continuous (fun t => P.Y t q) :=
    P.value_cont.comp (continuous_id.prodMk continuous_const)
  have jac : Continuous (fun t => fderiv ℝ (P.Y t) q) :=
    P.jac_cont.comp (continuous_id.prodMk continuous_const)
  simp only [VectorField.lieBracket, (P.average_derivative q).fderiv, Window.average]
  rw [ContinuousLinearMap.intervalIntegral_apply (jac.intervalIntegrable _ _),
    ← ContinuousLinearMap.intervalIntegral_comp_comm _ (val.intervalIntegrable _ _)]
  apply (intervalIntegral.integral_sub _ _).symm
  · exact (((fderiv ℝ W q).continuous.comp val).intervalIntegrable _ _)
  · exact ((jac.clm_apply continuous_const).intervalIntegrable _ _)

private theorem Window.bracket_average_right [ProperSpace E] (P : Window E) (W : E → E) (q : E) :
    VectorField.lieBracket ℝ W P.average q =
      ∫ t in P.a..P.b, VectorField.lieBracket ℝ W (P.Y t) q := by
  rw [VectorField.lieBracket_swap, P.bracket_average_left, ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro t _
  exact (VectorField.lieBracket_swap (𝕜 := ℝ) (V := W) (W := P.Y t)).symm

/-- The chronological mixed amplitude derivative minus its reversed-order
correction is exactly the double integral of the mixed-time Lie bracket.
All amplitude derivatives below are derivatives of actual solution endpoints. -/
theorem pulse_rectangle_bracket [ProperSpace E] (P Q : Window E) (q : E)
    (Z W : E → ℝ → ℝ → E) (hZ : P.FamilyNear q Z) (hW : Q.FamilyNear q W) :
    deriv (fun h => deriv (orderedEndpoint P Q Z W q h) 0) 0 -
      deriv (fun k => deriv (orderedEndpoint Q P W Z q k) 0) 0 =
      ∫ t in Q.a..Q.b, ∫ s in P.a..P.b, VectorField.lieBracket ℝ (P.Y s) (Q.Y t) q := by
  rw [(ordered_mixed_derivative P Q q Z W hZ hW).deriv,
    (ordered_mixed_derivative Q P q W Z hW hZ).deriv]
  change VectorField.lieBracket ℝ P.average Q.average q = _
  rw [Q.bracket_average_right]
  exact intervalIntegral.integral_congr (fun t _ => P.bracket_average_left (Q.Y t) q)

#print axioms ordered_mixed_derivative
#print axioms pulse_rectangle_bracket

variable {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]

/-- Recover the actual Fréchet Hessian on two control directions from
equality of local endpoint values on their amplitude plane. -/
theorem hessian_on_amplitude_plane (F : U → E) (hf : ContDiffAt ℝ 2 F 0)
    (v w : U) (G : ℝ → ℝ → E)
    (graph : ∀ᶠ h in 𝓝 (0 : ℝ), G h =ᶠ[𝓝 0] fun k => F (h • v + k • w)) :
    HasDerivAt (fun h => deriv (G h) 0) ((fderiv ℝ (fderiv ℝ F) 0 v) w) 0 := by
  have line : HasDerivAt (fun h : ℝ => h • v) v 0 := by
    simpa only [one_smul] using (hasDerivAt_id' (0 : ℝ)).smul_const v
  have lim : Tendsto (fun h : ℝ => h • v) (𝓝 0) (𝓝 0) := by
    simpa only [zero_smul] using line.continuousAt.tendsto
  have near : (fun h => deriv (G h) 0) =ᶠ[𝓝 0] fun h : ℝ => (fderiv ℝ F (h • v)) w := by
    filter_upwards [graph,lim.eventually (hf.eventually (by decide))] with h hh hF
    have line2 : HasDerivAt (fun k : ℝ => h • v + k • w) w 0 := by
      simpa only [zero_add,one_smul] using
        (hasDerivAt_const (0 : ℝ) (h • v)).add ((hasDerivAt_id' (0 : ℝ)).smul_const w)
    have atBase : DifferentiableAt ℝ F (h • v + (0 : ℝ) • w) := by
      simpa using hF.differentiableAt (by decide)
    simpa only [zero_smul,add_zero] using
      ((atBase.hasFDerivAt.comp_hasDerivAt 0 line2).congr_of_eventuallyEq hh).deriv
  have jac : DifferentiableAt ℝ (fderiv ℝ F) ((0 : ℝ) • v) := by
    simpa only [zero_smul] using (hf.fderiv_right (m := 1) (by decide)).differentiableAt (by decide)
  have hd := ((ContinuousLinearMap.apply ℝ E w).hasFDerivAt.comp_hasDerivAt 0
    (jac.hasFDerivAt.comp_hasDerivAt 0 line))
  apply HasDerivAt.congr_of_eventuallyEq _ near
  simpa only [zero_smul] using hd

/-- Only the chronological experiment has to agree with the original
endpoint map. The separable correction is computed from the two fields. -/
theorem corrected_endpoint_hessian_on_pulses [ProperSpace E]
    (F : U → E) (hf : ContDiffAt ℝ 2 F 0) (v w : U)
    (P Q : Window E) (q : E) (Z W : E → ℝ → ℝ → E)
    (hZ : P.FamilyNear q Z) (hW : Q.FamilyNear q W)
    (graph : ∀ᶠ h in 𝓝 (0 : ℝ), orderedEndpoint P Q Z W q h =ᶠ[𝓝 0]
      fun k => F (h • v + k • w)) :
    (fderiv ℝ (fderiv ℝ F) 0 v) w -
      (∫ s in P.a..P.b, fderiv ℝ (P.Y s) q) (∫ t in Q.a..Q.b, Q.Y t q) =
      ∫ t in Q.a..Q.b, ∫ s in P.a..P.b, VectorField.lieBracket ℝ (P.Y s) (Q.Y t) q := by
  have hess := (hessian_on_amplitude_plane F hf v w _ graph).deriv
  have hrev := (ordered_mixed_derivative Q P q W Z hW hZ).deriv
  rw [(P.average_derivative q).fderiv] at hrev
  simpa only [hess,hrev,Window.average] using pulse_rectangle_bracket P Q q Z W hZ hW

#print axioms hessian_on_amplitude_plane
#print axioms corrected_endpoint_hessian_on_pulses
end MinimizingSard.Pulse
