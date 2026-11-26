import PulseEndpointGraph
import Mathlib.Analysis.ODE.PicardLindelof

/-! Obtain all pulse families from the field data by Picard–Lindelöf.
Time differentiability of the fields is unnecessary. -/
noncomputable section
open Set MeasureTheory Filter Metric ODE
open scoped Topology
open MinimizingSard.Pulse
namespace MinimizingSard.PulseGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private theorem bound_on_tube {G : Type*} [NormedAddCommGroup G] (P : Window E)
    (q : E) (f : ℝ × E → G) (hf : Continuous f) :
    ∃ C : NNReal, ∀ t ∈ Icc P.a P.b, ∀ x ∈ closedBall q 1, ‖f (t,x)‖ ≤ C := by
  obtain ⟨C,bc⟩ := (isCompact_Icc.prod (isCompact_closedBall q 1)).bddAbove_image
    (hf.norm.continuousOn (s := Icc P.a P.b ×ˢ closedBall q 1))
  exact ⟨Real.toNNReal C, fun t ht x hx => (bc ⟨(t,x),⟨ht,hx⟩,rfl⟩).trans
    (Real.le_coe_toNNReal _)⟩

theorem pulse_family_exists (P : Window E) (q : E) :
    ∃ Z, P.FamilyNear q Z := by
  classical
  obtain ⟨C,bc⟩ := bound_on_tube P q _ P.value_cont
  obtain ⟨K,bk⟩ := bound_on_tube P q _ P.jac_cont
  let start : Icc P.a P.b := ⟨P.a,le_rfl,P.ordered⟩
  let r : NNReal := 1 / 2
  have rad : (0 : ℝ) < r := by norm_num [r]
  have small : ∀ᶠ h in 𝓝 (0 : ℝ), ‖h‖ * C * (P.b - P.a) < 1 / 2 := by
    have cont : ContinuousAt (fun h : ℝ => ‖h‖ * C * (P.b - P.a)) 0 := by fun_prop
    exact cont.eventually_lt continuousAt_const (by norm_num)
  have existence (x : E) (h : ℝ) (hx : x ∈ closedBall q r)
      (hh : ‖h‖ * C * (P.b - P.a) < 1 / 2) : ∃ z, Solves P.Y x P.a P.b h z := by
    let V (t : ℝ) (x : E) := h • P.Y t x
    have pl : IsPicardLindelof V start q 1 r (‖h‖₊ * C) (‖h‖₊ * K) := by
      constructor
      · intro t ht
        have lip : LipschitzOnWith K (P.Y t) (closedBall q 1) :=
          (convex_closedBall q 1).lipschitzOnWith_of_nnnorm_fderiv_le
            (fun x _ => P.space_diff t ht x) (fun x hx => bk t ht x hx)
        exact (lipschitzWith_smul h).comp_lipschitzOnWith lip
      · intro x _
        exact (continuous_const.smul (P.value_cont.comp (continuous_id.prodMk
          (continuous_const (y := x))))).continuousOn
      · intro t ht y hy
        change ‖h • P.Y t y‖ ≤ ‖h‖ * (C : ℝ)
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (bc t ht y hy) (norm_nonneg h)
      · change (‖h‖ * (C : ℝ)) * max (P.b-P.a) (P.a-P.a) ≤ 1 - (r : ℝ)
        simp only [sub_self, max_eq_left (sub_nonneg.mpr P.ordered)]
        simpa [r] using (show ‖h‖ * C * (P.b-P.a) ≤ 1 - ((1 : ℝ)/2) by linarith)
    obtain ⟨α,hα⟩ := FunSpace.exists_isFixedPt_next pl hx
    let β := FunSpace.next pl hx α
    refine ⟨β.compProj,β.continuous_compProj.continuousOn,?_⟩
    intro t ht
    have fp : β.compProj t = ODE.picard V start x β.compProj t := by
      dsimp only [β]
      rw [FunSpace.compProj_apply,FunSpace.next_apply,hα,projIcc_of_mem _ ht]
    simpa only [ODE.picard_apply,V,start,intervalIntegral.integral_smul] using fp
  refine ⟨fun x h => Classical.epsilon (Solves P.Y x P.a P.b h),?_⟩
  filter_upwards [ball_mem_nhds q rad] with x hx
  filter_upwards [small] with h hh
  exact Classical.epsilon_spec (existence x h (ball_subset_closedBall hx) hh)

/-- Endpoint exclusion on a moving-frame patch; no pulse solutions,
chronological agreement, or finite-rank auxiliary operator are input. -/
theorem moving_endpoint_kills_triples (X : Columns E) (q : E) (F : Controls → E)
    (p : E →L[ℝ] ℝ) (endpoint : X.Endpoint q F) (smooth : ContDiffAt ℝ 2 F 0)
    [FiniteDimensional ℝ (LinearMap.range (restrictedHessianRow F p))]
    (B : ℝ → E → E) (u v : ℝ → ℝ) (hend : B 1 = VectorField.lieBracket ℝ (X.Y 0 1) (X.Y 1 1))
    (hB : ContinuousOn (fun t => MixedTime.jet (B t) q) (Icc 0 1))
    (flow : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1),
      HasDerivAt (fun s => MixedTime.jet (X.Y 0 s) q) (-(v t) • MixedTime.jet (B t) q) t ∧
      HasDerivAt (fun s => MixedTime.jet (X.Y 1 s) q) (u t • MixedTime.jet (B t) q) t ∧
      (u t ≠ 0 ∨ v t ≠ 0)) :
    ∀ i, p (VectorField.lieBracket ℝ (X.Y i 1)
      (VectorField.lieBracket ℝ (X.Y 0 1) (X.Y 1 1)) q) = 0 := by
  choose Z hZ using fun i => pulse_family_exists (X.window i) q
  exact integral_endpoint_kills_triples X q F p endpoint smooth Z hZ B u v hend hB flow

#print axioms pulse_family_exists
#print axioms moving_endpoint_kills_triples

/-- The rank-two flag through order three at the terminal point. -/
def thirdLayer (X : Columns E) (q : E) : Submodule ℝ E :=
  let B := VectorField.lieBracket ℝ (X.Y 0 1) (X.Y 1 1)
  Submodule.span ℝ (range (fun i => X.Y i 1 q) ∪ {B q} ∪
    range (fun i => VectorField.lieBracket ℝ (X.Y i 1) B q))

/-- A finite-rank row of the intrinsic Hessian annihilates the whole
displayed third layer in moving coordinates. The column and first-bracket
conclusions are derived from the first variation, the third-order ones
from the pulse Hessian and the reference-flow jet identities. -/
theorem finite_row_annihilates_third_layer (X : Columns E) (q : E) (F : Controls → E)
    (p : E →L[ℝ] ℝ) (endpoint : X.Endpoint q F) (smooth : ContDiffAt ℝ 2 F 0)
    (row : ∀ v, p (fderiv ℝ F 0 v) = 0)
    [FiniteDimensional ℝ (LinearMap.range (restrictedHessianRow F p))]
    (B : ℝ → E → E) (u v : ℝ → ℝ) (hend : B 1 = VectorField.lieBracket ℝ (X.Y 0 1) (X.Y 1 1))
    (hB : ContinuousOn (fun t => MixedTime.jet (B t) q) (Icc 0 1))
    (flow : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1),
      HasDerivAt (fun s => MixedTime.jet (X.Y 0 s) q) (-(v t) • MixedTime.jet (B t) q) t ∧
      HasDerivAt (fun s => MixedTime.jet (X.Y 1 s) q) (u t • MixedTime.jet (B t) q) t ∧
      (u t ≠ 0 ∨ v t ≠ 0)) : thirdLayer X q ≤ LinearMap.ker p.toLinearMap := by
  choose Z hZ using fun i => pulse_family_exists (X.window i) q
  have graph := graph_of_integral_endpoint X q F endpoint Z hZ
  have cols := annihilates_columns X F q p (smooth.differentiableAt (by decide)) row Z hZ graph
  let L := p.comp (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E))
  have bracket := MixedTime.row_zero_of_two_columns L
    (fun t => MixedTime.jet (X.Y 0 t) q) (fun t => MixedTime.jet (X.Y 1 t) q)
    (fun t => MixedTime.jet (B t) q) u v zero_lt_one hB
    (fun t ht => ⟨cols 0 t (Ioo_subset_Icc_self ht),cols 1 t (Ioo_subset_Icc_self ht)⟩) flow
  have triple := finite_hessian_kills_triples X F q p smooth Z hZ graph B u v hend hB flow
  apply Submodule.span_le.mpr
  rintro x ((⟨i,rfl⟩ | hx) | ⟨i,rfl⟩)
  · exact cols i 1 ⟨zero_le_one,le_rfl⟩
  · obtain rfl := Set.mem_singleton_iff.mp hx
    change p (B 1 q) = 0 at bracket
    rwa [hend] at bracket
  · exact triple i

#print axioms finite_row_annihilates_third_layer
end MinimizingSard.PulseGeometry
