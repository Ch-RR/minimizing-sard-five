import ClockForward
import VolterraInverse

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace MinimizingSard.Five
open Volterra
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The time weight uses the integral of the actual coefficient bound. -/
def clockWeight (S : C(Time,ℝ)) (c : ℝ) : C(Time,E) →L[ℝ] C(Time,E) :=
  PathCalculus.multiplier Time E E ⟨fun t => Real.exp (c*S t) • ContinuousLinearMap.id ℝ E,by fun_prop⟩

private theorem clockWeight_inv (S : C(Time,ℝ)) (c : ℝ) :
    (clockWeight S c : C(Time,E) →L[ℝ] C(Time,E))*clockWeight S (-c) = 1 := by
  apply ContinuousLinearMap.ext
  intro h
  ext t : 1
  change Real.exp (c*S t) • (Real.exp (-c*S t) • h t) = h t
  rw [smul_smul,← Real.exp_add,neg_mul,add_neg_cancel,Real.exp_zero,one_smul]

private theorem clock_exponential_integral (ν : ℝ → ℝ) (iv : IntervalIntegrable ν volume 0 1)
    (nn : ∀ t, 0 ≤ ν t) (c : ℝ) (pos : 0 < c) (t : Time) :
    (∫ s in (0:ℝ)..(t:ℝ), ν s * Real.exp (c*arcClock ν s)) = (Real.exp (c*arcClock ν t)-1)/c := by
  let f (s : ℝ) := Real.exp (c*s)/c
  let b (s : ℝ) := Real.exp (c*s)
  have df (s : ℝ) : HasDerivAt f (b s) s := by
    simpa [f,b,pos.ne',mul_div_cancel_right₀] using (((hasDerivAt_id s).const_mul c).exp.div_const c)
  have cb : Continuous b := by dsimp [b]; fun_prop
  have h := forward_clock ν iv nn f b cb.continuousOn (fun s _ => (df s).hasDerivWithinAt) t t.property
  simp only [f,b,mul_zero,Real.exp_zero,smul_eq_mul] at h
  rw [sub_div]
  linarith

def integralClockPath (ν : ℝ → ℝ) (iv : IntervalIntegrable ν volume 0 1) : C(Time,ℝ) :=
  ⟨fun t => arcClock ν t,(continuousOn_iff_continuous_restrict.mp (continuousOn_arcClock iv))⟩

/-- An integral majorant of a continuous path. No pointwise boundedness
of the time-dependent coefficient is needed. -/
def IntegralMajorant (ν : ℝ → ℝ) (z h : C(Time,E)) : Prop :=
  ∀ t : Time, ‖z t‖ ≤ ∫ s in (0:ℝ)..(t:ℝ), ν s * ‖h (clamp s)‖

theorem clock_weight_bound (ν : ℝ → ℝ) (iv : IntervalIntegrable ν volume 0 1) (nn : ∀ t, 0 ≤ ν t)
    (c : ℝ) (pos : 0 < c) (z h : C(Time,E))
    (bound : IntegralMajorant ν z (clockWeight (integralClockPath ν iv) c h)) :
    ‖clockWeight (integralClockPath ν iv) (-c) z‖ ≤ c⁻¹ * ‖h‖ := by
  let S := integralClockPath ν iv
  let P := clockWeight S c (E := E)
  let b (r : ℝ) := Real.exp (c*arcClock ν r)
  have cb : ContinuousOn b (Icc 0 1) := Real.continuous_exp.continuousOn.comp
    (continuousOn_const.mul (continuousOn_arcClock iv)) (fun _ _ => mem_univ _)
  have i₁ := iv.mul_continuousOn (g := fun r => ‖P h (clamp r)‖)
    ((P h).continuous.comp (show Continuous clamp from continuous_projIcc)).norm.continuousOn
  have i₂ := iv.mul_continuousOn (g := b) (by rwa [uIcc_of_le zero_le_one])
  have subint {f : ℝ → ℝ} (i : IntervalIntegrable f volume 0 1) (t : Time) : IntervalIntegrable f volume 0 (t:ℝ) :=
    i.mono_set (by rw [uIcc_of_le t.property.1,uIcc_of_le zero_le_one]; exact Icc_subset_Icc le_rfl t.property.2)
  apply (ContinuousMap.norm_le _ (mul_nonneg (inv_nonneg.mpr pos.le) (norm_nonneg _))).mpr
  intro t
  have point (r : ℝ) (hr : r ∈ Icc 0 (t:ℝ)) :
      ν r * ‖P h (clamp r)‖ ≤ (ν r*b r)*‖h‖ := by
    have unit : r ∈ Icc (0:ℝ) 1 := ⟨hr.1,hr.2.trans t.property.2⟩
    change ν r*‖Real.exp (c*arcClock ν ((clamp r):ℝ)) • h (clamp r)‖ ≤ _
    rw [show ((clamp r):ℝ) = r from congrArg Subtype.val (projIcc_of_mem zero_le_one unit),
      norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),← mul_assoc]
    exact mul_le_mul_of_nonneg_left (h.norm_coe_le_norm _) (mul_nonneg (nn r) (Real.exp_pos _).le)
  have int := (bound t).trans (intervalIntegral.integral_mono_on t.property.1 (subint i₁ t)
    ((subint i₂ t).mul_const ‖h‖) point)
  rw [intervalIntegral.integral_mul_const] at int
  change ‖z t‖ ≤ (∫ s in (0:ℝ)..(t:ℝ), ν s*Real.exp (c*arcClock ν s))*‖h‖ at int
  rw [clock_exponential_integral ν iv nn c pos] at int
  change ‖Real.exp (-c*arcClock ν t) • z t‖ ≤ _
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),neg_mul,Real.exp_neg]
  apply (mul_le_mul_of_nonneg_left int (inv_pos.mpr (Real.exp_pos _)).le).trans
  have he := Real.exp_pos (c*arcClock ν t)
  calc (Real.exp (c*arcClock ν t))⁻¹ * ((Real.exp (c*arcClock ν t)-1)/c*‖h‖) ≤
       (Real.exp (c*arcClock ν t))⁻¹ * (Real.exp (c*arcClock ν t)/c*‖h‖) := by gcongr; linarith
       _ = c⁻¹ * ‖h‖ := by field_simp

/-- A Volterra operator majorized by any integrable, nonnegative
coefficient has invertible identity minus derivative on continuous paths. -/
theorem measured_volterra_isUnit [CompleteSpace E] (A : C(Time,E) →L[ℝ] C(Time,E))
    (ν : ℝ → ℝ) (iv : IntervalIntegrable ν volume 0 1) (nn : ∀ t, 0 ≤ ν t)
    (dom : ∀ h, IntegralMajorant ν (A h) h) : IsUnit (1-A) := by
  let S := integralClockPath ν iv
  let P : C(Time,E) →L[ℝ] C(Time,E) := clockWeight S 2
  let Q : C(Time,E) →L[ℝ] C(Time,E) := clockWeight S (-2)
  have pq : P*Q = 1 := clockWeight_inv S 2
  have qp : Q*P = 1 := by simpa only [neg_neg] using (clockWeight_inv (E := E) S (-2))
  let W : (C(Time,E) →L[ℝ] C(Time,E))ˣ := ⟨P,Q,pq,qp⟩
  have small : ‖Q*A*P‖ ≤ (2:ℝ)⁻¹ := (Q*A*P).opNorm_le_bound (by norm_num)
    (fun h => clock_weight_bound ν iv nn 2 (by norm_num) (A (P h)) h (dom (P h)))
  have unit := isUnit_one_sub_of_norm_lt_one (x := Q*A*P) (small.trans_lt (by norm_num))
  have id : 1-A = P*(1-Q*A*P)*Q := by
    rw [mul_sub,mul_one,sub_mul,pq]
    congr 1
    calc A = (P*Q)*A*(P*Q) := by rw [pq,one_mul,mul_one]
         _ = P*(Q*A*P)*Q := by simp only [mul_assoc]
  exact id ▸ (W.isUnit.mul unit).mul (W⁻¹).isUnit

/-- Two integral trajectories with the same initial value coincide whenever
the norm of their difference satisfies this integrable Volterra bound. -/
theorem zero_of_integral_majorant (ν : ℝ → ℝ) (iv : IntervalIntegrable ν volume 0 1)
    (nn : ∀ t, 0 ≤ ν t) (z : C(Time,E)) (dom : IntegralMajorant ν z z) : z = 0 := by
  let S := integralClockPath ν iv
  let P : C(Time,E) →L[ℝ] C(Time,E) := clockWeight S 2
  let Q : C(Time,E) →L[ℝ] C(Time,E) := clockWeight S (-2)
  have pq : P*Q = 1 := clockWeight_inv S 2
  have eq : P (Q z) = z := DFunLike.congr_fun pq z
  have b := clock_weight_bound ν iv nn 2 (by norm_num) z (Q z) (by change IntegralMajorant ν z (P (Q z)); rwa [eq])
  change ‖Q z‖ ≤ (2:ℝ)⁻¹ * ‖Q z‖ at b
  have h : Q z = 0 := norm_le_zero_iff.mp (by linarith)
  rwa [h,map_zero,eq_comm] at eq

#print axioms measured_volterra_isUnit
#print axioms zero_of_integral_majorant
end MinimizingSard.Five
