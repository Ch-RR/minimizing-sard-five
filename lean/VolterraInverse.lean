import SmoothShortFlow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace MinimizingSard.Five
open Volterra
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def pathWeight (c : ℝ) : C(Time,E) →L[ℝ] C(Time,E) :=
  PathCalculus.multiplier Time E E ⟨fun t => Real.exp (c*(t:ℝ)) • ContinuousLinearMap.id ℝ E,by fun_prop⟩

def pathVolterra (D : C(Time,E →L[ℝ] E)) : C(Time,E) →L[ℝ] C(Time,E) :=
  integralPath.comp (PathCalculus.multiplier Time E E D)

omit [CompleteSpace E] in
private theorem weight_inverse (c : ℝ) :
    (pathWeight c : C(Time,E) →L[ℝ] C(Time,E))*pathWeight (-c) = 1 := by
  apply ContinuousLinearMap.ext
  intro h
  ext t : 1
  change Real.exp (c*(t:ℝ)) • (Real.exp (-c*(t:ℝ)) • h t) = h t
  rw [smul_smul,← Real.exp_add,neg_mul,add_neg_cancel,Real.exp_zero,one_smul]

private theorem exp_int {c : ℝ} (hc : 0 < c) (t : ℝ) :
    (∫ s in (0:ℝ)..t, Real.exp (c*s)) = (Real.exp (c*t)-1)/c := by
  have deriv (s : ℝ) : HasDerivAt (fun r => Real.exp (c*r)/c) (Real.exp (c*s)) s := by
    simpa [hc.ne',mul_div_cancel_right₀] using (((hasDerivAt_id s).const_mul c).exp.div_const c)
  have cont : Continuous (fun r => Real.exp (c*r)) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => deriv s) (cont.intervalIntegrable _ _)]
  simp [sub_div]

omit [CompleteSpace E] in
/-- The Volterra derivative is conjugate to a strict contraction by exponential
weights. This bound holds for arbitrarily long paths and large coefficients. -/
theorem weighted_volterra_bound (D : C(Time,E →L[ℝ] E)) (c : ℝ) (hc : 0 < c) :
    ‖pathWeight (-c) * pathVolterra D * pathWeight c‖ ≤ ‖D‖/c := by
  let A := pathWeight (-c) * pathVolterra D * pathWeight c
  apply A.opNorm_le_bound (div_nonneg (norm_nonneg D) hc.le)
  intro h
  apply (ContinuousMap.norm_le _ (mul_nonneg (div_nonneg (norm_nonneg _) hc.le) (norm_nonneg h))).mpr
  intro t
  let v := PathCalculus.multiplier Time E E D (pathWeight c h)
  let C := ‖D‖*‖h‖
  have posC : 0 ≤ C := mul_nonneg (norm_nonneg D) (norm_nonneg h)
  have point (s : ℝ) (hs : s ∈ Icc 0 (t:ℝ)) : ‖v (clamp s)‖ ≤ C*Real.exp (c*s) := by
    have unit : s ∈ Icc (0:ℝ) 1 := ⟨hs.1,hs.2.trans t.property.2⟩
    change ‖D (clamp s) (Real.exp (c*((clamp s):ℝ)) • h (clamp s))‖ ≤ _
    have atS : ((clamp s):ℝ) = s := congrArg Subtype.val (projIcc_of_mem zero_le_one unit)
    rw [atS]
    apply ((D (clamp s)).le_opNorm _).trans
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    calc ‖D (clamp s)‖ * (Real.exp (c*s)*‖h (clamp s)‖) ≤ ‖D‖*(Real.exp (c*s)*‖h‖) :=
          mul_le_mul (D.norm_coe_le_norm _) (mul_le_mul_of_nonneg_left (h.norm_coe_le_norm _) (Real.exp_pos _).le)
            (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) (norm_nonneg D)
         _ = C*Real.exp (c*s) := by dsimp [C]; ring
  have cv : Continuous (fun s => v (clamp s)) := v.continuous.comp continuous_projIcc
  have ce : Continuous (fun s : ℝ => Real.exp (c*s)) := by fun_prop
  have bound := (intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := fun s => v (clamp s)) t.property.1).trans
    (intervalIntegral.integral_mono_on t.property.1 (cv.norm.intervalIntegrable _ _)
      ((ce.intervalIntegrable _ _).const_mul C) point)
  rw [intervalIntegral.integral_const_mul,exp_int hc] at bound
  change ‖Real.exp (-c*(t:ℝ)) • (∫ s in (0:ℝ)..(t:ℝ), v (clamp s))‖ ≤ _
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),neg_mul,Real.exp_neg]
  apply (mul_le_mul_of_nonneg_left bound (inv_pos.mpr (Real.exp_pos _)).le).trans
  have hExp := Real.exp_pos (c*(t:ℝ))
  calc (Real.exp (c*(t:ℝ)))⁻¹*(C*((Real.exp (c*(t:ℝ))-1)/c)) ≤
        (Real.exp (c*(t:ℝ)))⁻¹*(C*(Real.exp (c*(t:ℝ))/c)) := by gcongr; linarith
       _ = ‖D‖/c*‖h‖ := by dsimp [C]; field_simp

theorem volterra_isUnit (D : C(Time,E →L[ℝ] E)) :
    IsUnit (1 - pathVolterra D) := by
  let c := ‖D‖+1
  have hc : 0 < c := by dsimp [c]; positivity
  let P : C(Time,E) →L[ℝ] C(Time,E) := pathWeight c
  let Q : C(Time,E) →L[ℝ] C(Time,E) := pathWeight (-c)
  have pq : P*Q = 1 := weight_inverse c
  have qp : Q*P = 1 := by simpa only [neg_neg] using (weight_inverse (E := E) (-c))
  let W : (C(Time,E) →L[ℝ] C(Time,E))ˣ := ⟨P,Q,pq,qp⟩
  have bound : ‖Q*pathVolterra D*P‖ < 1 :=
    (weighted_volterra_bound D c hc).trans_lt ((div_lt_one hc).mpr (by dsimp [c]; linarith))
  have unit : IsUnit (1-Q*pathVolterra D*P) := isUnit_one_sub_of_norm_lt_one (x := Q*pathVolterra D*P) bound
  have id : 1-pathVolterra D = P*(1-Q*pathVolterra D*P)*Q := by
    rw [mul_sub,mul_one,sub_mul,pq]
    congr 1
    calc pathVolterra D = (P*Q)*pathVolterra D*(P*Q) := by rw [pq,one_mul,mul_one]
         _ = P*(Q*pathVolterra D*P)*Q := by simp only [mul_assoc]
  exact id ▸ (W.isUnit.mul unit).mul (W⁻¹).isUnit

#print axioms weighted_volterra_bound
#print axioms volterra_isUnit
end MinimizingSard.Five
