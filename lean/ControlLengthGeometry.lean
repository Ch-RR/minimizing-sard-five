import PointedLengthValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace MinimizingSard.Five

private abbrev μ := volume.restrict (Icc (0 : ℝ) 1)

private instance : IsProbabilityMeasure μ := ⟨by simp [μ, Real.volume_Icc]⟩

/-- On the unit time interval, the inclusion of L² into L¹ is a contraction. -/
private def timeInclusion (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Lp E 2 μ →L[ℝ] Lp E 1 μ := by
  let incl (u : Lp E 2 μ) := ((Lp.memLp u).integrable (by norm_num)).toL1 u
  have rep (u : Lp E 2 μ) : ⇑(incl u) =ᵐ[μ] ⇑u := Integrable.coeFn_toL1 _
  let A : Lp E 2 μ →ₗ[ℝ] Lp E 1 μ :=
    { toFun := incl
      map_add' := by
        intro u v
        apply Lp.ext
        filter_upwards [rep (u+v), Lp.coeFn_add u v, Lp.coeFn_add (incl u) (incl v),
          rep u, rep v] with t h₁ h₂ h₃ h₄ h₅
        change incl (u + v) t = (incl u + incl v) t
        rw [h₁,h₂,h₃,Pi.add_apply,Pi.add_apply,h₄,h₅]
      map_smul' := by
        intro r u
        apply Lp.ext
        filter_upwards [rep (r • u), Lp.coeFn_smul r u, Lp.coeFn_smul r (incl u),
          rep u] with t h₁ h₂ h₃ h₄
        change incl (r • u) t = (r • incl u) t
        rw [h₁,h₂,h₃,Pi.smul_apply,Pi.smul_apply,h₄] }
  refine A.mkContinuous 1 (fun u => ?_)
  change ‖incl u‖ ≤ 1 * ‖u‖
  rw [one_mul,Lp.norm_def,Lp.norm_def,eLpNorm_congr_ae (rep u)]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top u)
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) (Lp.memLp u).1)

private def lengthMap (m : ℕ) : Control m →L[ℝ] Lp (EuclideanSpace ℝ (Fin m)) 1 μ :=
  (timeInclusion _).comp ((EuclideanSpace.equiv (Fin m) ℝ).symm.toContinuousLinearMap.compLpL 2 μ)

private theorem length_as_sum {m n : ℕ} (u : Fin n → Control m) :
    length u = ∑ i, ‖lengthMap m (u i)‖ := by
  unfold length
  apply Finset.sum_congr rfl
  intro i _
  rw [intervalIntegral.integral_of_le zero_le_one,Measure.restrict_congr_set Ioc_ae_eq_Icc,
    L1.norm_eq_integral_norm]
  let T := (EuclideanSpace.equiv (Fin m) ℝ).symm.toContinuousLinearMap
  have rep : ⇑(lengthMap m (u i)) =ᵐ[μ] ⇑(T.compLp (u i)) :=
    Integrable.coeFn_toL1 ((Lp.memLp (T.compLp (u i))).integrable (by norm_num))
  apply integral_congr_ae
  filter_upwards [rep,T.coeFn_compLp (u i)] with t h₁ h₂
  rw [h₁,h₂]
  change Real.sqrt (speedSq _) = ‖(EuclideanSpace.equiv (Fin m) ℝ).symm _‖
  rw [EuclideanSpace.norm_eq]
  simp only [speedSq,Real.norm_eq_abs,sq_abs]
  rfl

theorem continuous_control_length {m n : ℕ} : Continuous (length (m := m) (n := n)) := by
  simp_rw [show length (m := m) (n := n) = _ from funext length_as_sum]
  exact continuous_finset_sum _ fun i _ => ((lengthMap m).continuous.comp (continuous_apply i)).norm

theorem convex_control_length {m n : ℕ} : ConvexOn ℝ univ (length (m := m) (n := n)) := by
  refine ⟨convex_univ, ?_⟩
  intro u _ v _ a b ha hb _
  simp only [length_as_sum, Pi.add_apply, Pi.smul_apply, map_add, map_smul,
    smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  exact (norm_add_le _ _).trans_eq (by rw [norm_smul,norm_smul,Real.norm_eq_abs,
    Real.norm_eq_abs,abs_of_nonneg ha,abs_of_nonneg hb])

#print axioms continuous_control_length
#print axioms convex_control_length
end MinimizingSard.Five
