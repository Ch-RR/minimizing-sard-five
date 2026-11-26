import SegmentPasting
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section
open Set MeasureTheory
namespace MinimizingSard.Five.TimePartition

variable {m n : ℕ}

/-- The length in the specification uses Euclidean speed, although the
control space itself uses the ordinary Pi norm on its finite-dimensional fiber. -/
private theorem euclidean_speed (v : Fiber m) :
    Real.sqrt (speedSq v) = ‖(EuclideanSpace.equiv (Fin m) ℝ).symm v‖ := by
  rw [EuclideanSpace.norm_eq]
  simp only [speedSq,Real.norm_eq_abs,sq_abs]
  rfl

private theorem speed_integrable (u : Control m) :
    IntervalIntegrable (fun s => Real.sqrt (speedSq (u s))) volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr
  simp_rw [euclidean_speed]
  exact ((EuclideanSpace.equiv (Fin m) ℝ).symm.toContinuousLinearMap.integrable_comp
    ((Lp.memLp u).integrable (by norm_num))).norm

private theorem telescope (f : Fin (n+1) → ℝ) :
    (∑ i : Fin n, (f i.succ - f i.castSucc)) = f (Fin.last n) - f 0 := by
  rw [Finset.sum_sub_distrib]
  linarith [Fin.sum_univ_succ f,Fin.sum_univ_castSucc f]

/-- Equality of the original sub-Riemannian lengths for any tuple with
the a.e. rescaling formula, using all the control channels. -/
theorem length_eq_of_rescaling (P : TimePartition n) (u : Control m) (v : Fin n → Control m)
    (rep : ∀ i, ∀ᵐ t ∂volume.restrict (Icc (0:ℝ) 1),
      v i t = P.duration i • u (P.left i + P.duration i*t)) :
    length v = length (fun _ : Fin 1 => u) := by
  let f := fun t => Real.sqrt (speedSq (u t))
  let F (j : Fin (n+1)) := ∫ t in (0:ℝ)..P.cut j, f t
  have sub (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) : IntervalIntegrable f volume a b :=
    (speed_integrable u).mono_set (by
      rw [uIcc_of_le hab,uIcc_of_le zero_le_one]; exact Icc_subset_Icc ha hb)
  have each (i : Fin n) : (∫ t in (0:ℝ)..1, Real.sqrt (speedSq (v i t))) = F i.succ - F i.castSucc := by
    have d := P.duration_pos i
    have eq : (fun t => Real.sqrt (speedSq (v i t))) =ᵐ[volume.restrict (uIoc (0:ℝ) 1)]
        (fun t => P.duration i • f (P.left i+P.duration i*t)) := by
      rw [uIoc_of_le zero_le_one,Measure.restrict_congr_set Ioc_ae_eq_Icc]
      filter_upwards [rep i] with t ht
      simp only [f,ht,euclidean_speed,map_smul,norm_smul,Real.norm_eq_abs,abs_of_pos d,smul_eq_mul]
    rw [intervalIntegral.integral_congr_ae_restrict eq,intervalIntegral.integral_smul,
      intervalIntegral.smul_integral_comp_add_mul]
    simp only [mul_zero,add_zero,mul_one,P.end_eq]
    have add := intervalIntegral.integral_add_adjacent_intervals
      (sub 0 (P.left i) le_rfl (P.cut_mem _).1 (P.cut_mem _).2)
      (sub (P.left i) (P.cut i.succ) (P.cut_mem _).1
        ((P.increasing (Fin.castSucc_lt_succ i)).le) (P.cut_mem _).2)
    exact eq_sub_of_add_eq' add
  change (∑ i, ∫ t in (0:ℝ)..1, Real.sqrt (speedSq (v i t))) = _
  simp_rw [each]
  rw [telescope]
  simp [F,P.first,P.last,length,f]

/-- One and the same change of controls preserves both length and singularity. -/
theorem length_and_singularity {M : Type*} [TopologicalSpace M] [ChartedSpace State M]
    (P : TimePartition n) (e : Frame M m) :
    ∃ R : (Fin 1 → Control m) ≃L[ℝ] (Fin n → Control m),
      (∀ u, length (R u) = length u) ∧ ∀ u x y c,
        SingularIn (fun _ : Fin 1 => e) u x y c ↔ SingularIn (fun _ : Fin n => e) (R u) x y c := by
  obtain ⟨R,rep,sg⟩ := P.singular_under_subdivision e
  refine ⟨R,fun u => ?_,sg⟩
  have one : (fun _ : Fin 1 => u 0) = u := funext fun i => congrArg u (Subsingleton.elim 0 i)
  rw [← one] at ⊢
  exact P.length_eq_of_rescaling _ _ (rep (fun _ => u 0))

#print axioms length_eq_of_rescaling
#print axioms length_and_singularity
end MinimizingSard.Five.TimePartition
