import CausalTail
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The indefinite integral with a continuous time-dependent coefficient
is a bounded bilinear map on the actual L² controls and the sup-norm
coefficient paths. -/
noncomputable section
open MeasureTheory Set Filter ContinuousMap
open scoped Topology
namespace MinimizingSard.Volterra
abbrev Time := Icc (0 : ℝ) 1
def clamp := projIcc (0 : ℝ) 1 zero_le_one
variable {U E : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance : IsProbabilityMeasure Causal.timeMeasure := ⟨by
  simp [Causal.timeMeasure,Real.volume_Ioo]⟩

omit [NormedSpace ℝ U] in
private theorem l1 (u : Causal.Signals U) : Integrable (fun s => u s) Causal.timeMeasure :=
  memLp_one_iff_integrable.mp ((Lp.memLp u).mono_exponent (by norm_num : (1 : ENNReal) ≤ 2))

omit [NormedSpace ℝ U] in
private theorem mass (u : Causal.Signals U) : (∫ s, ‖u s‖ ∂Causal.timeMeasure) ≤ ‖u‖ := by
  rw [integral_norm_eq_lintegral_enorm (Lp.memLp u).1, ← eLpNorm_one_eq_lintegral_enorm, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp u).2.ne (eLpNorm_le_eLpNorm_of_exponent_le
    (by norm_num : (1 : ENNReal) ≤ 2) (Lp.memLp u).1)

private theorem integrable (A : C(Time,U →L[ℝ] E)) (u : Causal.Signals U) :
    Integrable (fun s => A (clamp s) (u s)) Causal.timeMeasure := by
  apply ((l1 u).norm.const_mul ‖A‖).mono'
  · have ce : Continuous (fun p : (U →L[ℝ] E) × U => p.1 p.2) := continuous_fst.clm_apply continuous_snd
    exact (ce.comp_aestronglyMeasurable
      (((A.continuous.comp continuous_projIcc).aestronglyMeasurable).prodMk (Lp.memLp u).1))
  · exact .of_forall fun s => ((A (clamp s)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (A.norm_coe_le_norm _) (norm_nonneg _))

theorem intervalIntegrable (A : C(Time,U →L[ℝ] E)) (u : Causal.Signals U) :
    IntervalIntegrable (fun s => A (clamp s) (u s)) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  change Integrable _ (volume.restrict (Ioc (0 : ℝ) 1))
  rw [← restrict_Ioo_eq_restrict_Ioc]
  exact integrable A u

def primitive (A : C(Time,U →L[ℝ] E)) (u : Causal.Signals U) : C(Time,E) :=
  ⟨fun t => ∫ s in (0 : ℝ)..(t : ℝ), A (clamp s) (u s) ∂Causal.timeMeasure,
    ((integrable A u).continuous_primitive 0).comp continuous_subtype_val⟩

theorem primitive_estimate (A : C(Time,U →L[ℝ] E)) (u : Causal.Signals U) (t : Time)
    (M : ℝ) (hM : 0 ≤ M) (localBound : ∀ s : Time, s ≤ t → ‖A s‖ ≤ M) :
    ‖primitive A u t‖ ≤ M * ‖u‖ := by
  let μ := Causal.timeMeasure
  let S := Ioc (0 : ℝ) (t : ℝ)
  change ‖∫ s in (0 : ℝ)..(t : ℝ), A (clamp s) (u s) ∂μ‖ ≤ _
  rw [intervalIntegral.integral_of_le t.2.1]
  calc
    _ ≤ ∫ s in S, ‖A (clamp s) (u s)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ s in S, M * ‖u s‖ ∂μ := by
      apply integral_mono_ae (integrable A u).norm.integrableOn ((l1 u).norm.const_mul M).integrableOn
      filter_upwards [ae_restrict_mem (μ := μ) (measurableSet_Ioc (a := 0) (b := (t : ℝ)))]
        with s hs
      have hi : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le,hs.2.trans t.2.2⟩
      have eq : clamp s = ⟨s,hi⟩ := projIcc_of_mem _ hi
      exact ((A (clamp s)).le_opNorm _).trans (mul_le_mul_of_nonneg_right
        (localBound _ (eq ▸ hs.2 : clamp s ≤ t)) (norm_nonneg _))
    _ = M * ∫ s in S, ‖u s‖ ∂μ := integral_const_mul _ _
    _ ≤ M * ‖u‖ := mul_le_mul_of_nonneg_left
      ((integral_mono_measure Measure.restrict_le_self (.of_forall fun s => norm_nonneg (u s))
        (l1 u).norm).trans (mass u)) hM

def operator (U E : Type*) [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup E] [NormedSpace ℝ E] :
    C(Time,U →L[ℝ] E) →L[ℝ] Causal.Signals U →L[ℝ] C(Time,E) := by
  let m : C(Time,U →L[ℝ] E) →ₗ[ℝ] Causal.Signals U →ₗ[ℝ] C(Time,E) :=
    LinearMap.mk₂ ℝ (primitive (U := U) (E := E))
    (fun A B u => by
      ext t
      apply intervalIntegral.integral_add (integrable A u).intervalIntegrable
        (integrable B u).intervalIntegrable)
    (fun c A u => by ext t; apply intervalIntegral.integral_smul)
    (fun A u v => by
      ext t
      change (∫ s in (0 : ℝ)..(t : ℝ), A (clamp s) ((u+v) s) ∂Causal.timeMeasure) =
        (∫ s in (0 : ℝ)..(t : ℝ), A (clamp s) (u s) ∂Causal.timeMeasure) +
        ∫ s in (0 : ℝ)..(t : ℝ), A (clamp s) (v s) ∂Causal.timeMeasure
      rw [← intervalIntegral.integral_add (integrable A u).intervalIntegrable
        (integrable A v).intervalIntegrable]
      apply intervalIntegral.integral_congr_ae
      filter_upwards [Lp.coeFn_add u v] with s hs using fun _ => by rw [hs]; exact map_add _ _ _)
    (fun c A u => by
      ext t
      change (∫ s in (0 : ℝ)..(t : ℝ), A (clamp s) ((c • u) s) ∂Causal.timeMeasure) =
        c • ∫ s in (0 : ℝ)..(t : ℝ), A (clamp s) (u s) ∂Causal.timeMeasure
      rw [← intervalIntegral.integral_smul]
      apply intervalIntegral.integral_congr_ae
      filter_upwards [Lp.coeFn_smul c u] with s hs using fun _ => by rw [hs]; exact map_smul _ _ _)
  have bound (A : C(Time,U →L[ℝ] E)) (u : Causal.Signals U) :
      ‖m A u‖ ≤ 1 * ‖A‖ * ‖u‖ := by
    rw [one_mul]
    change ‖primitive A u‖ ≤ ‖A‖ * ‖u‖
    exact (ContinuousMap.norm_le (primitive A u) (mul_nonneg (norm_nonneg A) (norm_nonneg u))).mpr
      (fun t => primitive_estimate (U := U) (E := E) A u t ‖A‖ (norm_nonneg A) fun s _ => A.norm_coe_le_norm s)
  exact LinearMap.mkContinuous₂ (σ₁₃ := RingHom.id ℝ) (σ₂₃ := RingHom.id ℝ)
    (E := C(Time,U →L[ℝ] E)) (F := Causal.Signals U) (G := C(Time,E)) m 1 bound

theorem operator_eq_interval (A : C(Time,U →L[ℝ] E)) (u : Causal.Signals U) (t : Time) :
    operator U E A u t = ∫ s in (0 : ℝ)..(t : ℝ), A (clamp s) (u s) := by
  change (∫ s in (0 : ℝ)..(t : ℝ), A (clamp s) (u s) ∂Causal.timeMeasure) = _
  rw [intervalIntegral.integral_of_le t.2.1, intervalIntegral.integral_of_le t.2.1]
  simp only [Causal.timeMeasure,restrict_Ioo_eq_restrict_Ioc,Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr (Ioc_subset_Ioc_right t.2.2)]

#print axioms primitive_estimate
#print axioms operator_eq_interval
end MinimizingSard.Volterra
