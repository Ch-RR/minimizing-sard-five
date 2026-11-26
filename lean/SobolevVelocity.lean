import PrimitivePairing
import ArbitraryFrameEndpoint
import SupportedControlDensity

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace MinimizingSard.Five
open Volterra
abbrev Velocity (E : Type) [NormedAddCommGroup E] := Lp E 2 controlMeasure
variable {U E : Type} [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem mul_mem (A : C(Time,U →L[ℝ] E)) (u : Velocity U) :
    MemLp (fun r => A (clamp r) (u r)) 2 controlMeasure := by
  apply ((Lp.memLp u).norm.const_mul ‖A‖).mono'
  · have ce : Continuous (fun p : (U →L[ℝ] E) × U => p.1 p.2) := continuous_fst.clm_apply continuous_snd
    exact ce.comp_aestronglyMeasurable
      ((A.continuous.comp continuous_projIcc).aestronglyMeasurable.prodMk (Lp.memLp u).1)
  · exact .of_forall fun r => ((A (clamp r)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (A.norm_coe_le_norm _) (norm_nonneg _))

private def mul_vel (A : C(Time,U →L[ℝ] E)) (u : Velocity U) : Velocity E :=
  (mul_mem A u).toLp _
private theorem mul_ae (A : C(Time,U →L[ℝ] E)) (u : Velocity U) :
    (fun r => mul_vel A u r) =ᵐ[controlMeasure] (fun r => A (clamp r) (u r)) := (mul_mem A u).coeFn_toLp

/-- Multiplication of a raw L² ambient velocity by a continuous field of
linear maps is a bounded bilinear operation in the actual Sobolev norm. -/
def multiplyVelocity (U E : Type) [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup E] [NormedSpace ℝ E] :
    C(Time,U →L[ℝ] E) →L[ℝ] Velocity U →L[ℝ] Velocity E := by
  let L : C(Time,U →L[ℝ] E) →ₗ[ℝ] Velocity U →ₗ[ℝ] Velocity E := LinearMap.mk₂ ℝ mul_vel
    (fun a b u => by
      apply Lp.ext
      filter_upwards [mul_ae (a+b) u,Lp.coeFn_add (mul_vel a u) (mul_vel b u),mul_ae a u,mul_ae b u]
        with t h j k l using by rw [h,j]; change _ = mul_vel a u t+mul_vel b u t; rw [k,l]; rfl)
    (fun c a u => by
      apply Lp.ext
      filter_upwards [mul_ae (c • a) u,Lp.coeFn_smul c (mul_vel a u),mul_ae a u] with t h j k
      rw [h,j]; change _ = c • mul_vel a u t; rw [k]; rfl)
    (fun a u v => by
      apply Lp.ext
      filter_upwards [mul_ae a (u+v),Lp.coeFn_add u v,Lp.coeFn_add (mul_vel a u) (mul_vel a v),mul_ae a u,mul_ae a v]
        with t h k j l m
      rw [h,k,j]; change a (clamp t) (u t+v t) = mul_vel a u t+mul_vel a v t
      rw [l,m,map_add])
    (fun c a u => by
      apply Lp.ext
      filter_upwards [mul_ae a (c • u),Lp.coeFn_smul c u,Lp.coeFn_smul c (mul_vel a u),mul_ae a u] with t h k j l
      rw [h,k,j]; change a (clamp t) (c • u t) = c • mul_vel a u t; rw [l,map_smul])
  apply LinearMap.mkContinuous₂ (σ₁₃ := RingHom.id ℝ) (σ₂₃ := RingHom.id ℝ)
    (E := C(Time,U →L[ℝ] E)) (F := Velocity U) (G := Velocity E) L 1
  intro A u
  rw [one_mul]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [mul_ae A u] with r h
  change ‖mul_vel A u r‖ ≤ _
  rw [h]
  exact ((A (clamp r)).le_opNorm _).trans (mul_le_mul_of_nonneg_right (A.norm_coe_le_norm _) (norm_nonneg _))

theorem multiplyVelocity_ae (A : C(Time,U →L[ℝ] E)) (u : Velocity U) :
    (fun r => multiplyVelocity U E A u r) =ᵐ[controlMeasure] (fun r => A (clamp r) (u r)) := mul_ae A u

theorem multiplyVelocity_smooth {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {k : ℕ}
    {A : P → C(Time,U →L[ℝ] E)} {v : P → Velocity U} {p : P}
    (hA : ContDiffAt ℝ k A p) (hv : ContDiffAt ℝ k v p) :
    ContDiffAt ℝ k (fun z => multiplyVelocity U E (A z) (v z)) p := by
  letI : NormedAddCommGroup (Velocity U →L[ℝ] Velocity E) := inferInstance
  have h := @ContinuousLinearMap.contDiff ℝ _ C(Time,U →L[ℝ] E) _ _ (Velocity U →L[ℝ] Velocity E) _ _ k (multiplyVelocity U E)
  exact (h.contDiffAt.comp p hA).clm_apply hv

theorem TimePrimitive.velocity_unique [FiniteDimensional ℝ E] {w : C(Time,E)} {a : E} {v b : Velocity E}
    (h : TimePrimitive w a (fun r => v r)) (k : TimePrimitive w a (fun r => b r)) : v = b := by
  apply Lp.ext
  have eq : (fun t => v t) =ᵐ[volume.restrict (Ioo (0:ℝ) 1)] (fun t => b t) := by
    filter_upwards [h.ae_derivative,k.ae_derivative] with t d f using d.unique f
  simpa only [Measure.restrict_congr_set Ioo_ae_eq_Icc] using eq

theorem TimePrimitive.replace_ae {w : C(Time,E)} {a : E} {v b : ℝ → E}
    (h : TimePrimitive w a v) (eq : v =ᵐ[controlMeasure] b) : TimePrimitive w a b := by
  have same : v =ᵐ[volume.restrict (uIoc (0:ℝ) 1)] b := by
    rwa [uIoc_of_le zero_le_one,Measure.restrict_congr_set Ioc_ae_eq_Icc]
  refine ⟨(intervalIntegrable_congr_ae same).mp h.1,fun t => ?_⟩
  rw [h.2 t]
  congr 1
  apply intervalIntegral.integral_congr_ae_restrict
  apply ae_mono (Measure.restrict_mono _ (le_refl volume)) same
  rw [uIoc_of_le t.2.1,uIoc_of_le zero_le_one]
  exact Ioc_subset_Ioc_right t.2.2

#print axioms multiplyVelocity_ae
#print axioms TimePrimitive.velocity_unique
#print axioms TimePrimitive.replace_ae
end MinimizingSard.Five
