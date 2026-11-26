import NormalSegmentLift
import ArcLengthClock
import PathSuperposition

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace MinimizingSard.Five
open Volterra

theorem speed_memLp {m : ℕ} (u : Control m) : MemLp (fun t => Real.sqrt (speedSq (u t))) 2 controlMeasure := by
  apply MemLp.ae_eq (hf_Lp := (Lp.memLp (euclideanControl m u)).norm)
  let T := (EuclideanSpace.equiv (Fin m) ℝ).symm.toContinuousLinearMap
  filter_upwards [T.coeFn_compLp u] with t ht
  change ‖T.compLp u t‖ = Real.sqrt (speedSq (u t))
  rw [ht,EuclideanSpace.norm_eq]
  simp only [Real.norm_eq_abs,sq_abs,speedSq]
  rfl

/-- Multiplication by the fixed original speed maps continuous coefficient
paths linearly and continuously into the full square-integrable control space. -/
theorem fixed_clock_controls {m : ℕ} (ν : ℝ → ℝ) (mem : MemLp ν 2 controlMeasure) :
    ∃ W : C(Time,Fiber m) →L[ℝ] Control m, ∀ b, ∀ᵐ t ∂controlMeasure, W b t = ν t • b (clamp t) := by
  let f (b : C(Time,Fiber m)) (t : ℝ) := ν t • b (clamp t)
  have bound (b : C(Time,Fiber m)) (t : ℝ) : ‖f b t‖ ≤ ‖b‖*‖ν t‖ := by
    change ‖ν t • b (clamp t)‖ ≤ _
    rw [norm_smul,mul_comm ‖b‖]
    exact mul_le_mul_of_nonneg_left (b.norm_coe_le_norm _) (norm_nonneg _)
  have mb (b : C(Time,Fiber m)) : MemLp (f b) 2 controlMeasure := mem.of_le_mul
    (mem.1.smul (b.continuous.comp continuous_projIcc).aestronglyMeasurable) (.of_forall (bound b))
  let W (b : C(Time,Fiber m)) := (mb b).toLp (f b)
  have rep (b : C(Time,Fiber m)) : ∀ᵐ t ∂controlMeasure, W b t = ν t • b (clamp t) := (mb b).coeFn_toLp
  let A : C(Time,Fiber m) →ₗ[ℝ] Control m := {
    toFun := W
    map_add' := fun b c => by
      apply Lp.ext
      filter_upwards [rep (b+c),rep b,rep c,Lp.coeFn_add (W b) (W c)] with t sum hb hc plus
      change (W (b+c)) t = (W b+W c) t
      change (W b+W c) t = W b t+W c t at plus
      rw [sum,plus,hb,hc,ContinuousMap.add_apply,smul_add]
    map_smul' := fun a b => by
      apply Lp.ext
      filter_upwards [rep (a • b),rep b,Lp.coeFn_smul a (W b)] with t sc hb scale
      change (W (a • b)) t = (a • W b) t
      change (a • W b) t = a • W b t at scale
      rw [sc,scale,hb,ContinuousMap.smul_apply,smul_comm]
  }
  let speed := mem.toLp ν
  have bounded (b : C(Time,Fiber m)) : ‖A b‖ ≤ ‖speed‖*‖b‖ := by
    rw [mul_comm]
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [rep b,mem.coeFn_toLp] with t hb ht
    change ‖W b t‖ ≤ ‖b‖*‖speed t‖
    rw [hb,show speed t = ν t from ht]
    exact bound b t
  exact ⟨A.mkContinuous ‖speed‖ bounded,rep⟩

/-- A differentiable family of continuous coefficient paths supplies genuine
original-clock controls in L² and recovers the given reference input exactly. -/
theorem differentiable_clock_controls {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} (u : Control m) (B : E → C(Time,Fiber m)) (ξ : E) (d : DifferentiableAt ℝ B ξ)
    (ref : ∀ᵐ t ∂controlMeasure, u t = Real.sqrt (speedSq (u t)) • B ξ (clamp t)) :
    ∃ V : E → Control m, V ξ = u ∧ DifferentiableAt ℝ V ξ ∧ ∀ a, ∀ᵐ t ∂controlMeasure,
      V a t = Real.sqrt (speedSq (u t)) • B a (clamp t) := by
  obtain ⟨W,rep⟩ := fixed_clock_controls (m := m) _ (speed_memLp u)
  refine ⟨W ∘ B,?_,W.differentiableAt.comp ξ d,fun a => rep (B a)⟩
  apply Lp.ext
  filter_upwards [rep (B ξ),ref] with t h k using h.trans k.symm

#print axioms fixed_clock_controls
#print axioms differentiable_clock_controls
end MinimizingSard.Five
