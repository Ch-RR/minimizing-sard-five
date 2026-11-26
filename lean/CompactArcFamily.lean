import OrbitDependence
import ClockForward

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace MinimizingSard.Five
open Volterra
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A finite-time ordinary orbit has a differentiable family in its initial
phase. The family takes values in the uniform space of entire paths. -/
theorem compact_arc_family (U : Set E) (ou : IsOpen U) (X : E → E) (cx : ContDiffOn ℝ 1 X U)
    (L : ℝ) (pos : 0 < L) (f : ℝ → E) (cf : Continuous f)
    (inside : ∀ s ∈ Icc 0 L, f s ∈ U)
    (df : ∀ s ∈ Icc 0 L, HasDerivWithinAt f (X (f s)) (Icc 0 L) s) :
    ∃ S : E → C(Time,E), DifferentiableAt ℝ S (f 0) ∧
      (∀ t : Time, S (f 0) t = f (L*(t:ℝ))) ∧
      ∀ᶠ a in 𝓝 (f 0), S a (clamp 0) = a ∧ (∀ t, S a t ∈ U) ∧
        ∀ s ∈ Icc 0 L, HasDerivWithinAt (fun r => S a (clamp (r/L)))
          (X (S a (clamp (s/L)))) (Icc 0 L) s := by
  let τ (t : ℝ) := L*t
  have maps : MapsTo τ (Icc 0 1) (Icc 0 L) := fun t ht =>
    ⟨mul_nonneg pos.le ht.1,mul_le_of_le_one_right pos.le ht.2⟩
  let w : C(Time,E) := ⟨fun t => f (L*(t:ℝ)),by fun_prop⟩
  have wU t : w t ∈ U := inside _ (maps t.property)
  let Y := fun z => L • X z
  have cy : ContDiffOn ℝ 1 Y U := contDiffOn_const.smul cx
  let b : C(Time,E) := ⟨fun t => Y (w t),cy.continuousOn.comp_continuous w.continuous wU⟩
  have atT (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : w (clamp t) = f (L*t) := by
    change f (L*((clamp t):ℝ)) = _
    rw [show ((clamp t):ℝ) = t from congrArg Subtype.val (projIcc_of_mem zero_le_one ht)]
  have deriv (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      HasDerivWithinAt (fun r => w (clamp r)) (b (clamp t)) (Icc 0 1) t := by
    have dτ : HasDerivAt τ L t := by simpa only [mul_one] using (hasDerivAt_id t).const_mul L
    have d := (df _ (maps ht)).scomp t dτ.hasDerivWithinAt maps
    change HasDerivWithinAt _ (L • X (w (clamp t))) _ _
    rw [atT t ht]
    exact d.congr_of_mem atT ht
  have prim := time_derivative_primitive w b deriv
  obtain ⟨S,root,sm,ne⟩ := orbit_path_dependence U ou Y cy w wU prim
  have initial : w (clamp 0) = f 0 := (atT 0 (left_mem_Icc.mpr zero_le_one)).trans (by rw [mul_zero])
  rw [initial] at root sm ne
  refine ⟨S,sm.differentiableAt (by decide),by intro t; rw [root]; rfl,?_⟩
  filter_upwards [ne] with a ha
  let B : C(Time,E) := ⟨fun t => Y (S a t),cy.continuousOn.comp_continuous (S a).continuous ha.1⟩
  have eq0 : S a (clamp 0) = a := by simpa [clamp] using ha.2 (clamp 0)
  refine ⟨eq0,ha.1,?_⟩
  intro s hs
  have divs : MapsTo (fun r : ℝ => r/L) (Icc 0 L) (Icc 0 1) :=
    fun r hr => ⟨div_nonneg hr.1 pos.le,(div_le_one pos).mpr hr.2⟩
  have scaled := (time_primitive_derivative (S a) B a ha.2 _ (divs hs)).scomp s
    ((hasDerivAt_id s).div_const L).hasDerivWithinAt divs
  simpa only [B,Y,ContinuousMap.coe_mk,smul_smul,one_div,inv_mul_cancel₀ pos.ne',one_smul] using scaled

def reparamPath (θ : C(Time,Time)) : C(Time,E) →L[ℝ] C(Time,E) :=
  LinearMap.mkContinuous
    ({ toFun := fun z : C(Time,E) => z.comp θ
       map_add' := fun _ _ => rfl
       map_smul' := fun _ _ => rfl } : C(Time,E) →ₗ[ℝ] C(Time,E)) 1 (fun z => by
      rw [one_mul]
      exact (ContinuousMap.norm_le _ (norm_nonneg z)).mpr fun t => z.norm_coe_le_norm (θ t))

#print axioms compact_arc_family
end MinimizingSard.Five
