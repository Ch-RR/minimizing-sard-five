import ControlledImplicit
import MeasuredVolterra

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace MinimizingSard.Five
open Volterra
variable {U E : Type} [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [CompleteSpace U] in
theorem signal_norm_integrable (u : Causal.Signals U) : IntervalIntegrable (fun r => ‖u r‖) volume 0 1 := by
  simpa using (Volterra.intervalIntegrable (ContinuousMap.const Time (ContinuousLinearMap.id ℝ U)) u).norm

omit [CompleteSpace U] in
/-- The actual path derivative for a base L² control has an integrable
majorant of size ‖D‖ times the instantaneous control norm. -/
theorem controlled_linear_inverse (u : Causal.Signals U) (D : C(Time,E →L[ℝ] U →L[ℝ] E)) :
    IsUnit (1 - ((ContinuousLinearMap.apply ℝ C(Time,E) u).comp (Volterra.operator U E)).comp (PathCalculus.multiplier Time E (U →L[ℝ] E) D)) := by
  let A := ((ContinuousLinearMap.apply ℝ C(Time,E) u).comp (Volterra.operator U E)).comp (PathCalculus.multiplier Time E (U →L[ℝ] E) D)
  have cd : Continuous (fun t : Time => ‖D t‖) := (@continuous_norm (E →L[ℝ] U →L[ℝ] E) _).comp D.continuous
  obtain ⟨C,cap⟩ := (isCompact_univ (X := Time)).bddAbove_image (f := fun t : Time => ‖D t‖) cd.continuousOn
  have point (t : Time) : ‖D t‖ ≤ C := cap (mem_image_of_mem _ (mem_univ t))
  have cp : 0 ≤ C := (norm_nonneg (D (clamp 0))).trans (point (clamp 0))
  let ν (r : ℝ) := C*‖u r‖
  have iv : IntervalIntegrable ν volume 0 1 := (signal_norm_integrable u).const_mul C
  apply measured_volterra_isUnit A ν iv (fun r => mul_nonneg cp (norm_nonneg _))
  intro h t
  let B := PathCalculus.multiplier Time E (U →L[ℝ] E) D h
  change ‖Volterra.operator U E B u t‖ ≤ _
  rw [operator_eq_interval]
  have i₁ := (Volterra.intervalIntegrable B u).norm
  have i₂ := iv.mul_continuousOn ((h.continuous.comp (show Continuous clamp from continuous_projIcc)).norm.continuousOn)
  have subint {f : ℝ → ℝ} (i : IntervalIntegrable f volume 0 1) : IntervalIntegrable f volume 0 (t:ℝ) :=
    i.mono_set (by rw [uIcc_of_le t.property.1,uIcc_of_le zero_le_one]; exact Icc_subset_Icc le_rfl t.property.2)
  apply (intervalIntegral.norm_integral_le_integral_norm t.property.1).trans
    (intervalIntegral.integral_mono_on t.property.1 (subint i₁) (subint i₂) ?_)
  intro r _
  change ‖D (clamp r) (h (clamp r)) (u r)‖ ≤ (C*‖u r‖)*‖h (clamp r)‖
  calc _ ≤ ‖D (clamp r) (h (clamp r))‖*‖u r‖ := (D (clamp r) (h (clamp r))).le_opNorm _
       _ ≤ (C*‖h (clamp r)‖)*‖u r‖ := by
            gcongr
            exact ((D (clamp r)).le_opNorm _).trans
              (mul_le_mul_of_nonneg_right (point _) (norm_nonneg _))
       _ = _ := by ring

/-- The entire path depends smoothly on the initial state and all L²
control variations. The vector fields need only be defined smoothly on
the open region containing the reference trajectory. -/
theorem controlled_path_family {n : ℕ} (hn : 1 ≤ n) (O : Set E) (op : IsOpen O)
    (X : E → U →L[ℝ] E) (cx : ContDiffOn ℝ n X O) (u : Causal.Signals U)
    (w : C(Time,E)) (inside : ∀ t, w t ∈ O)
    (eq : ∀ t : Time, w t = w (clamp 0) + ∫ r in (0:ℝ)..(t:ℝ), X (w (clamp r)) (u r)) :
    ∃ S : E × Causal.Signals U → C(Time,E), S (w (clamp 0),u) = w ∧ ContDiffAt ℝ n S (w (clamp 0),u) ∧
      ∀ᶠ p in 𝓝 (w (clamp 0),u), (∀ t, S p t ∈ O) ∧
        ∀ t : Time, S p t = p.1 + ∫ r in (0:ℝ)..(t:ℝ), X (S p (clamp r)) (p.2 r) := by
  obtain ⟨Y,V,cy,ov,contains,sub,agree⟩ := compact_smooth_extension O (range w) op
    (isCompact_range w.continuous) (range_nonempty _) (range_subset_iff.mpr inside) X cx
  have hn' : 1 ≤ (n : WithTop ℕ∞) := by exact_mod_cast hn
  let N := pathField Y cy.continuous
  let B := (Volterra.operator U E) ∘ N
  have cB : ContDiff ℝ n B := by
    have co := @ContinuousLinearMap.contDiff ℝ _ C(Time,U →L[ℝ] E) _ _ (Causal.Signals U →L[ℝ] C(Time,E)) _ _ n (Volterra.operator U E)
    exact co.comp (pathField_smooth Y cy)
  have c₁ : ContDiff ℝ 1 Y := cy.of_le hn'
  have cd : Continuous (fderiv ℝ Y) := (c₁.fderiv_right (m := 0) (by decide)).continuous
  let D := pathField (fderiv ℝ Y) cd w
  let M₁ := PathCalculus.multiplier Time E (U →L[ℝ] E) D
  have dN : HasFDerivAt N M₁ w := PathCalculus.hasFDerivAt_subst (liftField Y cy.continuous)
    (liftField (fderiv ℝ Y) cd) (fun _ x => (cy.differentiable hn' x).hasFDerivAt) w
  let V₀ : C(Time,U →L[ℝ] E) →L[ℝ] C(Time,E) := (ContinuousLinearMap.apply ℝ C(Time,E) u).comp (Volterra.operator U E)
  let K := V₀.comp M₁
  have dNK := V₀.hasFDerivAt.comp w dN
  have dH : HasFDerivAt (fun z => z-B z u) (1-K) w :=
    (hasFDerivAt_id w).sub dNK
  obtain ⟨g,ge⟩ := controlled_linear_inverse u D
  let J := ContinuousLinearEquiv.unitsEquiv ℝ (C(Time,E)) g
  have dJ : HasFDerivAt (fun z => z-B z u) J.toContinuousLinearMap w := by
    change HasFDerivAt _ (g : C(Time,E) →L[ℝ] C(Time,E)) w
    rwa [ge]
  obtain ⟨S,s₀,cs,near⟩ := ImplicitControl.solution_at B hn' w u cB.contDiffAt J dJ
  let I : E →L[ℝ] C(Time,E) := ContinuousLinearMap.const ℝ Time
  let T (p : E × Causal.Signals U) := (I p.1,p.2)
  have cT : ContDiff ℝ n T := (I.contDiff.comp contDiff_fst).prodMk contDiff_snd
  let q := w (clamp 0)
  have base : I q = w-B w u := by
    ext t : 1
    change q = w t-Volterra.operator U E (N w) u t
    rw [operator_eq_interval]
    have equal (r : ℝ) : (N w (clamp r)) = X (w (clamp r)) := agree (contains (mem_range_self _))
    simp_rw [equal]
    rw [eq t]; abel
  have b₀ : T (q,u) = (w-B w u,u) := Prod.ext base rfl
  have reg : ContDiffAt ℝ n (S ∘ T) (q,u) := (b₀.symm ▸ cs).comp _ cT.contDiffAt
  have start : S (T (q,u)) = w := (congrArg S b₀).trans s₀
  have stay : {z : C(Time,E) | MapsTo z univ V} ∈ 𝓝 (S (T (q,u))) := by
    rw [start]
    exact (ContinuousMap.isOpen_setOf_mapsTo isCompact_univ ov).mem_nhds (fun t _ => contains (mem_range_self t))
  have pull : Tendsto T (𝓝 (q,u)) (𝓝 (w-B w u,u)) := b₀ ▸ cT.continuous.continuousAt.tendsto
  refine ⟨S ∘ T,start,reg,?_⟩
  filter_upwards [pull near,reg.continuousAt stay] with p hp good
  refine ⟨fun t => sub (good (mem_univ t)),fun t => ?_⟩
  have h := congrArg (fun z : C(Time,E) => z t) hp
  change S (T p) t = p.1 + Volterra.operator U E (N (S (T p))) p.2 t at h
  rw [operator_eq_interval] at h
  have equal (r : ℝ) : N (S (T p)) (clamp r) = X (S (T p) (clamp r)) := agree (good (mem_univ _))
  simpa only [Function.comp_apply,equal] using h

#print axioms controlled_linear_inverse
#print axioms controlled_path_family
end MinimizingSard.Five
