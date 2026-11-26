import EndpointRankFloor
import Mathlib.MeasureTheory.Function.Jacobian

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five

/-- A single finite-dimensional endpoint parametrization has a null image at
all its differentiable critical points, on arbitrary domains of definition. -/
theorem critical_values_null (P : State → State) :
    volume (P '' {z | DifferentiableAt ℝ P z ∧ ¬ Function.Surjective (fderiv ℝ P z)}) = 0 := by
  apply MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
    (f' := fderiv ℝ P) (fun _ hz => hz.1.hasFDerivAt.hasFDerivWithinAt)
  intro ξ hξ
  apply LinearMap.det_eq_zero_iff_ker_ne_bot.mpr
  intro ker
  exact hξ.2 ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (fderiv ℝ P ξ).toLinearMap) rfl).mp (LinearMap.ker_eq_bot.mp ker))

/-- Keeping the reference clock in a differentiable family of controls
transfers endpoint singularity to its finite-dimensional parameters. -/
theorem critical_of_control_factor {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (P : State → State) (ξ : State) (V : State → U) (G : U → State)
    (dv : DifferentiableAt ℝ V ξ) (dg : DifferentiableAt ℝ G (V ξ))
    (factor : P =ᶠ[𝓝 ξ] G ∘ V) (singular : ¬ Function.Surjective (fderiv ℝ G (V ξ))) :
    P ξ ∈ P '' {z | DifferentiableAt ℝ P z ∧ ¬ Function.Surjective (fderiv ℝ P z)} := by
  refine ⟨ξ,⟨(dg.comp ξ dv).congr_of_eventuallyEq factor,?_⟩,rfl⟩
  rw [factor.fderiv_eq,fderiv_comp ξ dg dv]
  intro onto
  apply singular
  intro z
  obtain ⟨h,hh⟩ := onto z
  exact ⟨fderiv ℝ V ξ h,hh⟩

/-- Suffices to realize the supported controls in a fixed countable family
of finite-dimensional endpoint maps. The family is chosen before the paths. -/
theorem rank_two_null_of_normal_parameters {M : Type*} [TopologicalSpace M] [ChartedSpace State M]
    [IsManifold 𝓘(ℝ,State) ∞ M] (Γ : Geometry M 2) (x : M)
    (c : OpenPartialHomeomorph M State) (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M)
    {I : Type*} [Countable I] (P : I → State → State)
    (param : ∀ {n : ℕ} (e : Fin (n+1) → Frame M 2) (w : Fin (n+1) → Control 2) (y : M),
      y ∈ c.source → (∀ j, e j ∈ Γ.frames) → Joins e w x y →
      (∀ (k : ℕ) (a : Fin (k+1) → Frame M 2) (b : Fin (k+1) → Control 2),
        (∀ j, a j ∈ Γ.frames) → Joins a b x y → length w ≤ length b) →
      ∀ G : (Fin (n+1) → Control 2) → State, G w = c y →
      (∀ᶠ b in 𝓝 w, G b ∈ c.target ∧ ∀ z, Joins e b x z ↔ z = c.symm (G b)) →
      ¬ Function.Surjective (fderiv ℝ G w) → HasCostMultiplier length (fderiv ℝ G w) w →
      ∃ (i : I) (ξ : State) (V : State → (Fin (n+1) → Control 2)),
        V ξ = w ∧ DifferentiableAt ℝ V ξ ∧ P i =ᶠ[𝓝 ξ] G ∘ V) :
    volume (c '' (c.source ∩ singularMinEndpoints Γ x)) = 0 := by
  let C (i : I) := P i '' {z | DifferentiableAt ℝ (P i) z ∧ ¬ Function.Surjective (fderiv ℝ (P i) z)}
  have exc : ∀ᵐ q : State, q ∉ ⋃ i, C i := ae_iff.mpr (by
    simpa only [not_not] using measure_iUnion_null (fun i => critical_values_null (P i)))
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [exc,ae_singular_minimizer_has_multiplier Γ x c hc] with q outside multiplier
  rintro ⟨y,⟨hy,n,e,w,he,path,sing,minimal⟩,rfl⟩
  obtain ⟨G,gw,sm,graph,defect⟩ := path_endpoint_and_singularity e w x y path c hc hy 1 (by decide)
  have bad := defect.mp sing
  have support := multiplier (c.map_source hy) e w G
  rw [c.left_inv hy] at support
  obtain ⟨i,ξ,V,vw,dv,factor⟩ := param e w y hy he path minimal G gw graph bad (support he path minimal graph bad)
  apply outside
  apply mem_iUnion.mpr
  obtain ⟨z,hz,eq⟩ := critical_of_control_factor (P i) ξ V G dv
    (vw.symm ▸ sm.differentiableAt (by decide)) factor (vw.symm ▸ bad)
  exact ⟨i,z,hz,eq.trans ((factor.self_of_nhds).trans (by simp [vw,gw]))⟩

#print axioms critical_values_null
#print axioms critical_of_control_factor
#print axioms rank_two_null_of_normal_parameters
end MinimizingSard.Five
