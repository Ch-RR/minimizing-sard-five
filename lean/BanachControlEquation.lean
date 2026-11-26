import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! The local solution of z = A(z)u for a Banach-space control and a
Banach-space trajectory. Centering the coefficient makes the derivative
of the inverse-function problem exactly the identity at zero. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace MinimizingSard.ImplicitControl
variable {U Z : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]

theorem local_solution (A : Z → U →L[ℝ] Z) {n : WithTop ℕ∞}
    (hn : 1 ≤ n) (ha : ContDiffAt ℝ n A 0) :
    ∃ S : U → Z, S 0 = 0 ∧ ContDiffAt ℝ n S 0 ∧
      (∀ᶠ u in 𝓝 0, S u = A (S u) u) ∧
      ∃ r > 0, ∀ᶠ u in 𝓝 0, ∀ z, ‖z‖ < r → z = A z u → z = S u := by
  let H (p : U × Z) := (p.1, p.2 - (A p.2 - A 0) p.1)
  have hzero : H 0 = 0 := by simp [H]
  have a0 : ContDiffAt ℝ n (fun p : U × Z => A p.2 - A 0) 0 :=
    (ha.comp 0 contDiffAt_snd).sub contDiffAt_const
  have hc : ContDiffAt ℝ n H 0 := contDiffAt_fst.prodMk
    (contDiffAt_snd.sub (a0.clm_apply contDiffAt_fst))
  let e := ContinuousLinearEquiv.refl ℝ (U × Z)
  have d : HasFDerivAt H (e : (U × Z) →L[ℝ] (U × Z)) 0 := by
    have a := (a0.differentiableAt hn).hasFDerivAt.clm_apply (hasFDerivAt_fst (𝕜 := ℝ) (p := (0 : U × Z)))
    have b := (hasFDerivAt_fst (𝕜 := ℝ) (p := (0 : U × Z))).prodMk
      ((hasFDerivAt_snd (𝕜 := ℝ) (p := (0 : U × Z))).sub a)
    convert b using 1
    ext p <;> simp [e]
  let T := hc.toOpenPartialHomeomorph H d hn
  have src : (0 : U × Z) ∈ T.source := hc.mem_toOpenPartialHomeomorph_source d hn
  have tgt : H 0 ∈ T.target := T.map_source src
  let g (u : U) := (u,A 0 u)
  have cg : ContDiff ℝ n g := contDiff_id.prodMk (A 0).contDiff
  have inv : ContDiffAt ℝ n T.symm (H 0) := hc.to_localInverse d hn
  have g0 : g 0 = H 0 := by simp [g,hzero]
  let S (u : U) := (T.symm (g u)).2
  have left : T.symm (H 0) = 0 := T.left_inv src
  have smooth : ContDiffAt ℝ n S 0 := contDiffAt_snd.comp 0
    ((g0.symm ▸ inv : ContDiffAt ℝ n T.symm (g 0)).comp 0 cg.contDiffAt)
  refine ⟨S,by simp [S,g0,left],smooth,?_,?_⟩
  · have near := cg.continuous.continuousAt (x := 0) (T.open_target.mem_nhds (g0.symm ▸ tgt))
    filter_upwards [near] with u hu
    have hit : H (T.symm (g u)) = g u := T.right_inv hu
    have xeq := congrArg Prod.fst hit
    change (T.symm (g u)).1 = u at xeq
    have y := congrArg Prod.snd hit
    change S u - (A (S u) - A 0) ((T.symm (g u)).1) = A 0 u at y
    rw [xeq,ContinuousLinearMap.sub_apply] at y
    exact sub_eq_zero.mp (by linear_combination (norm := abel) y)
  · obtain ⟨r,hr,inside⟩ := Metric.mem_nhds_iff.mp (T.open_source.mem_nhds src)
    refine ⟨r,hr,?_⟩
    filter_upwards [Metric.ball_mem_nhds (0 : U) hr] with u hu
    intro z hz eq
    have mem : (u,z) ∈ T.source := inside (by
      simpa [Metric.mem_ball, Prod.dist_eq] using And.intro
        (show ‖u‖ < r by simpa [Metric.mem_ball] using hu) hz)
    have hit : H (u,z) = g u := by simp [H,g,ContinuousLinearMap.sub_apply,← eq]
    exact (congrArg Prod.snd ((congrArg T.symm hit).symm.trans (T.left_inv mem))).symm

#print axioms local_solution
end MinimizingSard.ImplicitControl
