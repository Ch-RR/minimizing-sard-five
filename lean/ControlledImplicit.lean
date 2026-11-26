import BanachControlEquation

noncomputable section
open Set Filter
open scoped Topology
namespace MinimizingSard.ImplicitControl
variable {U Z : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]

/-- Dependence on both the forcing term and the control, along a prescribed
nonzero solution, when the path derivative is invertible. -/
theorem solution_at (A : Z → U →L[ℝ] Z) {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (w : Z) (u : U) (ha : ContDiffAt ℝ n A w) (J : Z ≃L[ℝ] Z)
    (dJ : HasFDerivAt (fun z => z-A z u) J.toContinuousLinearMap w) :
    ∃ S : Z × U → Z, S (w-A w u,u) = w ∧ ContDiffAt ℝ n S (w-A w u,u) ∧
      ∀ᶠ p in 𝓝 (w-A w u,u), S p = p.1 + A (S p) p.2 := by
  let H (p : U × Z) := (p.1,(p.2-A p.2 u) - (A p.2-A w) (p.1-u))
  let b := (u,w)
  let X := (ContinuousLinearEquiv.refl ℝ U).prodCongr J
  have ca : ContDiffAt ℝ n (fun p : U × Z => A p.2) b := ha.comp b contDiffAt_snd
  have cH : ContDiffAt ℝ n H b := contDiffAt_fst.prodMk
    ((contDiffAt_snd.sub (ca.clm_apply contDiffAt_const)).sub
      ((ca.sub contDiffAt_const).clm_apply (contDiffAt_fst.sub contDiffAt_const)))
  have zeroD : HasFDerivAt (𝕜 := ℝ) (fun p : U × Z => (A p.2-A w) (p.1-u)) 0 b := by
    have d := ((ca.sub (contDiffAt_const (c := A w))).differentiableAt hn).hasFDerivAt.clm_apply
      ((hasFDerivAt_fst (𝕜 := ℝ) (p := b)).sub_const u)
    simpa [b] using d
  have deriv : HasFDerivAt H X.toContinuousLinearMap b := by
    have d := (hasFDerivAt_fst (𝕜 := ℝ) (p := b)).prodMk
      ((dJ.comp b (hasFDerivAt_snd (𝕜 := ℝ) (p := b))).sub zeroD)
    convert d using 1
    ext x <;> simp [X]
  let T := cH.toOpenPartialHomeomorph H deriv hn
  have src : b ∈ T.source := cH.mem_toOpenPartialHomeomorph_source deriv hn
  let g (p : Z × U) := (p.2,p.1+A w (p.2-u))
  let a := (w-A w u,u)
  have base : g a = H b := by simp [g,a,H,b]
  have cg : ContDiff ℝ n g := contDiff_snd.prodMk (contDiff_fst.add ((A w).contDiff.comp (contDiff_snd.sub contDiff_const)))
  have inv : ContDiffAt ℝ n T.symm (g a) := base.symm ▸ cH.to_localInverse deriv hn
  let S (p : Z × U) := (T.symm (g p)).2
  refine ⟨S,congrArg Prod.snd ((congrArg T.symm base).trans (T.left_inv src)),
    contDiffAt_snd.comp a (inv.comp a cg.contDiffAt),?_⟩
  have mem : g a ∈ T.target := base.symm ▸ T.map_source src
  filter_upwards [cg.continuous.continuousAt (T.open_target.mem_nhds mem)] with p hp
  have hit : H (T.symm (g p)) = g p := T.right_inv hp
  have h₁ := congrArg Prod.fst hit
  change (T.symm (g p)).1 = p.2 at h₁
  have h₂ := congrArg Prod.snd hit
  change S p - A (S p) u - (A (S p)-A w) ((T.symm (g p)).1-u) = p.1 + A w (p.2-u) at h₂
  rw [h₁,ContinuousLinearMap.sub_apply,map_sub,map_sub] at h₂
  abel_nf at h₂ ⊢
  linear_combination (norm := abel) h₂

#print axioms solution_at
end MinimizingSard.ImplicitControl
