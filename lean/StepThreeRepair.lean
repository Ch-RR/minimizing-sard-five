import HigherRankSard
import BracketWordRepair

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] {m : ℕ} {Γ : Geometry M m}

private theorem short_connectors {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    (c : OpenPartialHomeomorph M State) (y : State) (A : State × P → State) (basis : P ≃L[ℝ] State)
    (zero : ∀ᶠ z in 𝓝 y, A (z,0) = 0)
    (jet : HasStrictFDerivAt A (basis.toContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ State P)) (y,0))
    {α L : ℝ} (hα : 0 ≤ α) (hL : 0 ≤ L)
    (cost : ∀ᶠ p : State × P in 𝓝 (y,0), ∃ b ∈ attainableLengths Γ (c.symm p.1) (c.symm (p.1+A p)),
      b ≤ L*‖p.2‖^α) : ∃ K : ℝ, ∀ᶠ p : State × State in 𝓝 (y,y),
      ∃ b ∈ attainableLengths Γ (c.symm p.1) (c.symm p.2), b ≤ K*‖p.2-p.1‖^α := by
  let H (p : State × P) := (p.1,A p)
  let e := (ContinuousLinearEquiv.refl ℝ State).prodCongr basis
  have hd : HasStrictFDerivAt H (e : (State × P) →L[ℝ] (State × State)) (y,0) :=
    (hasStrictFDerivAt_fst (𝕜 := ℝ) (p := (y,(0:P)))).prodMk jet
  let S := hd.localInverse H e (y,0)
  have h0 : H (y,0) = (y,0) := Prod.ext rfl zero.self_of_nhds
  have ds : HasStrictFDerivAt S (e.symm : (State × State) →L[ℝ] State × P) (y,0) := h0 ▸ hd.to_localInverse
  obtain ⟨C,U,hU,lip⟩ := ds.exists_lipschitzOnWith
  let w (p : State × State) := (p.1,p.2-p.1)
  let w0 (p : State × State) := (p.1,(0:State))
  let v0 (p : State × State) := (p.1,(0:P))
  have cw : Tendsto w (𝓝 (y,y)) (𝓝 (y,0)) := by
    have con : Continuous w := continuous_fst.prodMk (continuous_snd.sub continuous_fst)
    simpa [w] using con.tendsto (y,y)
  have cw0 : Tendsto w0 (𝓝 (y,y)) (𝓝 (y,0)) := continuousAt_fst.prodMk continuousAt_const
  have cv0 : Tendsto v0 (𝓝 (y,y)) (𝓝 (y,0)) := continuousAt_fst.prodMk continuousAt_const
  have left : ∀ᶠ p : State × P in 𝓝 (y,0), S (H p) = p := hd.eventually_left_inverse
  have right : ∀ᶠ p : State × State in 𝓝 (y,0), H (S p) = p := h0 ▸ hd.eventually_right_inverse
  have s0 : S (y,0) = (y,0) := h0 ▸ hd.localInverse_apply_image
  have cs : Tendsto S (𝓝 (y,0)) (𝓝 (y,0)) := s0 ▸ ds.continuousAt
  refine ⟨L*(C:ℝ)^α,?_⟩
  filter_upwards [cw hU,cw0 hU,cv0 left,cw right,(cs.comp cw) cost,
      (continuous_fst.continuousAt (x := (y,y))) zero] with p hu hu0 hleft hright use hz
  have base : H (v0 p) = w0 p := Prod.ext rfl hz
  change S (H (v0 p)) = v0 p at hleft
  change H (S (w p)) = w p at hright
  rw [base] at hleft
  have xeq := congrArg Prod.fst hright
  have aeq := congrArg Prod.snd hright
  change (S (w p)).1 = p.1 at xeq
  change A (S (w p)) = p.2 - p.1 at aeq
  obtain ⟨b,hb,bd⟩ := use
  change b ∈ attainableLengths Γ (c.symm (S (w p)).1) (c.symm ((S (w p)).1 + A (S (w p)))) at hb
  rw [xeq,aeq,add_sub_cancel] at hb
  have bound := lip.dist_le_mul _ hu _ hu0
  rw [hleft] at bound
  have parm : ‖(S (w p)).2‖ ≤ (C:ℝ) * ‖p.2-p.1‖ := by
    have le := (le_max_right (dist (S (w p)).1 p.1) (dist (S (w p)).2 0)).trans bound
    simpa [w,w0,v0,Prod.dist_eq] using le
  have root := Real.rpow_le_rpow (norm_nonneg _) parm hα
  rw [Real.mul_rpow (by positivity) (norm_nonneg _)] at root
  exact ⟨b,hb,bd.trans (by simpa only [Function.comp_apply,mul_assoc] using mul_le_mul_of_nonneg_left root hL)⟩


/-- Actual competitors between both variable endpoints, at the root exponent
of a spanning bracket layer. No minimizing trajectory or fixed-source reachability is needed. -/
theorem frame_root_connectors (e : Frame M m) (he : e ∈ Γ.frames) {q : State} (hq : q ∈ e.chart.target)
    {d : ℕ} (hd : d ≤ 4) (full : wordLayer e.X q d = ⊤) :
    ∃ K : ℝ, ∀ᶠ p : State × State in 𝓝 (q,q),
      ∃ b ∈ attainableLengths Γ (e.chart.symm p.1) (e.chart.symm p.2), b ≤ K*‖p.2-p.1‖^(1/(d:ℝ)) := by
  have prof : HasGeneratorProfiles e := all_frame_generator_profiles e
  classical
  let S := {v : State | ∃ w : BracketWord m, w.order ≤ d ∧ w.eval e.X q = v}
  have span : Submodule.span ℝ S = ⊤ := full
  have dim : Module.finrank ℝ (Submodule.span ℝ S) = 5 := by rw [span,finrank_top,Module.finrank_fin_fun]
  have ex := Submodule.exists_fun_fin_finrank_span_eq ℝ S
  rw [dim] at ex
  obtain ⟨v,hv,_,ind⟩ := ex
  choose w hw eq using hv
  choose W order lead using fun i => bracket_repair_word_of_profiles e prof he hq (w i) ((hw i).trans hd)
  let B := basisOfPiSpaceOfLinearIndependent ind
  let L := B.equivFun.symm.toContinuousLinearEquiv
  have cols (s : State) : ∑ i, s i • (W i).profile (q,0) = L s := by
    have at0 (i) : (W i).profile (q,0) = v i := (lead i).self_of_nhds.trans (eq i)
    change _ = B.equivFun.symm s
    simp only [at0,Module.Basis.equivFun_symm_apply]
    exact congrArg (fun f : Fin 5 → State => ∑ i, s i • f i) (coe_basisOfPiSpaceOfLinearIndependent ind).symm
  obtain ⟨A,z,j,motion⟩ := word_motion_of_order W (d := d) (fun i => by rw [order i]; exact hw i) L cols
  exact short_connectors e.chart q A L z j (by positivity) (Finset.sum_nonneg fun i _ => (W i).nonneg) motion

theorem ae_rank_three_connectors (e : Frame M 3) {Γ : Geometry M 3} (he : e ∈ Γ.frames) :
    ∀ᵐ q : State, q ∈ e.chart.target → 4 ≤ Module.finrank ℝ (wordLayer e.X q 2) ∧
      ∃ K : ℝ, ∀ᶠ p : State × State in 𝓝 (q,q),
        ∃ b ∈ attainableLengths Γ (e.chart.symm p.1) (e.chart.symm p.2), b ≤ K*‖p.2-p.1‖^(1/3:ℝ) := by
  filter_upwards [ae_frame_growth_bounds e (by decide)] with q good
  intro hq
  obtain ⟨two,three,_⟩ := good hq
  have top : wordLayer e.X q 3 = ⊤ := Submodule.eq_of_le_of_finrank_le le_top (by
    rw [finrank_top,Module.finrank_fin_fun]; exact three)
  exact ⟨two,frame_root_connectors e he hq (d := 3) (by decide) top⟩

#print axioms frame_root_connectors
#print axioms ae_rank_three_connectors
end MinimizingSard.Five
