import AllFrameAdjoint
import AllRankLengthValue

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
open Volterra
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] {m n : ℕ}

/-- A continuous coefficient whose L² pairings all vanish vanishes even
at the terminal time. The test is the coefficient itself. -/
theorem zero_terminal_of_zero_pairings (b : C(Time,Fiber m))
    (kill : ∀ h : Control m, (∫ r in (0:ℝ)..1, ∑ i, h r i*b (clamp r) i) = 0) :
    b (clamp 1) = 0 := by
  let c (r : ℝ) := b (clamp r)
  have cc : Continuous c := b.continuous.comp continuous_projIcc
  have mb : MemLp c 2 controlMeasure := MemLp.of_bound cc.aestronglyMeasurable ‖b‖
    (.of_forall fun r => b.norm_coe_le_norm _)
  let F (r : ℝ) := ∑ i, (c r i)^2
  have cf : Continuous F := continuous_finset_sum _ (fun i _ => ((continuous_apply i).comp cc).pow 2)
  have same : (fun r => ∑ i, (mb.toLp c) r i * b (clamp r) i) =ᵐ[volume.restrict (uIoc (0:ℝ) 1)] F := by
    rw [uIoc_of_le zero_le_one,Measure.restrict_congr_set Ioc_ae_eq_Icc]
    filter_upwards [mb.coeFn_toLp] with r hr
    simp only [hr,F,c,pow_two]
  have k := kill (mb.toLp c)
  rw [intervalIntegral.integral_congr_ae_restrict same] at k
  have nn (r : ℝ) : 0 ≤ F r := Finset.sum_nonneg fun i _ => sq_nonneg _
  have ae := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae zero_le_one
    (Filter.Eventually.of_forall nn) (cf.intervalIntegrable 0 1)).mp k
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc] at ae
  have eq := Measure.eqOn_Icc_of_ae_eq (μ := volume) zero_ne_one ae cf.continuousOn continuousOn_const (right_mem_Icc.mpr zero_le_one)
  have van : ∑ i, (c 1 i)^2 = 0 := eq
  ext i
  exact sq_eq_zero_iff.mp ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).mp van i (Finset.mem_univ _))

set_option maxHeartbeats 600000 in
/-- Every covector annihilating the whole endpoint derivative annihilates
the full horizontal space in the final chart, including for an idle last
segment and an arbitrary finite sequence of earlier charts. -/
theorem final_horizontal_annihilator (e : Fin (n+1) → Frame M m) (u : Fin (n+1) → Control m)
    (q : Fin ((n+1)+1) → M) (seg : ∀ i, Segment (e i) (u i) (q i.castSucc) (q i.succ))
    (c : OpenPartialHomeomorph M State) (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M)
    (cy : q (Fin.last (n+1)) ∈ c.source) (G : (Fin (n+1) → Control m) → State)
    (dg : DifferentiableAt ℝ G u)
    (graph : ∀ᶠ b in 𝓝 u, G b ∈ c.target ∧ ∀ y, Joins e b (q 0) y ↔ y = c.symm (G b))
    (η : State →L[ℝ] ℝ) (ann : ∀ h, η (fderiv ℝ G u h) = 0) :
    let j := Fin.last n
    let y := q j.succ
    ∀ i, η (fderiv ℝ (c ∘ (e j).chart.symm) ((e j).chart y) ((e j).X i ((e j).chart y))) = 0 := by
  let j := Fin.last n
  let e₀ := e j
  let y := q j.succ
  let s := q j.castSucc
  let v := u j
  have ey : y ∈ e₀.chart.source := (seg j).2.1
  have es : s ∈ e₀.chart.source := (seg j).1
  have cy' : y ∈ c.source := by simpa [y,j,Fin.succ_last] using cy
  have fg := frame_segment_graph e₀ v s y (seg j) 1 le_rfl
  obtain ⟨F,df,gf⟩ := fg
  obtain ⟨H,dh,gh⟩ := segment_in_charts_of_graph e₀ v s y (seg j) 1 ⟨F,df,gf⟩ e₀.chart c
    e₀.compatible hc es cy'
  let I (b : Control m) := (e₀.chart s,b)
  have di : HasFDerivAt I (ContinuousLinearMap.inr ℝ State (Control m)) v :=
    (hasFDerivAt_const _ _).prodMk (hasFDerivAt_id v)
  have tail : ∀ᶠ b in 𝓝 v, H (I b) ∈ c.target ∧ ∀ t, Segment e₀ b s t ↔ t = c.symm (H (I b)) := by
    filter_upwards [di.continuousAt.tendsto gh] with b h
    exact ⟨h.2.1,by simpa only [I,e₀.chart.left_inv es] using h.2.2⟩
  have same := last_slice_agrees e u q seg c G graph (H ∘ I) tail
  let upd := Function.update u j
  have du : DifferentiableAt ℝ upd v := by
    apply differentiableAt_pi.mpr
    intro l
    by_cases eq : l = j
    · subst l
      simpa only [upd,Function.update_self] using (differentiableAt_id (𝕜 := ℝ) (x := v))
    · simpa only [upd,Function.update_of_ne eq] using (differentiableAt_const (𝕜 := ℝ) (x := v) (u l))
  have uv : upd v = u := Function.update_eq_self _ _
  have dg' : DifferentiableAt ℝ G (upd v) := uv.symm ▸ dg
  have ds := ((dg'.hasFDerivAt.comp v du.hasFDerivAt).congr_of_eventuallyEq same.symm).unique
    ((dh.differentiableAt (by decide)).hasFDerivAt.comp v di)
  let J := fderiv ℝ (c ∘ e₀.chart.symm) (e₀.chart y)
  have trans := segment_transition_derivative e₀ v (seg j) e₀.chart c e₀.compatible hc es cy'
    F H (df.differentiableAt (by decide)) (dh.differentiableAt (by decide)) gf gh
  have localAnn (h : Control m) : η (J (fderiv ℝ F (e₀.chart s,v) (0,h))) = 0 := by
    have a := trans 0 h
    rw [map_zero] at a
    have b := DFunLike.congr_fun ds h
    change fderiv ℝ G (upd v) (fderiv ℝ upd v h) = fderiv ℝ H (e₀.chart s,v) (0,h) at b
    rw [uv] at b
    exact (congrArg η a.symm).trans ((congrArg η b.symm).trans (ann _))
  obtain ⟨w,p,hw,wy,pe,_,rep⟩ := frame_adjoint_representation e₀ v (seg j) F
    (df.differentiableAt (by decide)) gf (η.comp J)
  let b : C(Time,Fiber m) := ⟨fun t i => p t (e₀.X i (w t)),continuous_pi fun i => p.continuous.clm_apply
    ((e₀.smooth i).continuousOn.comp_continuous w.continuous hw.1)⟩
  have stop := zero_terminal_of_zero_pairings b (fun h => by
    have val := rep (0,h)
    change η (J (fderiv ℝ F (e₀.chart s,v) (0,h))) = p (clamp 0) 0 + _ at val
    rw [localAnn,map_zero,zero_add] at val
    exact val.symm)
  dsimp only
  intro i
  have atI := congrFun stop i
  change p (clamp 1) (e₀.X i (w (clamp 1))) = 0 at atI
  rwa [pe,wy] at atI

variable [IsManifold 𝓘(ℝ,State) ∞ M]

theorem all_rank_endpoint_floor (e : Fin (n+1) → Frame M m) (u : Fin (n+1) → Control m)
    (x y : M) (path : Joins e u x y) (c : OpenPartialHomeomorph M State)
    (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (cy : y ∈ c.source) (G : (Fin (n+1) → Control m) → State)
    (dg : DifferentiableAt ℝ G u)
    (graph : ∀ᶠ b in 𝓝 u, G b ∈ c.target ∧ ∀ t, Joins e b x t ↔ t = c.symm (G b)) :
    m ≤ Module.finrank ℝ (LinearMap.range (fderiv ℝ G u).toLinearMap) := by
  obtain ⟨q,rfl,rfl,seg⟩ := path
  let j := Fin.last n
  let f := e j
  let y := q j.succ
  let z := f.chart y
  have ey : y ∈ f.chart.source := (seg j).2.1
  have cy' : y ∈ c.source := by simpa [y,j,Fin.succ_last] using cy
  let J := fderiv ℝ (c ∘ f.chart.symm) z
  obtain ⟨B,hB⟩ := ContinuousLinearMap.IsInvertible.of_inverse
    (transition_left c f.chart hc f.compatible y cy' ey) (transition_left f.chart c f.compatible hc y ey cy')
  let W := LinearMap.range (fderiv ℝ G u).toLinearMap
  let S := (Submodule.span ℝ (range (fun i => f.X i z))).map B.toLinearEquiv.toLinearMap
  have sub : S ≤ W := by
    apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change B (f.X i z) ∈ W
    rw [show B (f.X i z) = J (f.X i z) from DFunLike.congr_fun hB _]
    by_contra outside
    obtain ⟨l,nz,zero⟩ := W.exists_dual_map_eq_bot_of_notMem outside inferInstance
    apply nz
    apply final_horizontal_annihilator e u q seg c hc cy G dg graph l.toContinuousLinearMap _ i
    intro h
    have killed : l (fderiv ℝ G u h) ∈ W.map l := ⟨_,⟨h,rfl⟩,rfl⟩
    rwa [zero] at killed
  have d := Submodule.finrank_mono sub
  simpa only [S,B.toLinearEquiv.finrank_map_eq,finrank_span_eq_card (f.independent z (f.chart.map_source ey)),
    Fintype.card_fin] using d

#print axioms zero_terminal_of_zero_pairings
#print axioms final_horizontal_annihilator
#print axioms all_rank_endpoint_floor
end MinimizingSard.Five
