import KernelDescentSelection
import WholeHessianFlag
import CorankTwoLengthFlag

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five

private abbrev Plane := ℝ × ℝ
variable {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]

/-- Before straightening any fields, some actual bracket word of order at
most three points outside the rank-three endpoint range at this point. -/
theorem terminal_word_outside_range {M : Type*} [TopologicalSpace M] [ChartedSpace State M]
    [IsManifold 𝓘(ℝ,State) ∞ M] (e : Frame M 2) (c : OpenPartialHomeomorph M State)
    (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (y : M) (he : y ∈ e.chart.source) (hy : y ∈ c.source)
    (W : Submodule ℝ State) (dim : Module.finrank ℝ W = 3)
    (growth : 4 ≤ Module.finrank ℝ (wordLayer e.X (e.chart y) 3)) :
    ∃ w : BracketWord 2, w.order ≤ 3 ∧
      fderiv ℝ (c ∘ e.chart.symm) (e.chart y) (w.eval e.X (e.chart y)) ∉ W := by
  by_contra! all
  obtain ⟨T,eq⟩ := ContinuousLinearMap.IsInvertible.of_inverse
    (transition_left c e.chart hc e.compatible y hy he) (transition_left e.chart c e.compatible hc y he hy)
  have incl : chartThirdLayer e c y ≤ W := by
    apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨w,ord,rfl⟩
    exact all w ord
  have size := Submodule.finrank_mono incl
  unfold chartThirdLayer at size
  rw [← eq,dim] at size
  change Module.finrank ℝ ((wordLayer e.X (e.chart y) 3).map T.toLinearEquiv.toLinearMap) ≤ 3 at size
  rw [T.toLinearEquiv.finrank_map_eq] at size
  omega

#print axioms terminal_word_outside_range

private theorem minor_of_infinite {K : Type*} [AddCommGroup K] [Module ℝ K]
    (B : K →ₗ[ℝ] K →ₗ[ℝ] ℝ) (inf : ¬ FiniteDimensional ℝ (LinearMap.range B)) :
    ∃ i j a b, B i a * B j b ≠ B i b * B j a := by
  by_contra! dep
  apply inf
  by_cases nz : ∃ i a, B i a ≠ 0
  · obtain ⟨i,a,ha⟩ := nz
    apply Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℝ {B i})
    rintro _ ⟨j,rfl⟩
    apply Submodule.mem_span_singleton.mpr
    refine ⟨B j a / B i a,?_⟩
    ext b
    change (B j a/B i a)*B i b = B j b
    field_simp
    linarith only [dep i j a b]
  · push_neg at nz
    have zero : B = 0 := by ext i a; exact nz i a
    rw [zero,LinearMap.range_zero]
    infer_instance

set_option maxHeartbeats 1100000 in
/-- Identify both scalar Hessian conditions in coordinates whose first axis
represents a nonzero third-layer direction modulo the endpoint derivative. -/
theorem adapted_kernel_rows {M : Type*} [TopologicalSpace M] [ChartedSpace State M]
    [IsManifold 𝓘(ℝ,State) ∞ M] {n : ℕ} (e : Fin (n+1) → Frame M 2) (w : Fin (n+1) → Control 2)
    {x y : M} (distinct : x ≠ y) (path : Joins e w x y) (c : OpenPartialHomeomorph M State)
    (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (hy : y ∈ c.source)
    (G : (Fin (n+1) → Control 2) → State)
    (graph : ∀ᶠ b in 𝓝 w, G b ∈ c.target ∧ ∀ z, Joins e b x z ↔ z = c.symm (G b))
    (i : Fin (n+1)) (moving : w i ≠ 0) (last : ∀ j, i < j → w j = 0)
    (π : State →L[ℝ] Plane) (onto : Function.Surjective π)
    (cok : LinearMap.ker π.toLinearMap = LinearMap.range (fderiv ℝ G w).toLinearMap)
    (growth : 4 ≤ Module.finrank ℝ (wordLayer (e i).X ((e i).chart y) 3))
    (u : State) (layer : u ∈ chartThirdLayer (e i) c y) (axis : π u = (1,0))
    (noReg : ∀ h : LinearMap.ker (fderiv ℝ G w).toLinearMap,
      ¬ Function.Surjective (fun l : LinearMap.ker (fderiv ℝ G w).toLinearMap => π (fderiv ℝ (fderiv ℝ G) w h l))) :
    let A := kernelRowAt G w ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp π)
    let B := kernelRowAt G w ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp π)
    (∀ h l, B h l = 0) ∧ ∃ i j a b, A i a * A j b ≠ A i b * A j a := by
  intro A B
  let K := LinearMap.ker (fderiv ℝ G w).toLinearMap
  let H (p : K × K) := π (fderiv ℝ (fderiv ℝ G) w p.1 p.2)
  let L := Submodule.span ℝ (range H)
  obtain ⟨dim,flag,_,inf⟩ := whole_hessian_flag e w distinct path c hc hy G graph i moving last π onto cok growth noReg
  have mem : (1,0) ∈ L := by
    rw [flag] at layer
    exact axis ▸ (show π u ∈ L from layer)
  have eq : Submodule.span ℝ {((1,0):Plane)} = L := by
    apply Submodule.eq_of_le_of_finrank_le (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr mem))
    rw [finrank_span_singleton (by norm_num : ((1,0):Plane) ≠ 0)]
    exact dim.le
  have vanish (h l : K) : B h l = 0 := by
    have hmem : H (h,l) ∈ L := Submodule.subset_span ⟨(h,l),rfl⟩
    rw [← eq] at hmem
    obtain ⟨t,ht⟩ := Submodule.mem_span_singleton.mp hmem
    change (H (h,l)).2 = 0
    simpa using (congrArg Prod.snd ht).symm
  have zero : B = 0 := by ext h l; exact vanish h l
  have fin : FiniteDimensional ℝ (LinearMap.range B) := by rw [zero,LinearMap.range_zero]; infer_instance
  exact ⟨vanish,minor_of_infinite A (fun fa => inf ⟨fa,fin⟩)⟩

variable [CompleteSpace U]

/-- Fix the regular coordinates while retaining the full original kernel as
parameter space. Each displacement lies exactly in the prescribed plane. -/
theorem plane_level_family (G : U → State) (w : U) (smooth : ContDiffAt ℝ 4 G w)
    (π : State →L[ℝ] Plane) (u v : State) (hu : π u = (1,0)) (hv : π v = (0,1))
    (cok : LinearMap.ker π.toLinearMap = LinearMap.range (fderiv ℝ G w).toLinearMap) :
    let K := LinearMap.ker (fderiv ℝ G w).toLinearMap
    ∃ S : K → U, S 0 = 0 ∧ ContDiffAt ℝ 4 S 0 ∧ HasFDerivAt S K.subtypeL 0 ∧
      ∀ᶠ z in 𝓝 0, let d := G (w+S z)-G w
        G (w+S z) = G w + (π d).1 • u + (π d).2 • v := by
  intro K
  let R := LinearMap.ker π.toLinearMap
  let a := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp π
  let b := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp π
  let J := ContinuousLinearMap.id ℝ State - a.smulRight u - b.smulRight v
  have land (z) : J z ∈ R := by
    change π (z - (π z).1 • u - (π z).2 • v) = 0
    rw [map_sub,map_sub,map_smul,map_smul,hu,hv]
    ext <;> simp
  let P := J.codRestrict R land
  let D := fderiv ℝ G w
  have ann (z) : π (D z) = 0 := by
    change D z ∈ R
    rw [show R = _ from cok]
    exact ⟨z,rfl⟩
  have keep (z) : (P (D z)).val = D z := by
    change D z - (π (D z)).1 • u - (π (D z)).2 • v = D z
    simp [ann]
  let F (z : U) := P (G (w+z))
  have tr := (hasFDerivAt_id (𝕜 := ℝ) (0:U)).const_add w
  have sg : ContDiffAt ℝ 4 G (w+(0:U)) := by simpa using smooth
  have cf : ContDiffAt ℝ 4 F 0 := P.contDiff.contDiffAt.comp 0 (sg.comp 0 (contDiffAt_const.add contDiffAt_id))
  have dg : HasFDerivAt G D (w+(0:U)) := by simpa [D] using (smooth.differentiableAt (by decide)).hasFDerivAt
  have df : fderiv ℝ F 0 = P.comp D := (P.hasFDerivAt.comp 0 (dg.comp 0 tr)).fderiv
  have sur : Function.Surjective (fderiv ℝ F 0) := by
    intro r
    obtain ⟨z,hz⟩ := (show r.val ∈ LinearMap.range D.toLinearMap from cok ▸ r.property)
    exact ⟨z,Subtype.ext (by rw [df]; exact (keep z).trans hz)⟩
  obtain ⟨T,t0,ct,dt,level⟩ := Reduced.level_chart F cf sur
  let I := K.subtypeL.codRestrict (LinearMap.ker (fderiv ℝ F 0).toLinearMap) (fun z => by
    change fderiv ℝ F 0 z.val = 0
    rw [df,ContinuousLinearMap.comp_apply,show D z.val = 0 from z.property,map_zero])
  let S := T ∘ I
  refine ⟨S,by simp [S,t0],(by simpa only [map_zero] using ct.comp (0:K) I.contDiff.contDiffAt),?_,?_⟩
  · have atI : HasFDerivAt T (LinearMap.ker (fderiv ℝ F 0).toLinearMap).subtypeL (I 0) := by simpa only [map_zero] using dt
    exact atI.comp 0 I.hasFDerivAt
  · have lim : Tendsto I (𝓝 0) (𝓝 0) := by simpa using I.continuous.tendsto 0
    filter_upwards [lim level] with z hz
    have hit : P (G (w+S z)) = P (G w) := by simpa [F,S] using hz
    let d := G (w+S z)-G w
    have zero : P d = 0 := by rw [show P d = _ from map_sub P _ _,hit,sub_self]
    have de : d - (π d).1 • u - (π d).2 • v = 0 := congrArg Subtype.val zero
    change G (w+S z) = G w + (π d).1 • u + (π d).2 • v
    dsimp only [d] at de ⊢
    linear_combination (norm := abel) de

#print axioms adapted_kernel_rows
#print axioms plane_level_family

omit [CompleteSpace U] in
theorem scalar_jet (G : U → State) (w : U) (smooth : ContDiffAt ℝ 4 G w)
    (p : State →L[ℝ] ℝ) (ann : ∀ z, p (fderiv ℝ G w z) = 0)
    (S : LinearMap.ker (fderiv ℝ G w).toLinearMap → U) (s0 : S 0 = 0)
    (cs : ContDiffAt ℝ 4 S 0) (ds : HasFDerivAt S (LinearMap.ker (fderiv ℝ G w).toLinearMap).subtypeL 0) :
    let f := fun z => p (G (w+S z)-G w)
    ContDiffAt ℝ 4 f 0 ∧ f 0 = 0 ∧ fderiv ℝ f 0 = 0 ∧
      ∀ h l, fderiv ℝ (fderiv ℝ f) 0 h l = kernelRowAt G w p h l := by
  let K := LinearMap.ker (fderiv ℝ G w).toLinearMap
  let A (z : K) := w+S z
  have a0 : A 0 = w := by simp [A,s0]
  have da : HasFDerivAt A K.subtypeL 0 := ds.const_add w
  have ca : ContDiffAt ℝ 4 A 0 := contDiffAt_const.add cs
  let C (z : State) := p (z-G w)
  have cc : ContDiff ℝ 4 C := p.contDiff.comp (contDiff_id.sub contDiff_const)
  have dc (z : State) : fderiv ℝ C z = p := (p.hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const (G w))).fderiv
  have sg : ContDiffAt ℝ 4 G (A 0) := a0.symm ▸ smooth
  change ContDiffAt ℝ 4 (C ∘ (G ∘ A)) 0 ∧ _
  refine ⟨cc.contDiffAt.comp 0 (sg.comp 0 ca),by simp [s0],?_,?_⟩
  · change fderiv ℝ (C ∘ (G ∘ A)) 0 = 0
    rw [fderiv_comp 0 (cc.differentiable (by decide) _) ((sg.comp 0 ca).differentiableAt (by decide)),
      fderiv_comp 0 (sg.differentiableAt (by decide)) da.differentiableAt,dc,da.fderiv,a0]
    exact ContinuousLinearMap.ext fun h => ann _
  · intro h l
    have hx : fderiv ℝ G w h.val = 0 := h.property
    have eq := Transport.intrinsic_second_variation A G C 0 h l (ContinuousLinearMap.id ℝ ℝ)
      (ca.of_le (by decide)) (sg.of_le (by decide)) (cc.of_le (by decide)).contDiffAt
      (by simpa only [a0,da.fderiv,Submodule.subtypeL_apply] using hx)
      (by simpa only [dc,a0,ContinuousLinearMap.id_apply] using ann)
    simpa only [a0,da.fderiv,Submodule.subtypeL_apply,dc,ContinuousLinearMap.id_apply] using eq

set_option maxHeartbeats 1800000 in
/-- For a supplied adapted pair of axes, the actual endpoint and the terminal
flag imply the descent box, with no reduced family or jet data as premises. -/
theorem ae_box_on_adapted_plane {M : Type*} [TopologicalSpace M] [ChartedSpace State M]
    [IsManifold 𝓘(ℝ,State) ∞ M] (Γ : Geometry M 2) (chart : OpenPartialHomeomorph M State)
    (hc : chart ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (x : M) :
    ∀ᵐ q : State, q ∈ chart.target → ∀ {n : ℕ} (d : Fin (n+1) → Frame M 2)
      (w : Fin (n+1) → Control 2) (G : (Fin (n+1) → Control 2) → State),
      let y := chart.symm q
      x ≠ y → (∀ j, d j ∈ Γ.frames) → Joins d w x y →
      (∀ (k : ℕ) (r : Fin (k+1) → Frame M 2) (b : Fin (k+1) → Control 2),
        (∀ j, r j ∈ Γ.frames) → Joins r b x y → length w ≤ length b) →
      (∀ᶠ b in 𝓝 w, G b ∈ chart.target ∧ ∀ z, Joins d b x z ↔ z = chart.symm (G b)) →
      ¬ HasCostMultiplier length (fderiv ℝ G w) w →
      ∀ i : Fin (n+1), w i ≠ 0 → (∀ j, i < j → w j = 0) →
      4 ≤ Module.finrank ℝ (wordLayer (d i).X ((d i).chart y) 3) →
      ∀ (π : State →L[ℝ] Plane) (u v : State),
      LinearMap.ker π.toLinearMap = LinearMap.range (fderiv ℝ G w).toLinearMap →
      u ∈ chartThirdLayer (d i) chart y → π u = (1,0) → π v = (0,1) →
      ∃ k : ℕ, (k = 3 ∨ k = 4) ∧ ∃ a₀ b₀ c : ℝ, 0 < c ∧ ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ → ∀ a b : ℝ,
        |a-a₀| < δ → |b-b₀| < δ →
        pointedLengthValue Γ x (chart.symm (q+(t^2*a) • u+(t^k*b) • v)) ≤
          pointedLengthValue Γ x y-c*t := by
  filter_upwards [mixed_kernel_boxes_of_repair Γ chart (ae_compatible_value_repair Γ chart hc),ae_compatible_value_repair Γ chart hc,
    ae_corank_two_length_flag Γ x chart hc] with q box value flag
  intro hq n d w G y distinct hd path minimal graph absent i moving last growth π u v cok layer hu hv
  have hy : y ∈ chart.source := chart.map_target hq
  have atw := graph.self_of_nhds
  have center : q = G w := chart.symm.injOn hq atw.1 ((atw.2 _).mp path)
  have reach : (attainableLengths Γ x y).Nonempty := ⟨length w,n,d,w,hd,path,rfl⟩
  obtain ⟨V,op,inside,cont⟩ := (value hq x reach).1
  have region : q ∈ continuityRegion (fun s => pointedLengthValue Γ x (chart.symm s)) :=
    mem_iUnion.mpr ⟨V,mem_iUnion.mpr ⟨⟨op,cont⟩,inside⟩⟩
  have onto : Function.Surjective π := by
    rintro ⟨a,b⟩
    exact ⟨a • u+b • v,by rw [map_add,map_smul,map_smul,hu,hv]; ext <;> simp⟩
  have noReg := (flag region n d w y G hy hd path minimal graph center π onto cok absent).1
  obtain ⟨van,rank⟩ := adapted_kernel_rows d w distinct path chart hc hy G graph i moving last π onto cok growth u layer hu noReg
  obtain ⟨G₀,_,sm,gr,_⟩ := path_endpoint_and_singularity d w x y path chart hc hy 4 (by decide)
  have smooth : ContDiffAt ℝ 4 G w := sm.congr_of_eventuallyEq (by
    filter_upwards [graph,gr] with b gb rb
    exact (chart.right_inv gb.1).symm.trans ((congrArg chart ((rb.2 _).mp ((gb.2 _).mpr rfl))).trans (chart.right_inv rb.1)))
  obtain ⟨S,s0,cs,ds,level⟩ := plane_level_family G w smooth π u v hu hv cok
  let p₁ := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp π
  let p₂ := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp π
  have ann (z) : π (fderiv ℝ G w z) = 0 := by
    change fderiv ℝ G w z ∈ LinearMap.ker π.toLinearMap
    rw [cok]
    exact ⟨z,rfl⟩
  obtain ⟨cf,f0,f1,hf⟩ := scalar_jet G w smooth p₁ (fun z => congrArg Prod.fst (ann z)) S s0 cs ds
  obtain ⟨cg,g0,g1,hg⟩ := scalar_jet G w smooth p₂ (fun z => congrArg Prod.snd (ann z)) S s0 cs ds
  apply box hq d w x G hd path minimal (graph.mono fun _ h => h.2) absent S _ _ u v s0 ds
    (by simpa only [center] using level) (cf.of_le (by decide)) cg f0 f1 g0 g1
  · exact ContinuousLinearMap.ext fun h => ContinuousLinearMap.ext fun l => (hg h l).trans (van h l)
  · obtain ⟨i,j,a,b,ne⟩ := rank
    let f := fun z => p₁ (G (w+S z)-G w)
    have ident (h l) : Return.polarRow f 1 h l = kernelRowAt G w p₁ h l := by
      simpa [Return.polarRow,f] using hf h l
    refine ⟨i,j,a,b,?_⟩
    change Return.polarRow f 1 i a * Return.polarRow f 1 j b ≠
      Return.polarRow f 1 i b * Return.polarRow f 1 j a
    rw [ident,ident,ident,ident]
    exact ne

#print axioms ae_box_on_adapted_plane

theorem quotient_axes (W : Submodule ℝ State) (dim : Module.finrank ℝ W = 3)
    (u v : State) (outside : u ∉ W) (transverse : v ∉ W ⊔ Submodule.span ℝ {u}) :
    ∃ π : State →L[ℝ] Plane, LinearMap.ker π.toLinearMap = W ∧ π u = (1,0) ∧ π v = (0,1) := by
  let T := ((LinearMap.fst ℝ ℝ ℝ).smulRight u + (LinearMap.snd ℝ ℝ ℝ).smulRight v)
  let J := W.mkQ.comp T
  have inj : Function.Injective J := by
    apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    rintro ⟨a,b⟩ hz
    have inside : a • u + b • v ∈ W := (Submodule.Quotient.mk_eq_zero W).mp hz
    let H := W ⊔ Submodule.span ℝ {u}
    have au : a • u ∈ H := H.smul_mem _ ((show Submodule.span ℝ {u} ≤ H from le_sup_right)
      (Submodule.subset_span (Set.mem_singleton u)))
    have bv : b • v ∈ H := (H.add_mem_iff_right au).mp ((show W ≤ H from le_sup_left) inside)
    have zb : b = 0 := by
      by_contra ne
      exact transverse ((H.smul_mem_iff ne).mp bv)
    have auW : a • u ∈ W := by simpa [zb] using inside
    have za : a = 0 := by
      by_contra ne
      exact outside ((W.smul_mem_iff ne).mp auW)
    simp [za,zb]
  have dimQ := W.finrank_quotient_add_finrank
  rw [dim,Module.finrank_fin_fun] at dimQ
  have dims : Module.finrank ℝ Plane = Module.finrank ℝ (State ⧸ W) := by
    rw [Module.finrank_prod,Module.finrank_self]
    omega
  let E := LinearEquiv.ofBijective J ⟨inj,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank dims).mp inj⟩
  let π := (E.symm.toLinearMap.comp W.mkQ).toContinuousLinearMap
  refine ⟨π,?_,?_,?_⟩
  · ext z
    change E.symm (W.mkQ z) = 0 ↔ z ∈ W
    rw [map_eq_zero_iff E.symm E.symm.injective]
    exact Submodule.Quotient.mk_eq_zero W
  · change E.symm (W.mkQ u) = _
    apply E.symm_apply_eq.mpr
    change W.mkQ u = W.mkQ ((1:ℝ) • u + (0:ℝ) • v)
    simp
  · change E.symm (W.mkQ v) = _
    apply E.symm_apply_eq.mpr
    change W.mkQ v = W.mkQ ((0:ℝ) • u + (1:ℝ) • v)
    simp

/-- For fixed vertical coordinate axes, almost every center excludes every
adapted minimizing witness without a supporting length multiplier. -/
private theorem ae_multiplier_on_split {M : Type*} [TopologicalSpace M] [ChartedSpace State M]
    [IsManifold 𝓘(ℝ,State) ∞ M] (Γ : Geometry M 2) (chart : OpenPartialHomeomorph M State)
    (hc : chart ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (x : M)
    (τ : State ≃L[ℝ] Reduced.Ambient) (u v : State) (tu : τ u = (0,![1,0])) (tv : τ v = (0,![0,1])) :
    ∀ᵐ q : State, q ∈ chart.target → ∀ {n : ℕ} (d : Fin (n+1) → Frame M 2)
      (w : Fin (n+1) → Control 2) (G : (Fin (n+1) → Control 2) → State),
      let y := chart.symm q
      x ≠ y → (∀ j, d j ∈ Γ.frames) → Joins d w x y →
      (∀ (k : ℕ) (r : Fin (k+1) → Frame M 2) (b : Fin (k+1) → Control 2),
        (∀ j, r j ∈ Γ.frames) → Joins r b x y → length w ≤ length b) →
      (∀ᶠ b in 𝓝 w, G b ∈ chart.target ∧ ∀ z, Joins d b x z ↔ z = chart.symm (G b)) →
      ∀ i : Fin (n+1), w i ≠ 0 → (∀ j, i < j → w j = 0) →
      4 ≤ Module.finrank ℝ (wordLayer (d i).X ((d i).chart y) 3) →
      let W := LinearMap.range (fderiv ℝ G w).toLinearMap
      Module.finrank ℝ W = 3 → u ∈ chartThirdLayer (d i) chart y →
      u ∉ W → v ∉ W ⊔ Submodule.span ℝ {u} →
      HasCostMultiplier length (fderiv ℝ G w) w := by
  let D (s : State) := pointedLengthValue Γ x (chart.symm s)
  filter_upwards [ae_box_on_adapted_plane Γ chart hc x, ae_compatible_value_repair Γ chart hc,
    ae_no_fixed_box D τ u v tu tv 3 (by decide),ae_no_fixed_box D τ u v tu tv 4 (by decide)]
    with q descent value three four
  intro hq n d w G y distinct hd path minimal graph i moving last growth W dim layer outside transverse
  obtain ⟨π,cok,hu,hv⟩ := quotient_axes W dim u v outside transverse
  by_contra absent
  obtain ⟨k,hk,A,B,c,cp,δ,dp,box⟩ :=
    descent hq d w G distinct hd path minimal graph absent i moving last growth π u v cok layer hu hv
  have reach : (attainableLengths Γ x y).Nonempty := ⟨length w,n,d,w,hd,path,rfl⟩
  obtain ⟨V,op,inside,cont⟩ := (value hq x reach).1
  have region : q ∈ continuityRegion D :=
    mem_iUnion.mpr ⟨V,mem_iUnion.mpr ⟨⟨op,cont⟩,inside⟩⟩
  rcases hk with rfl | rfl
  · exact three region A B c δ cp dp box
  · exact four region A B c δ cp dp box

theorem transverse_coordinate (W : Submodule ℝ State) (dim : Module.finrank ℝ W = 3)
    (u : State) (outside : u ∉ W) : ∃ j : Fin 5, Pi.single j 1 ∉ W ⊔ Submodule.span ℝ {u} := by
  by_contra! all
  let H := W ⊔ Submodule.span ℝ {u}
  have full : H = ⊤ := by
    apply Submodule.eq_top_iff'.mpr
    intro z
    have eq : ∑ j, z j • (Pi.single j 1 : State) = z := by ext i; simp [Pi.single_apply]
    rw [← eq]
    exact H.sum_mem fun j _ => H.smul_mem (z j) (all j)
  have nz : u ≠ 0 := by rintro rfl; exact outside W.zero_mem
  have size := W.finrank_sup_add_finrank_inf_eq (Submodule.span ℝ {u})
  rw [show W ⊔ Submodule.span ℝ {u} = ⊤ from full,finrank_top,Module.finrank_fin_fun,
    dim,finrank_span_singleton nz] at size
  omega

/-- The exceptional set is common to all paths and all five choices of
first coordinate axis. Only this first axis must belong to the terminal
third layer outside the endpoint range. The second axis is selected here. -/
abbrev FixedAxisMultiplierAt {M : Type*} [TopologicalSpace M] [ChartedSpace State M]
    (Γ : Geometry M 2) (chart : OpenPartialHomeomorph M State) (x : M) (q : State) : Prop :=
    ∀ {n : ℕ} (d : Fin (n+1) → Frame M 2)
      (w : Fin (n+1) → Control 2) (G : (Fin (n+1) → Control 2) → State),
      let y := chart.symm q
      x ≠ y → (∀ j, d j ∈ Γ.frames) → Joins d w x y →
      (∀ (k : ℕ) (r : Fin (k+1) → Frame M 2) (b : Fin (k+1) → Control 2),
        (∀ j, r j ∈ Γ.frames) → Joins r b x y → length w ≤ length b) →
      (∀ᶠ b in 𝓝 w, G b ∈ chart.target ∧ ∀ z, Joins d b x z ↔ z = chart.symm (G b)) →
      ∀ i : Fin (n+1), w i ≠ 0 → (∀ j, i < j → w j = 0) →
      4 ≤ Module.finrank ℝ (wordLayer (d i).X ((d i).chart y) 3) →
      let W := LinearMap.range (fderiv ℝ G w).toLinearMap
      Module.finrank ℝ W = 3 →
      (∃ l : Fin 5, Pi.single l 1 ∈ chartThirdLayer (d i) chart y ∧ Pi.single l 1 ∉ W) →
      HasCostMultiplier length (fderiv ℝ G w) w

theorem ae_multiplier_on_fixed_axes {M : Type*} [TopologicalSpace M] [ChartedSpace State M]
    [IsManifold 𝓘(ℝ,State) ∞ M] (Γ : Geometry M 2) (chart : OpenPartialHomeomorph M State)
    (hc : chart ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (x : M) :
    ∀ᵐ q : State, q ∈ chart.target → FixedAxisMultiplierAt Γ chart x q := by
  classical
  let P := {p : Fin 5 × Fin 5 // p.1 ≠ p.2}
  choose τ hu hv using fun p : P => split_coordinate_axes p.val.1 p.val.2 p.property
  filter_upwards [ae_all_iff.mpr (fun p : P => ae_multiplier_on_split Γ chart hc x (τ p) _ _ (hu p) (hv p))]
    with q every
  intro hq n d w G y distinct hd path minimal graph i moving last growth W dim axes
  obtain ⟨l,layer,outside⟩ := axes
  obtain ⟨j,transverse⟩ := transverse_coordinate W dim _ outside
  have ne : l ≠ j := by
    rintro rfl
    exact transverse ((show Submodule.span ℝ {Pi.single l 1} ≤ W ⊔ _ from le_sup_right)
      (Submodule.subset_span (Set.mem_singleton _)))
  exact every (⟨(l,j),ne⟩ : P) hq d w G distinct hd path minimal graph i moving last growth
    dim layer outside transverse

#print axioms ae_multiplier_on_fixed_axes

/-- One null exception in the measuring chart serves the entire countable
family of test charts, regardless of the path used to select a chart. -/
theorem ae_multiplier_in_countable_charts {M : Type*} [TopologicalSpace M] [ChartedSpace State M]
    [IsManifold 𝓘(ℝ,State) ∞ M] {I : Type*} [Countable I] (Γ : Geometry M 2) (x : M)
    (c : OpenPartialHomeomorph M State) (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M)
    (b : I → OpenPartialHomeomorph M State) (hb : ∀ i, b i ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) :
    ∀ᵐ q : State, q ∈ c.target → ∀ i, c.symm q ∈ (b i).source →
      FixedAxisMultiplierAt Γ (b i) x (b i (c.symm q)) := by
  filter_upwards [ae_all_iff.mpr (fun i => ae_chart_overlap (b i) c (hb i) hc _
    (ae_multiplier_on_fixed_axes Γ (b i) (hb i) x))] with q all
  exact fun hq i hi => all i ⟨hq,hi⟩

#print axioms ae_multiplier_in_countable_charts
end MinimizingSard.Five
