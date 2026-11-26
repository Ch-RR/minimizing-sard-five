import WordFlowBox
import OneCoordinateReturn

noncomputable section
open Set Filter MeasureTheory Metric IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five

private theorem quotient_line (W : Submodule ℝ State) (dim : Module.finrank ℝ W = 4) :
    ∃ (i : Fin 5) (p : State →L[ℝ] ℝ), LinearMap.ker p.toLinearMap = W ∧ p (Pi.single i 1) = 1 := by
  have ex : ∃ i : Fin 5, Pi.single i (1:ℝ) ∉ W := by
    by_contra! all
    have full : W = ⊤ := by
      apply Submodule.eq_top_iff'.mpr
      intro z
      have eq : ∑ j, z j • (Pi.single j 1 : State) = z := by ext i; simp [Pi.single_apply]
      rw [← eq]
      exact W.sum_mem fun j _ => W.smul_mem _ (all j)
    rw [full,finrank_top,Module.finrank_fin_fun] at dim
    omega
  obtain ⟨i,out⟩ := ex
  let u : State := Pi.single i 1
  let J := W.mkQ.comp ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight u)
  have inj : Function.Injective J := by
    apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro a ha
    have inside : a • u ∈ W := (Submodule.Quotient.mk_eq_zero W).mp ha
    change a = 0
    by_contra ne
    exact out ((W.smul_mem_iff ne).mp inside)
  have dimQ := W.finrank_quotient_add_finrank
  rw [dim,Module.finrank_fin_fun] at dimQ
  have dims : Module.finrank ℝ ℝ = Module.finrank ℝ (State ⧸ W) := by rw [Module.finrank_self]; omega
  let E := LinearEquiv.ofBijective J ⟨inj,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank dims).mp inj⟩
  let p := (E.symm.toLinearMap.comp W.mkQ).toContinuousLinearMap
  refine ⟨i,p,?_,?_⟩
  · ext z
    change E.symm (W.mkQ z) = 0 ↔ z ∈ W
    rw [map_eq_zero_iff E.symm E.symm.injective]
    exact Submodule.Quotient.mk_eq_zero W
  · change E.symm (W.mkQ u) = 1
    apply E.symm_apply_eq.mpr
    change W.mkQ u = W.mkQ ((1:ℝ) • u)
    simp

/-- Correct a kernel displacement so that all regular endpoint coordinates stay fixed. -/
theorem line_level_family {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
    (G : U → State) (w : U) (smooth : ContDiffAt ℝ 4 G w)
    (p : State →L[ℝ] ℝ) (u : State) (hu : p u = 1)
    (cok : LinearMap.ker p.toLinearMap = LinearMap.range (fderiv ℝ G w).toLinearMap) :
    let K := LinearMap.ker (fderiv ℝ G w).toLinearMap
    ∃ S : K → U, S 0 = 0 ∧ ContDiffAt ℝ 4 S 0 ∧ HasFDerivAt S K.subtypeL 0 ∧
      ∀ᶠ z in 𝓝 0, G (w+S z) = G w + p (G (w+S z)-G w) • u := by
  intro K
  let R := LinearMap.ker p.toLinearMap
  let J := ContinuousLinearMap.id ℝ State - p.smulRight u
  have land (z) : J z ∈ R := by
    change p (z - p z • u) = 0
    simp [hu]
  let P := J.codRestrict R land
  let D := fderiv ℝ G w
  have ann (z) : p (D z) = 0 := by
    change D z ∈ R
    rw [show R = _ from cok]
    exact ⟨z,rfl⟩
  have keep (z) : (P (D z)).val = D z := by
    change D z - p (D z) • u = D z
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
    have de : d - p d • u = 0 := congrArg Subtype.val zero
    dsimp only [d] at de
    linear_combination (norm := abel) de

/-- A linear saving along one corrected radial family suffices, including when
the original length is nondifferentiable at an idle segment. -/
theorem scalar_return_of_radial_saving {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (V : ℝ → ℝ) (hf : ContDiffAt ℝ 2 f 0) (f0 : f 0 = 0)
    (f1 : fderiv ℝ f 0 = 0) (h : E) (c : ℝ) (cp : 0 < c)
    (save : ∀ᶠ t : ℝ in 𝓝 0, 0 < t → V (f (t • h)) ≤ V 0-c*t) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∃ d r : ℝ, 0 < d ∧ 0 < r ∧
      ∀ s ∈ Ioo (0:ℝ) r, V (s^2*σ) ≤ V 0-d*s := by
  have ff : ∀ j ≤ 1, ∀ v : E, iteratedFDeriv ℝ j f 0 (fun _ => v) = 0 := by
    intro j hj v
    interval_cases j <;> simp [f0,f1]
  obtain ⟨δ,dp,est⟩ := Return.radial_profile f 1 h hf ff zero_lt_one
  have co : Continuous (fun t : ℝ => t • h) := continuous_id.smul continuous_const
  have near : Tendsto (fun t : ℝ => t • h) (𝓝 0) (𝓝 0) := by simpa using co.tendsto 0
  have reg : ∀ᶠ t : ℝ in 𝓝 0, ContDiffAt ℝ 2 f (t • h) := near (hf.eventually (by decide))
  obtain ⟨R,rp,nb⟩ := Metric.mem_nhds_iff.mp (reg.and save)
  let T := min R δ / 2
  have pos := lt_min rp dp
  have small (t : ℝ) (ht : t ∈ Icc 0 T) := lt_min_iff.mp (ht.2.trans_lt (half_lt_self pos))
  have valid (t : ℝ) (ht : t ∈ Icc 0 T) := nb (show t ∈ ball (0:ℝ) R by
    simpa [mem_ball,Real.dist_eq,abs_of_nonneg ht.1] using (small t ht).1)
  apply Return.interval_return (fun t => f (t • h)) V T (|Return.coeff f 2 0 h|+1) c (half_pos pos) (by positivity) cp
    (fun t ht => (ContinuousAt.comp (f := fun s : ℝ => s • h) (valid t ht).1.continuousAt
      (co.continuousAt (x := t))).continuousWithinAt) (by simpa using f0)
  · intro t ht
    have e := est t ht.1 (small t ⟨ht.1.le,ht.2⟩).2 h (by simpa using dp)
    have tri := abs_sub_le (f (t • h)/t^2) (Return.coeff f 2 0 h) 0
    simp only [sub_zero] at tri
    change |f (t • h)/t^2-Return.coeff f 2 0 h| < 1 at e
    apply (div_le_iff₀ (sq_pos_of_pos ht.1)).mp
    rw [abs_div,abs_of_pos (sq_pos_of_pos ht.1)] at tri
    linarith
  · intro t ht
    exact (valid t ⟨ht.1.le,ht.2⟩).2 ht.1

#print axioms line_level_family
#print axioms scalar_return_of_radial_saving

/-- The pointed value only needs to be continuous on a neighborhood of the
center, which can vary from point to point. -/
theorem ae_no_local_quadratic_ray (D : State → ℝ) (u : State) :
    ∀ᵐ q : State, q ∈ continuityRegion D → ∀ c r : ℝ, 0 < c → 0 < r →
      ¬ (∀ t ∈ Ioo (0:ℝ) r, D (q+t^2 • u) ≤ D q-c*t) := by
  obtain ⟨ho,hc⟩ := continuityRegion_spec D
  apply localize_value D _ _ ho hc
  intro V cv
  have null := Slicing.quadratic_ray_descent_null V cv (fun _ => u)
  have good : ∀ᵐ q : State, q ∉ {y | ∃ (i : ℕ) (c r : ℝ), 0 < c ∧ 0 < r ∧
      ∀ t ∈ Ioo (0:ℝ) r, V (y+t^2 • (fun _ : ℕ => u) i) ≤ V y-c*t} :=
    ae_iff.mpr (by simpa using null)
  filter_upwards [good] with q hq
  intro eq c r cp rp save
  have near : Tendsto (fun t : ℝ => q+t^2 • u) (𝓝 0) (𝓝 q) := by
    have co : Continuous (fun t : ℝ => q+t^2 • u) := by fun_prop
    simpa using co.tendsto 0
  have same : ∀ᶠ t : ℝ in 𝓝 0, V (q+t^2 • u) = D (q+t^2 • u) := near eq
  obtain ⟨δ,dp,nb⟩ := Metric.mem_nhds_iff.mp same
  apply hq
  refine ⟨0,c,min r δ,cp,lt_min rp dp,?_⟩
  intro t ht
  have bound := lt_min_iff.mp ht.2
  have eqt := nb (show t ∈ ball (0:ℝ) δ by simpa [mem_ball,Real.dist_eq,abs_of_pos ht.1] using bound.2)
  change V (q+t^2 • u) ≤ V q-c*t
  rw [show V (q+t^2 • u) = D (q+t^2 • u) from eqt,eq.self_of_nhds]
  exact save t ⟨ht.1,bound.1⟩

/-- A minimizing endpoint graph of any horizontal rank with one-dimensional
cokernel and no length multiplier yields a quadratic line of cheaper endpoints. -/
theorem corank_one_descent {m n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace State M]
    (Γ : Geometry M m) (x y : M) (chart : OpenPartialHomeomorph M State)
    (d : Fin (n+1) → Frame M m) (w : Fin (n+1) → Control m)
    (G : (Fin (n+1) → Control m) → State) (smooth : ContDiffAt ℝ 4 G w)
    (hd : ∀ i, d i ∈ Γ.frames) (path : Joins d w x y)
    (minimal : ∀ (k : ℕ) (a : Fin (k+1) → Frame M m) (b : Fin (k+1) → Control m),
      (∀ i, a i ∈ Γ.frames) → Joins a b x y → length w ≤ length b)
    (graph : ∀ᶠ b in 𝓝 w, ∀ z, Joins d b x z ↔ z = chart.symm (G b))
    (absent : ¬ HasCostMultiplier length (fderiv ℝ G w) w)
    (rank : Module.finrank ℝ (LinearMap.range (fderiv ℝ G w).toLinearMap) = 4) :
    let D := fun s => pointedLengthValue Γ x (chart.symm s)
    ∃ (i : Fin 5) (σ : ℝ), (σ = 1 ∨ σ = -1) ∧ ∃ c r : ℝ, 0 < c ∧ 0 < r ∧
      ∀ s ∈ Ioo (0:ℝ) r, D (G w + s^2 • (σ • (Pi.single i 1 : State))) ≤ D (G w)-c*s := by
  intro D
  obtain ⟨i,p,cok,unit⟩ := quotient_line _ rank
  let u : State := Pi.single i 1
  let K := LinearMap.ker (fderiv ℝ G w).toLinearMap
  obtain ⟨S,s0,cs,ds,level⟩ := line_level_family G w smooth p u unit cok
  obtain ⟨h,kh,down⟩ := (no_length_multiplier_iff_shorter _ _).mp absent
  let k : K := ⟨h,kh⟩
  obtain ⟨c,cp,cone⟩ := length_cone_on_radial_chart w S K.subtypeL s0 ds k down
  let A (z : K) := w+S z
  have az : A 0 = w := by simp [A,s0]
  have ca : ContDiffAt ℝ 2 A 0 := contDiffAt_const.add (cs.of_le (by decide))
  have da : HasFDerivAt A K.subtypeL 0 := ds.const_add w
  have cg : ContDiffAt ℝ 2 G (A 0) := az.symm ▸ smooth.of_le (by decide)
  let f (z : K) := p (G (A z)-G w)
  have cf : ContDiffAt ℝ 2 f 0 := p.contDiff.contDiffAt.comp 0 ((cg.comp 0 ca).sub contDiffAt_const)
  have fz : f 0 = 0 := by simp [f,az]
  have df := p.hasFDerivAt.comp 0 (((cg.differentiableAt (by decide)).hasFDerivAt.comp 0 da).sub_const (G w))
  have first : fderiv ℝ f 0 = 0 := by
    rw [show fderiv ℝ f 0 = _ from df.fderiv]
    ext z
    change p (fderiv ℝ G (A 0) z.val) = 0
    rw [az,show fderiv ℝ G w z.val = 0 from z.property,map_zero]
  have rad : Tendsto (fun t : ℝ => t • k) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_id.smul (continuous_const (y := k))).tendsto (0:ℝ)
  have atA : Tendsto A (𝓝 0) (𝓝 w) := az ▸ da.continuousAt.tendsto
  have pair : Tendsto (fun t : ℝ => (t,k)) (𝓝 0) (𝓝 (0,k)) := continuousAt_id.prodMk continuousAt_const
  have y0 : y = chart.symm (G w) := (graph.self_of_nhds y).mp path
  let V (s : ℝ) := D (G w+s • u)
  have save : ∀ᶠ t : ℝ in 𝓝 0, 0 < t → V (f (t • k)) ≤ V 0-c*t := by
    filter_upwards [pair cone,rad level,(atA.comp rad) (pointedLengthValue_comparison hd path minimal chart G graph)] with t drop line comp
    intro tp
    have eq : G (A (t • k)) = G w+f (t • k) • u := line
    have comp' : D (G (A (t • k))) - D (G w) ≤ length (A (t • k)) - length w := by simpa only [D,← y0] using comp
    have b := drop tp
    change length (A (t • k)) ≤ length w-c*t at b
    simp only [V,zero_smul,add_zero,← eq]
    linarith
  obtain ⟨σ,sign,b,r,bp,rp,ray⟩ := scalar_return_of_radial_saving f V cf fz first k c cp save
  refine ⟨i,σ,sign,b,r,bp,rp,fun s hs => ?_⟩
  simpa only [V,mul_smul,zero_smul,add_zero,u] using ray s hs

#print axioms ae_no_local_quadratic_ray
#print axioms corank_one_descent


/-- At almost every endpoint of the rank-two geometry, every minimizing
control whose derivative has rank four admits a supporting length covector. -/
theorem ae_corank_one_of_germs {m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace State M]
    [IsManifold 𝓘(ℝ,State) ∞ M] (Γ : Geometry M m) (x : M)
    (chart : OpenPartialHomeomorph M State) (hc : chart ∈ maximalAtlas 𝓘(ℝ,State) ∞ M)
    (vals : ∀ᵐ q : State, q ∈ chart.target → (attainableLengths Γ x (chart.symm q)).Nonempty →
      ∃ V : Set State, IsOpen V ∧ q ∈ V ∧ ContinuousOn (fun s => pointedLengthValue Γ x (chart.symm s)) V)
    (localGraph : ∀ (e : Frame M m) (v : Control m) (a b : M), Segment e v a b → HasSmoothSegmentGraph e 4 (e.chart a,v)) :
    ∀ᵐ q : State, q ∈ chart.target → ∀ {n : ℕ} (d : Fin (n+1) → Frame M m)
      (w : Fin (n+1) → Control m) (G : (Fin (n+1) → Control m) → State),
      let y := chart.symm q
      (∀ i, d i ∈ Γ.frames) → Joins d w x y →
      (∀ (k : ℕ) (a : Fin (k+1) → Frame M m) (b : Fin (k+1) → Control m),
        (∀ i, a i ∈ Γ.frames) → Joins a b x y → length w ≤ length b) →
      (∀ᶠ b in 𝓝 w, G b ∈ chart.target ∧ ∀ z, Joins d b x z ↔ z = chart.symm (G b)) →
      Module.finrank ℝ (LinearMap.range (fderiv ℝ G w).toLinearMap) = 4 →
      HasCostMultiplier length (fderiv ℝ G w) w := by
  let D (s : State) := pointedLengthValue Γ x (chart.symm s)
  let u (i : Fin 5) : State := Pi.single i 1
  filter_upwards [vals,
    ae_all_iff.mpr fun i : Fin 5 => ae_no_local_quadratic_ray D (u i),
    ae_all_iff.mpr fun i : Fin 5 => ae_no_local_quadratic_ray D (-u i)] with q value plus minus
  intro hq n d w G y hd path minimal graph rank
  have hy : y ∈ chart.source := chart.map_target hq
  have atw := graph.self_of_nhds
  have center : q = G w := chart.symm.injOn hq atw.1 ((atw.2 _).mp path)
  have reach : (attainableLengths Γ x y).Nonempty := ⟨length w,n,d,w,hd,path,rfl⟩
  obtain ⟨V,op,inside,cont⟩ := value hq reach
  have region : q ∈ continuityRegion D := mem_iUnion.mpr ⟨V,mem_iUnion.mpr ⟨⟨op,cont⟩,inside⟩⟩
  obtain ⟨G₀,_,sm,gr,_⟩ := path_endpoint_of_segment_graphs d w x y path chart hc hy 4 (by decide) localGraph
  have smooth : ContDiffAt ℝ 4 G w := sm.congr_of_eventuallyEq (by
    filter_upwards [graph,gr] with b gb rb
    exact (chart.right_inv gb.1).symm.trans ((congrArg chart ((rb.2 _).mp ((gb.2 _).mpr rfl))).trans (chart.right_inv rb.1)))
  by_contra absent
  obtain ⟨i,σ,sign,c,r,cp,rp,ray⟩ := corank_one_descent Γ x y chart d w G smooth hd path minimal
    (graph.mono fun _ h => h.2) absent rank
  rcases sign with rfl | rfl
  · apply plus i region c r cp rp
    simpa only [D,u,one_smul,← center] using ray
  · apply minus i region c r cp rp
    simpa only [D,u,neg_one_smul,← center] using ray

theorem ae_corank_one_length_multiplier {M : Type*} [TopologicalSpace M] [ChartedSpace State M]
    [IsManifold 𝓘(ℝ,State) ∞ M] (Γ : Geometry M 2) (x : M)
    (chart : OpenPartialHomeomorph M State) (hc : chart ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) :
    ∀ᵐ q : State, q ∈ chart.target → ∀ {n : ℕ} (d : Fin (n+1) → Frame M 2)
      (w : Fin (n+1) → Control 2) (G : (Fin (n+1) → Control 2) → State),
      let y := chart.symm q
      (∀ i, d i ∈ Γ.frames) → Joins d w x y →
      (∀ (k : ℕ) (a : Fin (k+1) → Frame M 2) (b : Fin (k+1) → Control 2),
        (∀ i, a i ∈ Γ.frames) → Joins a b x y → length w ≤ length b) →
      (∀ᶠ b in 𝓝 w, G b ∈ chart.target ∧ ∀ z, Joins d b x z ↔ z = chart.symm (G b)) →
      Module.finrank ℝ (LinearMap.range (fderiv ℝ G w).toLinearMap) = 4 →
      HasCostMultiplier length (fderiv ℝ G w) w :=
  ae_corank_one_of_germs Γ x chart hc ((ae_compatible_value_repair Γ chart hc).mono
    (fun _ h hq reach => (h hq x reach).1)) (fun e v a b seg => arbitrary_segment_graph e v a b seg 4 (by decide))

#print axioms ae_corank_one_length_multiplier

end MinimizingSard.Five
