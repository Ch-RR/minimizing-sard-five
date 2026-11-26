import LengthDescentCone
import EndpointLevelChart
import WholeHessianFlag
import Mathlib.MeasureTheory.Measure.Haar.Unique

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff

namespace MinimizingSard.Five
open Reduced

variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] [IsManifold 𝓘(ℝ,State) ∞ M]

set_option maxHeartbeats 1600000 in
/-- On a fixed product chart with a continuous representative of the pointed value,
true length minimization excludes a regular two-row polar almost everywhere on
the branch without a first-order length multiplier. The three observable coordinates
must be regular and the two quotient rows are normalized on their vertical plane. -/
private theorem ae_minimizing_length_normalized (Γ : Geometry M 2) (x : M) (chart : OpenPartialHomeomorph M State)
    (hc : chart ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (τ : State ≃L[ℝ] Ambient)
    (V : Ambient → ℝ) (hV : Continuous V) :
    ∀ᵐ p : Ambient, ∀ (n : ℕ) (e : Fin (n+1) → Frame M 2) (w : Fin (n+1) → Control 2)
      (y : M) (G : (Fin (n+1) → Control 2) → State),
      y ∈ chart.source → (∀ i, e i ∈ Γ.frames) → Joins e w x y →
      (∀ (k : ℕ) (d : Fin (k+1) → Frame M 2) (v : Fin (k+1) → Control 2),
        (∀ i, d i ∈ Γ.frames) → Joins d v x y → length w ≤ length v) →
      (∀ᶠ v in 𝓝 w, G v ∈ chart.target ∧ ∀ z, Joins e v x z ↔ z = chart.symm (G v)) →
      p = τ (G w) → (∀ᶠ z in 𝓝 p, V z = pointedLengthValue Γ x (chart.symm (τ.symm z))) →
      Function.Surjective (fun v => (τ (fderiv ℝ G w v)).1) →
      ∀ π : State →L[ℝ] ℝ × ℝ, (∀ v, π (fderiv ℝ G w v) = 0) →
      (∀ z, (τ z).1 = 0 → (τ z).2 = ![(π z).1,(π z).2]) →
      ¬ HasCostMultiplier length (fderiv ℝ G w) w →
      ∀ h : LinearMap.ker (fderiv ℝ G w).toLinearMap,
        ¬ Function.Surjective (fun l : LinearMap.ker (fderiv ℝ G w).toLinearMap =>
          π (fderiv ℝ (fderiv ℝ G) w h l)) := by
  filter_upwards [ae_no_regular_polar_of_cones V hV] with p except
  intro n e w y G hy he path hmin graph center rep onto π ann vertical absent h sur
  let U := Fin (n+1) → Control 2
  obtain ⟨G₀,_,hs,eg,_⟩ := path_endpoint_and_singularity e w x y path chart hc hy 4 (by decide)
  have smooth : ContDiffAt ℝ 4 G w := hs.congr_of_eventuallyEq (by
    filter_upwards [graph,eg] with v gv ev
    have eq := (ev.2 _).mp ((gv.2 _).mpr rfl)
    exact (chart.right_inv gv.1).symm.trans ((congrArg chart eq).trans (chart.right_inv ev.1)))
  let obs := (ContinuousLinearMap.fst ℝ (Fin 3 → ℝ) Plane).comp τ.toContinuousLinearMap
  let F (z : U) := obs (G (w+z))
  have tr : HasFDerivAt (fun z : U => w+z) (ContinuousLinearMap.id ℝ U) 0 := by
    exact (hasFDerivAt_id (𝕜 := ℝ) (0:U)).const_add w
  have dG : HasFDerivAt G (fderiv ℝ G w) (w+(0:U)) := by
    simpa using (smooth.differentiableAt (by decide)).hasFDerivAt
  have df : fderiv ℝ F 0 = obs.comp (fderiv ℝ G w) := (obs.hasFDerivAt.comp 0 (dG.comp 0 tr)).fderiv
  have cf : ContDiffAt ℝ 4 F 0 := obs.contDiff.contDiffAt.comp 0
    ((show ContDiffAt ℝ 4 G (w+(0:U)) by simpa using smooth).comp 0 (contDiffAt_const.add contDiffAt_id))
  let K := LinearMap.ker (fderiv ℝ F 0).toLinearMap
  obtain ⟨S,s0,cs,ds,level⟩ := level_chart F cf (by rw [df]; exact onto)
  let A (z : K) := w+S z
  have a0 : A 0 = w := by simp [A,s0]
  have da : HasFDerivAt A K.subtypeL 0 := ds.const_add w
  have ca : ContDiffAt ℝ 2 A 0 := contDiffAt_const.add (cs.of_le (by decide))
  let f (q : State →L[ℝ] ℝ) := (fun z => q (z-G w)) ∘ (G ∘ A)
  have smoothAtA : ContDiffAt ℝ 2 G (A 0) := a0.symm ▸ smooth.of_le (by decide)
  have cq (q : State →L[ℝ] ℝ) : ContDiff ℝ 2 (fun z => q (z-G w)) :=
    q.contDiff.comp (contDiff_id.sub contDiff_const)
  have der (q : State →L[ℝ] ℝ) (z : State) : fderiv ℝ (fun z => q (z-G w)) z = q :=
    (q.hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const (G w))).fderiv
  have cfq (q : State →L[ℝ] ℝ) : ContDiffAt ℝ 2 (f q) 0 :=
    (cq q).contDiffAt.comp 0 (smoothAtA.comp 0 ca)
  have zeroq (q : State →L[ℝ] ℝ) : f q 0 = 0 := by simp [f,a0]
  have first (q : State →L[ℝ] ℝ) (van : ∀ v, q (fderiv ℝ G w v) = 0) :
      fderiv ℝ (f q) 0 = 0 := by
    dsimp only [f]
    rw [fderiv_comp 0 ((cq q).differentiable (by decide) _) ((smoothAtA.comp 0 ca).differentiableAt (by decide)),
      fderiv_comp 0 (smoothAtA.differentiableAt (by decide)) da.differentiableAt,der,da.fderiv,a0]
    ext z
    exact van z
  have incl (z : U) (hz : fderiv ℝ G w z = 0) : z ∈ K := by
    change fderiv ℝ F 0 z = 0
    rw [df,ContinuousLinearMap.comp_apply,hz,map_zero]
  have second (q : State →L[ℝ] ℝ) (van : ∀ v, q (fderiv ℝ G w v) = 0)
      (v l : K) (hv : fderiv ℝ G w v = 0) :
      fderiv ℝ (fderiv ℝ (f q)) 0 v l = q (fderiv ℝ (fderiv ℝ G) w v l) := by
    have eq := Transport.intrinsic_second_variation A G (fun z => q (z-G w)) 0 v l
      (ContinuousLinearMap.id ℝ ℝ) ca smoothAtA (cq q).contDiffAt
      (by simpa only [a0,da.fderiv,Submodule.subtypeL_apply] using hv)
      (by simpa only [der,a0,ContinuousLinearMap.id_apply] using van)
    simpa only [f,a0,da.fderiv,Submodule.subtypeL_apply,der,ContinuousLinearMap.id_apply] using eq
  let q₁ := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp π
  let q₂ := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp π
  have v₁ (v : U) : q₁ (fderiv ℝ G w v) = 0 := congrArg Prod.fst (ann v)
  have v₂ (v : U) : q₂ (fderiv ℝ G w v) = 0 := congrArg Prod.snd (ann v)
  let O : Set K := {z | length (w+(z:U)) < length w}
  have op : IsOpen O := isOpen_lt (continuous_control_length.comp
    (continuous_const.add K.subtypeL.continuous)) continuous_const
  obtain ⟨d,dh,down⟩ := (no_length_multiplier_iff_shorter _ _).mp absent
  have ne : O.Nonempty := ⟨⟨d,incl d dh⟩,down⟩
  apply except (f q₁) (f q₂) (cfq q₁) (cfq q₂) (zeroq _) (first _ v₁) (zeroq _) (first _ v₂) O op ne
    _ (⟨h.val,incl h.val h.property⟩ : K)
  · intro r
    obtain ⟨l,hl⟩ := sur r
    let hk : K := ⟨h.val,incl h.val h.property⟩
    let lk : K := ⟨l.val,incl l.val l.property⟩
    exact ⟨lk,(congrArg₂ Prod.mk
      (second _ v₁ hk lk h.property) (second _ v₂ hk lk h.property)).trans hl⟩
  · intro k hk B
    obtain ⟨c,cp,cone⟩ := length_cone_on_level_chart w S K.subtypeL s0 ds k hk B
    refine ⟨c,cp,?_⟩
    have base : chart.symm (G w) = y := ((graph.self_of_nhds.2 _).mp path).symm
    have baseV : localValue V p 0 = pointedLengthValue Γ x y := by
      have z0 : (![0,0] : Plane) = 0 := by ext i; fin_cases i <;> rfl
      simpa [localValue,z0,center,base] using rep.self_of_nhds
    have localComp := pointedLengthValue_comparison he path hmin chart G (graph.mono fun _ hv => hv.2)
    have toW : Tendsto A (𝓝 0) (𝓝 w) := a0 ▸ da.continuousAt.tendsto
    have toP : Tendsto (fun z => τ (G (A z))) (𝓝 0) (𝓝 p) :=
      center ▸ τ.continuous.continuousAt.tendsto.comp (smooth.continuousAt.tendsto.comp toW)
    have estimate : ∀ᶠ z in 𝓝 (0:K), localValue V p (f q₁ z,f q₂ z) - localValue V p 0 ≤ length (A z)-length w := by
      filter_upwards [level,toP rep,toW localComp] with z hz val comp
      have same : (τ (G (A z))).1 = (τ (G w)).1 := by simpa [F,A,obs] using hz
      have vert := vertical (G (A z)-G w) (by simp [map_sub,same])
      have dest : (p.1,p.2 + ![f q₁ z,f q₂ z]) = τ (G (A z)) := by
        apply Prod.ext
        · simpa only [center] using same.symm
        · change p.2 + ![(π (G (A z)-G w)).1,(π (G (A z)-G w)).2] = _
          rw [← vert,center,map_sub,Prod.snd_sub,add_sub_cancel]
      change V (p.1,p.2 + ![f q₁ z,f q₂ z]) - _ ≤ _
      rw [dest,baseV]
      change V (τ (G (A z))) = _ at val
      simpa only [val,ContinuousLinearEquiv.symm_apply_apply] using comp
    have lim : Tendsto (fun b : ℝ × (ℝ × ℝ) => b.1 • (k+B b.2)) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_fst.smul (continuous_const.add (B.continuous.comp continuous_snd))).tendsto
        (0 : ℝ × (ℝ × ℝ))
    filter_upwards [lim estimate,cone] with b ec ed
    intro ht
    specialize ed ht
    change localValue V p _ - localValue V p 0 ≤ length (w+S (b.1 • (k+B b.2)))-length w at ec
    linarith

/-- In the fixed three-plus-two chart the restriction of any cokernel quotient to
the vertical two-plane is invertible. This normalizes the rows without changing the slice. -/
private theorem normalize_quotient {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (τ : State ≃L[ℝ] Ambient) (A : U →L[ℝ] State)
    (onto : Function.Surjective (fun v => (τ (A v)).1)) (π : State →L[ℝ] ℝ × ℝ)
    (sur : Function.Surjective π) (ann : ∀ v, π (A v) = 0) :
    ∃ T : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ), ∀ z, (τ z).1 = 0 →
      (τ z).2 = ![(T (π z)).1,(T (π z)).2] := by
  let pair := ContinuousLinearEquiv.finTwoArrow ℝ ℝ
  let j := τ.symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.inr ℝ (Fin 3 → ℝ) Plane).comp pair.symm.toContinuousLinearMap)
  let B := π.comp j
  have lift (z : State) (hz : (τ z).1 = 0) : j (pair (τ z).2) = z := by
    apply τ.injective
    change τ (τ.symm (0,pair.symm (pair (τ z).2))) = τ z
    rw [τ.apply_symm_apply,pair.symm_apply_apply]
    exact Prod.ext hz.symm rfl
  have surB : Function.Surjective B := by
    intro r
    obtain ⟨z,hz⟩ := sur r
    obtain ⟨v,hv⟩ := onto (τ z).1
    change (τ (A v)).1 = (τ z).1 at hv
    have zero : (τ (z-A v)).1 = 0 := by rw [map_sub,Prod.fst_sub,hv,sub_self]
    exact ⟨pair (τ (z-A v)).2,by change π (j _) = r; rw [lift _ zero,map_sub,ann,sub_zero,hz]⟩
  let T := ContinuousLinearEquiv.ofBijective B
    (LinearMap.ker_eq_bot.mpr ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := B.toLinearMap) rfl).mpr surB)) (LinearMap.range_eq_top.mpr surB)
  refine ⟨T.symm, fun z hz => ?_⟩
  have eq : T (pair (τ z).2) = π z := congrArg π (lift z hz)
  rw [← eq,T.symm_apply_apply]
  ext i
  fin_cases i <;> rfl

def MinimizingPolarAt (Γ : Geometry M 2) (x : M) (chart : OpenPartialHomeomorph M State)
    (τ : State ≃L[ℝ] Ambient) (p : Ambient) : Prop :=
  ∀ (n : ℕ) (e : Fin (n+1) → Frame M 2) (w : Fin (n+1) → Control 2)
      (y : M) (G : (Fin (n+1) → Control 2) → State),
      y ∈ chart.source → (∀ i, e i ∈ Γ.frames) → Joins e w x y →
      (∀ (k : ℕ) (d : Fin (k+1) → Frame M 2) (v : Fin (k+1) → Control 2),
        (∀ i, d i ∈ Γ.frames) → Joins d v x y → length w ≤ length v) →
      (∀ᶠ v in 𝓝 w, G v ∈ chart.target ∧ ∀ z, Joins e v x z ↔ z = chart.symm (G v)) →
      p = τ (G w) →
      Function.Surjective (fun v => (τ (fderiv ℝ G w v)).1) →
      ∀ π : State →L[ℝ] ℝ × ℝ, Function.Surjective π →
      LinearMap.ker π.toLinearMap = LinearMap.range (fderiv ℝ G w).toLinearMap →
      ¬ HasCostMultiplier length (fderiv ℝ G w) w →
      let K := LinearMap.ker (fderiv ℝ G w).toLinearMap
      let L := Submodule.span ℝ (range (fun z : K × K => π (fderiv ℝ (fderiv ℝ G) w z.1 z.2)))
      (∀ h : K, ¬ Function.Surjective (fun l : K => π (fderiv ℝ (fderiv ℝ G) w h l))) ∧
      (x ≠ y → ∀ i : Fin (n+1), w i ≠ 0 → (∀ j, i < j → w j = 0) →
        4 ≤ Module.finrank ℝ (wordLayer (e i).X ((e i).chart y) 3) →
        Module.finrank ℝ L = 1 ∧ chartThirdLayer (e i) chart y = L.comap π.toLinearMap ∧
          Module.finrank ℝ (chartThirdLayer (e i) chart y) = 4)

/-- Almost-everywhere non-surjectivity for every quotient basis, followed by the
four-dimensional third-layer conclusion for the last active frame when its growth is at least four. -/
theorem ae_minimizing_length_polar (Γ : Geometry M 2) (x : M) (chart : OpenPartialHomeomorph M State)
    (hc : chart ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (τ : State ≃L[ℝ] Ambient)
    (V : Ambient → ℝ) (hV : Continuous V) :
    ∀ᵐ p : Ambient, (∀ᶠ z in 𝓝 p, V z = pointedLengthValue Γ x (chart.symm (τ.symm z))) →
      MinimizingPolarAt Γ x chart τ p := by
  filter_upwards [ae_minimizing_length_normalized Γ x chart hc τ V hV] with p good
  intro rep n e w y G hy he path hmin graph center onto π sur cok absent
  have ann (v) : π (fderiv ℝ G w v) = 0 := by
    change fderiv ℝ G w v ∈ LinearMap.ker π.toLinearMap
    rw [cok]
    exact ⟨v,rfl⟩
  obtain ⟨T,vert⟩ := normalize_quotient τ _ onto π sur ann
  have noReg := good n e w y G hy he path hmin graph center rep onto
    (T.toContinuousLinearMap.comp π) (fun v => by simp [ann]) vert absent
  have unscaled (h : LinearMap.ker (fderiv ℝ G w).toLinearMap) :
      ¬ Function.Surjective (fun l : LinearMap.ker (fderiv ℝ G w).toLinearMap =>
        π (fderiv ℝ (fderiv ℝ G) w h l)) :=
    fun onto' => noReg h (T.surjective.comp onto')
  refine ⟨unscaled,?_⟩
  intro distinct i act last growth
  obtain ⟨one,layer,four,_⟩ := whole_hessian_flag e w distinct path chart hc hy G graph
    i act last π sur cok growth unscaled
  exact ⟨one,layer,four⟩

#print axioms ae_minimizing_length_polar

/-- Countably many extensions suffice on an arbitrary open chart region. The
exceptional sets can depend on the extensions, but never on the minimizing paths. -/
theorem localize_value {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SecondCountableTopology E] [MeasureSpace E] (D : E → ℝ) (P : E → Prop) (Ω : Set E)
    (ho : IsOpen Ω) (hc : ContinuousOn D Ω)
    (fromExtension : ∀ V : E → ℝ, Continuous V →
      ∀ᵐ p : E, (V =ᶠ[𝓝 p] D) → P p) :
    ∀ᵐ p : E, p ∈ Ω → P p := by
  classical
  have cover (p : Ω) : ∃ r > 0, Metric.closedBall p.val r ⊆ Ω :=
    Metric.nhds_basis_closedBall.mem_iff.mp (ho.mem_nhds p.property)
  choose r rp inside using cover
  have extension (p : Ω) : ∃ V : C(E,ℝ), ∀ z ∈ Metric.closedBall p.val (r p), V z = D z := by
    let R (z : E) := p.val + (r p / max (r p) ‖z-p.val‖) • (z-p.val)
    have den (z : E) : 0 < max (r p) ‖z-p.val‖ := (rp p).trans_le (le_max_left _ _)
    have cr : Continuous R := continuous_const.add ((continuous_const.div
      (continuous_const.max (continuous_id.sub continuous_const).norm) (fun z => (den z).ne')).smul
        (continuous_id.sub continuous_const))
    have inBall (z) : R z ∈ Metric.closedBall p.val (r p) := by
      rw [Metric.mem_closedBall,dist_eq_norm]
      simp only [R,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos (rp p) (den z))]
      calc
        _ ≤ (r p / max (r p) ‖z-p.val‖) * max (r p) ‖z-p.val‖ :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) (div_pos (rp p) (den z)).le
        _ = _ := div_mul_cancel₀ _ (den z).ne'
    refine ⟨⟨D ∘ R,hc.comp_continuous cr (fun z => inside p (inBall z))⟩,?_⟩
    intro z hz
    change D (R z) = D z
    have hz' : ‖z-p.val‖ ≤ r p := by simpa [Metric.mem_closedBall,dist_eq_norm] using hz
    simp [R,max_eq_left hz',(rp p).ne']
  choose V same using extension
  have lind : IsLindelof Ω := IsLindelof.of_coe
  obtain ⟨T,count,cov⟩ := lind.elim_countable_subcover (fun p : Ω => Metric.ball p.val (r p))
    (fun _ => Metric.isOpen_ball) (fun z hz => mem_iUnion.mpr ⟨⟨z,hz⟩,Metric.mem_ball_self (rp _)⟩)
  letI : Countable T := count.to_subtype
  filter_upwards [ae_all_iff.mpr (fun p : T => fromExtension (V p.val) (V p.val).continuous)] with z good
  intro hz
  obtain ⟨p,hp⟩ := mem_iUnion.mp (cov hz)
  obtain ⟨ht,hz⟩ := mem_iUnion.mp hp
  apply good ⟨p,ht⟩
  filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy using same p y (Metric.ball_subset_closedBall hy)

/-- Points having a neighborhood on which a scalar function is continuous. -/
def continuityRegion (D : State → ℝ) : Set State :=
  ⋃ U ∈ {U : Set State | IsOpen U ∧ ContinuousOn D U}, U

theorem continuityRegion_spec (D : State → ℝ) :
    IsOpen (continuityRegion D) ∧ ContinuousOn D (continuityRegion D) := by
  refine ⟨isOpen_iUnion (fun U => isOpen_iUnion fun h => h.1),?_⟩
  intro z hz
  obtain ⟨U,hU⟩ := mem_iUnion.mp hz
  obtain ⟨h,mem⟩ := mem_iUnion.mp hU
  exact ((h.2 z mem).continuousAt (h.1.mem_nhds mem)).continuousWithinAt

/-- Local continuity near the tested point suffices. The almost-everywhere statement
uses Lebesgue measure in the original five state coordinates. -/
theorem ae_chart_length_polar (Γ : Geometry M 2) (x : M) (chart : OpenPartialHomeomorph M State)
    (hc : chart ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (τ : State ≃L[ℝ] Ambient) :
    ∀ᵐ z : State, z ∈ continuityRegion (fun s => pointedLengthValue Γ x (chart.symm s)) →
      MinimizingPolarAt Γ x chart τ (τ z) := by
  let D (s : State) := pointedLengthValue Γ x (chart.symm s)
  let Ω := τ.symm ⁻¹' continuityRegion D
  obtain ⟨regionOpen,hd⟩ := continuityRegion_spec D
  have ho : IsOpen Ω := regionOpen.preimage τ.symm.continuous
  have cont : ContinuousOn (fun z => pointedLengthValue Γ x (chart.symm (τ.symm z))) Ω :=
    hd.comp τ.symm.continuous.continuousOn (fun _ h => h)
  have almost := localize_value _ _ Ω ho cont (ae_minimizing_length_polar Γ x chart hc τ)
  letI : Measure.IsAddHaarMeasure (volume : Measure Ambient) := by
    rw [Measure.volume_eq_prod]; infer_instance
  letI : Measure.IsAddHaarMeasure (volume.map τ) := τ.isAddHaarMeasure_map volume
  have qm : Measure.QuasiMeasurePreserving τ volume volume :=
    ⟨τ.continuous.measurable, Measure.absolutelyContinuous_isAddHaarMeasure _ _⟩
  filter_upwards [qm.tendsto_ae almost] with z hz
  exact fun mem => hz (by change τ.symm (τ z) ∈ continuityRegion D; simpa using mem)

#print axioms ae_chart_length_polar

/-- In fixed product coordinates local continuity of a state value suffices
to exclude mixed-order descent boxes based at almost every center. -/
theorem ae_no_fixed_box (D : State → ℝ) (τ : State ≃L[ℝ] Ambient) (u v : State)
    (hu : τ u = (0,![1,0])) (hv : τ v = (0,![0,1])) (k : ℕ) (hk : 2 ≤ k) :
    ∀ᵐ q : State, q ∈ continuityRegion D → ∀ A B c δ : ℝ, 0 < c → 0 < δ →
      ¬ (∀ t : ℝ, 0 < t → t < δ → ∀ a b : ℝ, |a-A| < δ → |b-B| < δ →
        D (q+(t^2*a) • u+(t^k*b) • v) ≤ D q-c*t) := by
  let F := D ∘ τ.symm
  let Ω := τ.symm ⁻¹' continuityRegion D
  obtain ⟨op,cont⟩ := continuityRegion_spec D
  have localF : ContinuousOn F Ω := cont.comp τ.symm.continuous.continuousOn (fun _ h => h)
  have almost := localize_value F _ Ω (op.preimage τ.symm.continuous) localF
    (fun V cV => (Reduced.ae_no_box_germ V cV k hk).mono (fun p good => good F))
  letI : Measure.IsAddHaarMeasure (volume : Measure Ambient) := by
    rw [Measure.volume_eq_prod]; infer_instance
  letI : Measure.IsAddHaarMeasure (volume.map τ) := τ.isAddHaarMeasure_map volume
  have qm : Measure.QuasiMeasurePreserving τ volume volume :=
    ⟨τ.continuous.measurable,Measure.absolutelyContinuous_isAddHaarMeasure _ _⟩
  filter_upwards [qm.tendsto_ae almost] with q good
  intro mem A B c δ cp dp box
  apply good (by change τ.symm (τ q) ∈ continuityRegion D; simpa using mem) A B c δ cp dp
  intro t ht htδ a b ha hb
  have coords (r s : ℝ) : τ (q+r • u+s • v) = ((τ q).1,(τ q).2 + ![r,s]) := by
    rw [map_add,map_add,map_smul,map_smul,hu,hv]
    apply Prod.ext
    · simp
    · ext i
      fin_cases i <;> simp <;> rfl
  change D (τ.symm _) ≤ D (τ.symm (τ q)) - c*t
  rw [← coords,τ.symm_apply_apply,τ.symm_apply_apply]
  exact box t ht htδ a b ha hb

#print axioms ae_no_fixed_box

end MinimizingSard.Five
