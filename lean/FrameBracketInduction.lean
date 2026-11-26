import WordSpatialDifference
import MinimizingLengthPolar
import Mathlib.MeasureTheory.Function.Jacobian

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace MinimizingSard.Five
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M]
private abbrev P := State × ℝ
section
variable {m : ℕ}
private abbrev costBound (Γ : Geometry M m) (c : OpenPartialHomeomorph M State) (f : P → P) (L : ℝ) (p : P) :=
  ∃ b ∈ attainableLengths Γ (c.symm p.1) (c.symm (f p).1), b ≤ L*|p.2|

private structure Motion (Γ : Geometry M m) (c : OpenPartialHomeomorph M State) (q : State) (n : ℕ) where
  f : P → P
  b : P → P
  ft : ∀ p, (f p).2 = p.2
  bt : ∀ p, (b p).2 = p.2
  f0 : f (q,0) = (q,0)
  b0 : b (q,0) = (q,0)
  cf : ContDiffAt ℝ n f (q,0)
  cb : ContDiffAt ℝ n b (q,0)
  fb : ∀ᶠ p in 𝓝 (q,0), f (b p) = p
  bf : ∀ᶠ p in 𝓝 (q,0), b (f p) = p
  L : ℝ
  nonneg : 0 ≤ L
  cost : ∀ᶠ p in 𝓝 (q,0), costBound Γ c f L p

variable {Γ : Geometry M m} {c : OpenPartialHomeomorph M State} {q : State} {n : ℕ}
private theorem Motion.tf (A : Motion Γ c q n) : Tendsto A.f (𝓝 (q,0)) (𝓝 (q,0)) := by
  simpa only [A.f0] using A.cf.continuousAt.tendsto
private theorem Motion.tb (A : Motion Γ c q n) : Tendsto A.b (𝓝 (q,0)) (𝓝 (q,0)) := by
  simpa only [A.b0] using A.cb.continuousAt.tendsto

private def Motion.inv (A : Motion Γ c q n) : Motion Γ c q n :=
  ⟨A.b,A.f,A.bt,A.ft,A.b0,A.f0,A.cb,A.cf,A.bf,A.fb,A.L,A.nonneg,by
    filter_upwards [A.tb A.cost,A.fb] with p path back
    obtain ⟨b,hb,bd⟩ := path
    change b ∈ attainableLengths Γ (c.symm (A.b p).1) (c.symm (A.f (A.b p)).1) at hb
    rw [back,attainableLengths_reverse Γ] at hb
    exact ⟨b,hb,by simpa only [A.bt] using bd⟩⟩

private def Motion.thenM (A B : Motion Γ c q n) : Motion Γ c q n :=
  ⟨B.f ∘ A.f,A.b ∘ B.b,fun p => (B.ft _).trans (A.ft p),fun p => (A.bt _).trans (B.bt p),
    by simp [A.f0,B.f0],by simp [A.b0,B.b0],
    (show ContDiffAt ℝ n B.f (A.f (q,0)) by rw [A.f0]; exact B.cf).comp _ A.cf,
    (show ContDiffAt ℝ n A.b (B.b (q,0)) by rw [B.b0]; exact A.cb).comp _ B.cb,
    by filter_upwards [B.tb A.fb,B.fb] with p h k; exact (congrArg B.f h).trans k,
    by filter_upwards [A.tf B.bf,A.bf] with p h k; exact (congrArg A.b h).trans k,
    A.L+B.L,add_nonneg A.nonneg B.nonneg,by
      filter_upwards [A.cost,A.tf B.cost] with p h j
      obtain ⟨b,hb,bd⟩ := h
      obtain ⟨d,hd,dd⟩ := j
      exact ⟨b+d,attainableLengths_add hb hd,by simpa only [add_mul,A.ft] using add_le_add bd dd⟩⟩

private def Motion.lower (A : Motion Γ c q (n+1)) : Motion Γ c q n :=
  ⟨A.f,A.b,A.ft,A.bt,A.f0,A.b0,A.cf.of_le (mod_cast Nat.le_succ n),A.cb.of_le (mod_cast Nat.le_succ n),
    A.fb,A.bf,A.L,A.nonneg,A.cost⟩

private theorem generator_motion (e : Frame M m) (prof : HasGeneratorProfiles e) (he : e ∈ Γ.frames) (hq : q ∈ e.chart.target)
    (i : Fin m) (n : ℕ) (hn : 1 ≤ n) :
    ∃ (A : Motion Γ e.chart q n) (Z : P → State), ContDiffAt ℝ n Z (q,0) ∧
      (∀ᶠ z in 𝓝 q, Z (z,0) = e.X i z) ∧ ∀ᶠ p in 𝓝 (q,0), (A.f p).1 = wordEndpoint 1 Z p := by
  obtain ⟨F,Z,cf,cz,f0,z0,near⟩ := prof hq i n (mod_cast hn)
  let rev (p : P) := (p.1,-p.2)
  have r0 : rev (q,0) = (q,0) := by simp [rev]
  have cr : ContDiff ℝ n rev := contDiff_fst.prodMk contDiff_snd.neg
  let f (p : P) := (F p,p.2)
  let b (p : P) := (F (rev p),p.2)
  have cbf : ContDiffAt ℝ n F (rev (q,0)) := by rw [r0]; exact cf
  have cb : ContDiffAt ℝ n b (q,0) := (cbf.comp (q,0) cr.contDiffAt).prodMk contDiffAt_snd
  have b0 : b (q,0) = (q,0) := by simp [b,r0,f0]
  have tr : Tendsto rev (𝓝 (q,0)) (𝓝 (q,0)) := by simpa only [r0] using cr.continuous.tendsto (q,0)
  have tb : Tendsto b (𝓝 (q,0)) (𝓝 (q,0)) := by simpa only [b0] using cb.continuousAt.tendsto
  have undo : ∀ᶠ p in 𝓝 (q,(0:ℝ)), f (b p) = p := by
    filter_upwards [tr near,tb near,continuous_fst.continuousAt.tendsto (e.chart.open_target.mem_nhds hq)] with p hb hf hp
    have path : Segment e (framePulse i (-p.2)) (e.chart.symm p.1) (e.chart.symm (F (rev p))) := (hb.2.2 _).mpr rfl
    have back := segment_reverse path
    rw [reverse_pulse,neg_neg] at back
    exact Prod.ext (e.chart.symm.injOn hf.2.1 hp ((hf.2.2 _).mp back).symm) rfl
  have redo : ∀ᶠ p in 𝓝 (q,(0:ℝ)), b (f p) = p := by
    filter_upwards [tr undo] with p h
    refine Prod.ext ?_ rfl
    change f (b (rev p)) = rev p at h
    simpa [f,b,rev] using congrArg Prod.fst h
  refine ⟨⟨f,b,fun _ => rfl,fun _ => rfl,Prod.ext f0 rfl,b0,cf.prodMk contDiffAt_snd,cb,undo,redo,1,zero_le_one,?_⟩,
    Z,cz,z0,?_⟩
  · filter_upwards [near] with p h
    have seg := (h.2.2 _).mpr rfl
    refine ⟨|p.2|,⟨0,fun _ => e,fun _ => framePulse i p.2,fun _ => he,
      ⟨![e.chart.symm p.1,e.chart.symm (F p)],rfl,rfl,?_⟩,pulse_length i p.2⟩,by simp⟩
    intro j
    fin_cases j
    exact seg
  · filter_upwards [near] with p h using by simpa [wordEndpoint,f] using h.1

private theorem order_pos (w : BracketWord m) : 0 < w.order := by
  induction w with
  | field => exact Nat.one_pos
  | bracket a b ha hb => change 0 < a.order+b.order; omega

private theorem realize_word (e : Frame M m) (prof : HasGeneratorProfiles e) (he : e ∈ Γ.frames) (hq : q ∈ e.chart.target)
    (w : BracketWord m) (n : ℕ) (hn : 1 ≤ n) :
    ∃ (A : Motion Γ e.chart q n) (Z : P → State), ContDiffAt ℝ n Z (q,0) ∧
      (∀ᶠ z in 𝓝 q, Z (z,0) = w.eval e.X z) ∧
      ∀ᶠ p in 𝓝 (q,0), (A.f p).1 = wordEndpoint w.order Z p := by
  induction w generalizing n with
  | field i => exact generator_motion e prof he hq i n hn
  | bracket a b ia ib =>
    obtain ⟨A,X,cx,x0,ex⟩ := ia (n+1) (by omega)
    obtain ⟨B,Y,cy,y0,ey⟩ := ib (n+1) (by omega)
    let C := B.thenM A
    let H := A.thenM B
    let U (p : P) := (C.b p).1
    have ce : ∀ᶠ p in 𝓝 (q,(0:ℝ)), C.f p = (wordEndpoint a.order X (wordEndpoint b.order Y p,p.2),p.2) := by
      filter_upwards [B.tf ex,ey] with p ha hb
      have rep : B.f p = (wordEndpoint b.order Y p,p.2) := Prod.ext hb (B.ft p)
      exact Prod.ext (ha.trans (congrArg (wordEndpoint a.order X) rep)) (C.ft p)
    have se : ∀ᶠ p in 𝓝 (q,(0:ℝ)), H.f p = (wordEndpoint b.order Y (wordEndpoint a.order X p,p.2),p.2) := by
      filter_upwards [A.tf ey,ex] with p hb ha
      have rep : A.f p = (wordEndpoint a.order X p,p.2) := Prod.ext ha (A.ft p)
      exact Prod.ext (hb.trans (congrArg (wordEndpoint b.order Y) rep)) (H.ft p)
    have undo : ∀ᶠ p in 𝓝 (q,(0:ℝ)), U (wordEndpoint a.order X (wordEndpoint b.order Y p,p.2),p.2) = p.1 := by
      filter_upwards [ce,C.bf] with p h j
      rw [← h]
      exact congrArg Prod.fst j
    obtain ⟨Z,cz,z0,ez⟩ := word_exchange_profile a.order b.order n (order_pos a) (order_pos b) X Y U q
      (by simpa using cx) (by simpa using cy) (by simpa using C.cb.fst) undo
    refine ⟨(H.thenM C.inv).lower,Z,cz,?_,?_⟩
    · have xx : (fun z => X (z,0)) =ᶠ[𝓝 q] a.eval e.X := x0
      have yy : (fun z => Y (z,0)) =ᶠ[𝓝 q] b.eval e.X := y0
      filter_upwards [z0,xx.lieBracket_vectorField (𝕜 := ℝ) yy] with z h j using h.trans j
    · filter_upwards [se,ez] with p hp hz
      exact (congrArg U hp).trans hz

/-- Every original bracket word through order four supplies a true repair motion
with the bracket as its leading field throughout a neighborhood. -/
theorem bracket_repair_word_of_profiles (e : Frame M m) (prof : HasGeneratorProfiles e) (he : e ∈ Γ.frames) (hq : q ∈ e.chart.target)
    (w : BracketWord m) (hw : w.order ≤ 4) :
    ∃ W : RepairWord Γ e.chart q, W.order = w.order ∧
      ∀ᶠ z in 𝓝 q, W.profile (z,0) = w.eval e.X z := by
  obtain ⟨A,Z,cz,z0,ex⟩ := realize_word e prof he hq w 1 le_rfl
  refine ⟨⟨w.order,order_pos w,hw,fun p => (A.f p).1,fun p => (A.b p).1,Z,cz,A.cb.fst,
    congrArg Prod.fst A.b0,ex,?_,A.L,A.nonneg,?_⟩,rfl,z0⟩
  · filter_upwards [A.fb] with p h
    rw [show ((A.b p).1,p.2) = A.b p from Prod.ext rfl (A.bt p).symm]
    exact congrArg Prod.fst h
  · filter_upwards [A.cost] with p h using fun hp => by simpa only [costBound,abs_of_nonneg hp] using h


/-- Fourth-root two-point repair for the actual fixed-source length infimum at every
reachable center of step at most four in an original rank-two frame. -/
theorem frame_step_four_value_of_profiles (e : Frame M m) (prof : HasGeneratorProfiles e) (he : e ∈ Γ.frames) (hq : q ∈ e.chart.target)
    (full : wordLayer e.X q 4 = ⊤) (x : M) (reach : (attainableLengths Γ x (e.chart.symm q)).Nonempty) :
    let D := fun z => pointedLengthValue Γ x (e.chart.symm z)
    (∃ U : Set State, IsOpen U ∧ q ∈ U ∧ ContinuousOn D U) ∧
      ∃ K : ℝ, ∀ᶠ p : State × State in 𝓝 (q,q), |D p.2-D p.1| ≤ K*‖p.2-p.1‖^(1/4:ℝ) := by
  classical
  let S := {v : State | ∃ w : BracketWord m, w.order ≤ 4 ∧ w.eval e.X q = v}
  have span : Submodule.span ℝ S = ⊤ := full
  have dim : Module.finrank ℝ (Submodule.span ℝ S) = 5 := by rw [span,finrank_top,Module.finrank_fin_fun]
  have ex := Submodule.exists_fun_fin_finrank_span_eq ℝ S
  rw [dim] at ex
  obtain ⟨v,hv,_,ind⟩ := ex
  choose w hw eq using hv
  choose W _hw lead using fun i => bracket_repair_word_of_profiles e prof he hq (w i) (hw i)
  let B := basisOfPiSpaceOfLinearIndependent ind
  let L := B.equivFun.symm.toContinuousLinearEquiv
  have cols (s : State) : ∑ i, s i • (W i).profile (q,0) = L s := by
    have at0 (i) : (W i).profile (q,0) = v i := (lead i).self_of_nhds.trans (eq i)
    change _ = B.equivFun.symm s
    simp only [at0,Module.Basis.equivFun_symm_apply]
    exact congrArg (fun f : Fin 5 → State => ∑ i, s i • f i) (coe_basisOfPiSpaceOfLinearIndependent ind).symm
  obtain ⟨cont,K,bound⟩ := pointed_value_repair_of_words W L cols x reach
  refine ⟨cont,K,?_⟩
  have swap : Tendsto (Prod.swap : State × State → State × State) (𝓝 (q,q)) (𝓝 (q,q)) := continuous_swap.tendsto (q,q)
  filter_upwards [bound,swap bound] with p up down
  apply abs_le.mpr
  constructor
  · change pointedLengthValue Γ x (e.chart.symm p.1) ≤ pointedLengthValue Γ x (e.chart.symm p.2) +
        K*‖p.1-p.2‖^(1/4:ℝ) at down
    rw [norm_sub_rev p.1 p.2] at down
    linarith
  · linarith

end

variable {Γ : Geometry M 2} {c : OpenPartialHomeomorph M State} {q : State} {n : ℕ}

theorem bracket_repair_word (e : Frame M 2) (he : e ∈ Γ.frames) (hq : q ∈ e.chart.target)
    (w : BracketWord 2) (hw : w.order ≤ 4) :
    ∃ W : RepairWord Γ e.chart q, W.order = w.order ∧
      ∀ᶠ z in 𝓝 q, W.profile (z,0) = w.eval e.X z :=
  bracket_repair_word_of_profiles e (fun h i n hn => generator_flow_profile e h i n hn) he hq w hw

#print axioms bracket_repair_word

theorem frame_step_four_value (e : Frame M 2) (he : e ∈ Γ.frames) (hq : q ∈ e.chart.target)
    (full : wordLayer e.X q 4 = ⊤) (x : M) (reach : (attainableLengths Γ x (e.chart.symm q)).Nonempty) :
    let D := fun z => pointedLengthValue Γ x (e.chart.symm z)
    (∃ U : Set State, IsOpen U ∧ q ∈ U ∧ ContinuousOn D U) ∧
      ∃ K : ℝ, ∀ᶠ p : State × State in 𝓝 (q,q), |D p.2-D p.1| ≤ K*‖p.2-p.1‖^(1/4:ℝ) :=
  frame_step_four_value_of_profiles e (fun h i n hn => generator_flow_profile e h i n hn) he hq full x reach

/-- Local estimates that repair a fourth-order change of endpoint while
preserving half of a strict first-order length saving. -/
abbrev ChartValueRepair (Γ : Geometry M 2) (chart : OpenPartialHomeomorph M State) : Prop :=
    ∀ᵐ q : State, q ∈ chart.target → ∀ x : M, (attainableLengths Γ x (chart.symm q)).Nonempty →
      let D := fun z => pointedLengthValue Γ x (chart.symm z)
      (∃ U : Set State, IsOpen U ∧ q ∈ U ∧ ContinuousOn D U) ∧
      (∃ K : ℝ, ∀ᶠ p : State × State in 𝓝 (q,q), |D p.2-D p.1| ≤ K*‖p.2-p.1‖^(1/4:ℝ)) ∧
      ∀ c : ℝ, 0 < c → ∃ ε > 0, ∀ᶠ p : State × State in 𝓝 (q,q), ∀ t : ℝ, 0 ≤ t →
        ‖p.2-p.1‖ ≤ ε*t^4 → D p.1 ≤ D q-c*t → D p.2 ≤ D q-(c/2)*t

private theorem fourth_root_repair (D : State → ℝ) (q : State) (K : ℝ)
    (bound : ∀ᶠ p : State × State in 𝓝 (q,q), |D p.2-D p.1| ≤ K*‖p.2-p.1‖^(1/4:ℝ)) :
    ∀ c : ℝ, 0 < c → ∃ ε > 0, ∀ᶠ p : State × State in 𝓝 (q,q), ∀ t : ℝ, 0 ≤ t →
      ‖p.2-p.1‖ ≤ ε*t^4 → D p.1 ≤ D q-c*t → D p.2 ≤ D q-(c/2)*t := by
  intro c hc
  let L := max 1 K
  have pos : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_left ..)
  let a := (c/2)/L
  have ha : 0 < a := div_pos (half_pos hc) pos
  refine ⟨a^4,pow_pos ha 4,?_⟩
  filter_upwards [bound] with p hp
  intro t ht err saved
  have root := Real.rpow_le_rpow (norm_nonneg _) (err.trans_eq (mul_pow a t 4).symm) (by norm_num : 0 ≤ (1/4:ℝ))
  have ident : ((a*t)^4)^(1/4:ℝ) = a*t := by
    simpa only [one_div,Nat.cast_ofNat] using Real.pow_rpow_inv_natCast (n := 4) (mul_nonneg ha.le ht) (by decide)
  rw [ident] at root
  have pay : K*‖p.2-p.1‖^(1/4:ℝ) ≤ (c/2)*t := by
    calc
      _ ≤ L * ‖p.2-p.1‖^(1/4:ℝ) := mul_le_mul_of_nonneg_right (le_max_right ..) (Real.rpow_nonneg (norm_nonneg _) _)
      _ ≤ L*(a*t) := mul_le_mul_of_nonneg_left root pos.le
      _ = _ := by dsimp [a]; field_simp
  linarith [(le_abs_self _).trans hp]

/-- Each original frame supplies the repair estimate independently of the source. -/
theorem ae_frame_value_repair (e : Frame M 2) (he : e ∈ Γ.frames) : ChartValueRepair Γ e.chart := by
  filter_upwards [ae_frame_step_four e] with q growth
  intro hq x reach
  obtain ⟨cont,K,bound⟩ := frame_step_four_value e he hq (growth hq).2.2 x reach
  exact ⟨cont,⟨K,bound⟩,fourth_root_repair (fun z => pointedLengthValue Γ x (e.chart.symm z)) q K bound⟩

#print axioms frame_step_four_value
#print axioms ae_frame_value_repair

/-- In the quartic alternative, a reduced family of competitors for the original
length and its endpoint jets give an entire box of cheaper endpoints. -/
abbrev QuarticLengthBoxes (Γ : Geometry M 2) (chart : OpenPartialHomeomorph M State) : Prop :=
    ∀ᵐ q : State, q ∈ chart.target → ∀ {K : Type} [NormedAddCommGroup K] [NormedSpace ℝ K]
      {N : ℕ} (d : Fin (N+1) → Frame M 2) (w : Fin (N+1) → Control 2) (x : M),
      (∀ i, d i ∈ Γ.frames) → Joins d w x (chart.symm q) →
      (∀ (k : ℕ) (r : Fin (k+1) → Frame M 2) (v : Fin (k+1) → Control 2),
        (∀ i, r i ∈ Γ.frames) → Joins r v x (chart.symm q) → length w ≤ length v) →
      ∀ (S : K → (Fin (N+1) → Control 2)) (T : K →L[ℝ] (Fin (N+1) → Control 2)) (h : K),
      S 0 = 0 → HasFDerivAt S T 0 → length (w+T h) < length w →
      ∀ (f g : K → ℝ) (u v : State), ContDiffAt ℝ 2 f 0 → ContDiffAt ℝ 4 g 0 →
      (∀ j ≤ 1, ∀ b : K, iteratedFDeriv ℝ j f 0 (fun _ => b) = 0) →
      (∀ j ≤ 3, ∀ b : K, iteratedFDeriv ℝ j g 0 (fun _ => b) = 0) →
      fderiv ℝ (Return.coeff f 2 0) h ≠ 0 →
      (∀ᶠ z in 𝓝 0, Joins d (w+S z) x (chart.symm (q + f z • u + g z • v))) →
      ∃ c > 0, ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ → ∀ a b : ℝ,
        |a-Return.coeff f 2 0 h| < δ → |b-Return.coeff g 4 0 h| < δ →
        pointedLengthValue Γ x (chart.symm (q+(t^2*a) • u+(t^4*b) • v)) ≤
          pointedLengthValue Γ x (chart.symm q)-c*t

theorem quartic_boxes_of_repair (Γ : Geometry M 2) (chart : OpenPartialHomeomorph M State)
    (repair : ChartValueRepair Γ chart) : QuarticLengthBoxes Γ chart := by
  filter_upwards [repair] with q good
  intro hq K _ _ N d w x hd hw hmin S T h s0 ds down f g u v cf cg ff gg regular joins
  have reachable : (attainableLengths Γ x (chart.symm q)).Nonempty := ⟨length w,N,d,w,hd,hw,rfl⟩
  have id := pointedLengthValue_eq hd hw hmin
  obtain ⟨c,hc,save⟩ := length_cone_on_radial_chart w S T s0 ds h down
  obtain ⟨ε,hε,repair⟩ := (good hq x reachable).2.2 c hc
  let A := Return.coeff f 2 0 h
  let B := Return.coeff g 4 0 h
  let η := ε/(2*(‖v‖+1))
  have den : 0 < 2*(‖v‖+1) := by positivity
  have hη : 0 < η := div_pos hε den
  obtain ⟨r,hr,profile⟩ := Return.radial_profile g 3 h cg gg hη
  let center : ℝ × K × ℝ := (0,h,B)
  let z (p : ℝ × K × ℝ) := p.1 • p.2.1
  let y (p : ℝ × K × ℝ) := q+f (z p) • u + g (z p) • v
  let Y (p : ℝ × K × ℝ) := q+f (z p) • u + (p.1^4*p.2.2) • v
  have f0 : f 0 = 0 := by simpa using ff 0 (by decide) 0
  have g0 : g 0 = 0 := by simpa using gg 0 (by decide) 0
  have z0 : z center = 0 := by simp [center,z]
  have cz : Continuous z := continuous_fst.smul (continuous_fst.comp continuous_snd)
  have C0 : Tendsto z (𝓝 center) (𝓝 0) := by simpa only [z0] using cz.tendsto center
  have fz := (show ContinuousAt f (z center) by rw [z0]; exact cf.continuousAt).comp cz.continuousAt
  have gz := (show ContinuousAt g (z center) by rw [z0]; exact cg.continuousAt).comp cz.continuousAt
  have c₁ : ContinuousAt y center := (continuousAt_const.add (fz.smul continuousAt_const)).add (gz.smul continuousAt_const)
  have c₂ : ContinuousAt Y center := (continuousAt_const.add (fz.smul continuousAt_const)).add
    ((((continuous_fst.pow 4).mul (continuous_snd.comp continuous_snd)).continuousAt).smul continuousAt_const)
  have pair : Tendsto (fun p => (y p,Y p)) (𝓝 center) (𝓝 (q,q)) := by
    simpa [y,Y,z0,f0,g0,center,z] using (c₁.prodMk c₂).tendsto
  have proj : Tendsto (fun p : ℝ × K × ℝ => (p.1,p.2.1)) (𝓝 center) (𝓝 (0,h)) :=
    (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).tendsto center
  obtain ⟨s,hs,tube⟩ := Metric.mem_nhds_iff.mp (inter_mem (inter_mem (pair repair) (proj save)) (C0 joins))
  let R := min r s
  have hR : 0 < R := lt_min hr hs
  obtain ⟨d₀,hd₀,solve⟩ := Return.quadratic_coordinate f h cf ff regular hR
  let δ := min d₀ (min R η)
  refine ⟨c/2,half_pos hc,δ,lt_min hd₀ (lt_min hR hη),?_⟩
  intro t ht small a b ha hb
  have tR : t < R := small.trans_le ((min_le_right ..).trans (min_le_left ..))
  have bR : |b-B| < R := hb.trans_le ((min_le_right ..).trans (min_le_left ..))
  have bη : |b-B| < η := hb.trans_le ((min_le_right ..).trans (min_le_right ..))
  obtain ⟨j,hj,hit⟩ := solve t ht (small.trans_le (min_le_left ..)) a (ha.trans_le (min_le_left ..))
  have jR : dist j h < R := hj
  have use := tube (show (t,j,b) ∈ Metric.ball center s by
    simpa [center,Metric.mem_ball,Prod.dist_eq,Real.dist_eq,abs_of_pos ht] using
      And.intro (tR.trans_le (min_le_right ..)) (And.intro (jR.trans_le (min_le_right ..)) (bR.trans_le (min_le_right ..))))
  have prof := profile t ht (tR.trans_le (min_le_left ..)) j (jR.trans_le (min_le_left ..))
  have price := pointedLengthValue_le hd use.2
  have saved := (use.1.2 ht)
  change length (w+S (z (t,j,b))) ≤ length w-c*t at saved
  have diff : Y (t,j,b) - y (t,j,b) = (t^4*b-g (t • j)) • v := by
    simp only [Y,y,z,sub_smul]
    abel
  have rel : |b-g (t • j)/t^4| ≤ 2*η := by
    have tri := abs_sub_le b B (g (t • j)/t^4)
    rw [abs_sub_comm B] at tri
    linarith
  have mag : |t^4*b-g (t • j)| ≤ t^4*(2*η) := by
    have fac : t^4*b-g (t • j) = t^4*(b-g (t • j)/t^4) := by field_simp
    rw [fac,abs_mul,abs_of_nonneg (by positivity : 0 ≤ t^4)]
    exact mul_le_mul_of_nonneg_left rel (by positivity)
  have pay : ‖Y (t,j,b)-y (t,j,b)‖ ≤ ε*t^4 := by
    rw [diff,norm_smul,Real.norm_eq_abs]
    have rel' := mul_le_mul_of_nonneg_right mag (norm_nonneg v)
    have eq : 2*η*(‖v‖+1) = ε := by dsimp [η]; field_simp
    have bound : 2*η*‖v‖ ≤ ε := by nlinarith
    calc
      _ ≤ _ := rel'
      _ = t^4*(2*η*‖v‖) := mul_assoc _ _ _
      _ ≤ ε*t^4 := by rw [mul_comm ε]; exact mul_le_mul_of_nonneg_left bound (by positivity)
  have net := use.1.1 t ht.le pay (by
    change pointedLengthValue Γ x (chart.symm (y (t,j,b))) ≤ pointedLengthValue Γ x (chart.symm q)-c*t
    rw [id]
    exact price.trans saved)
  simpa only [Y,z,hit] using net

theorem ae_actual_quartic_box (e : Frame M 2) (he : e ∈ Γ.frames) : QuarticLengthBoxes Γ e.chart :=
  quartic_boxes_of_repair Γ e.chart (ae_frame_value_repair e he)

#print axioms ae_actual_quartic_box

open scoped Manifold in
/-- The a.e. polar restriction in an original frame chart, with reachability
and local continuity supplied by the minimizing path and the bracket repair. -/
theorem ae_original_frame_polar [IsManifold 𝓘(ℝ,State) ∞ M] (e : Frame M 2) (he : e ∈ Γ.frames)
    (x : M) (τ : State ≃L[ℝ] Reduced.Ambient) :
    ∀ᵐ z : State, MinimizingPolarAt Γ x e.chart τ (τ z) := by
  filter_upwards [ae_frame_value_repair e he,ae_chart_length_polar Γ x e.chart e.compatible τ] with z repair polar
  intro n d w y G hy hd joins minimal graph matchEnd onto π sur cok absent
  have atw := graph.self_of_nhds
  have ez : z = G w := τ.injective matchEnd
  have same : y = e.chart.symm z := ez ▸ (atw.2 _).mp joins
  have inside : z ∈ e.chart.target := ez ▸ atw.1
  have reach : (attainableLengths Γ x (e.chart.symm z)).Nonempty :=
    ⟨length w,n,d,w,hd,same ▸ joins,rfl⟩
  obtain ⟨U,op,mem,continuous⟩ := (repair inside x reach).1
  have region : z ∈ continuityRegion (fun s => pointedLengthValue Γ x (e.chart.symm s)) :=
    mem_iUnion.mpr ⟨U,mem_iUnion.mpr ⟨⟨op,continuous⟩,mem⟩⟩
  exact polar region n d w y G hy hd joins minimal graph matchEnd onto π sur cok absent

#print axioms ae_original_frame_polar

open IsManifold
open scoped Manifold

private theorem transition_contDiffOn [IsManifold 𝓘(ℝ,State) ∞ M]
    (b c : OpenPartialHomeomorph M State) (hb : b ∈ maximalAtlas 𝓘(ℝ,State) ∞ M)
    (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) :
    ContDiffOn ℝ ∞ (c ∘ b.symm) (b.symm.trans c).source := by
  have h := (IsManifold.compatible_of_mem_maximalAtlas hb hc).1
  change ContDiffOn ℝ ∞ (c ∘ b.symm) ((b.symm.trans c).source ∩ range (𝓘(ℝ,State))) at h
  simpa using h

/-- Transfer a full-measure assertion through a smooth chart overlap,
including assertions about nonmeasurable families of witnesses. -/
theorem ae_chart_overlap [IsManifold 𝓘(ℝ,State) ∞ M]
    (b c : OpenPartialHomeomorph M State) (hb : b ∈ maximalAtlas 𝓘(ℝ,State) ∞ M)
    (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (P : State → Prop)
    (good : ∀ᵐ p : State, p ∈ b.target → P p) :
    ∀ᵐ q : State, q ∈ (c.symm.trans b).source → P (b (c.symm q)) := by
  let B := (b.symm.trans c).source ∩ {p | ¬ P p}
  have null : volume B = 0 := by
    apply measure_mono_null _ (ae_iff.mp good)
    rintro p ⟨hp,bad⟩ all
    exact bad (all hp.1)
  have image := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    (((transition_contDiffOn b c hb hc).differentiableOn (by simp)).mono (inter_subset_left (t := _))) null
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp image] with q safe
  intro hq
  by_contra bad
  apply safe
  have iy : c.symm q ∈ b.source := hq.2
  refine ⟨b (c.symm q),⟨⟨b.map_source iy,?_⟩,bad⟩,?_⟩
  · change b.symm (b (c.symm q)) ∈ c.source
    rw [b.left_inv iy]
    exact c.map_target hq.1
  · simp only [Function.comp_apply,b.left_inv iy,c.right_inv hq.1]

/-- Each compatible chart admits a common null exception outside which a
containing original frame has a full fourth bracket layer. The frame cover
in the geometry may be uncountable. -/
theorem ae_compatible_step_four_at_rank {m : ℕ} [IsManifold 𝓘(ℝ,State) ∞ M] (Γ : Geometry M m) (hm : 2 ≤ m)
    (c : OpenPartialHomeomorph M State) (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) :
    ∀ᵐ q : State, q ∈ c.target → ∃ e ∈ Γ.frames, c.symm q ∈ e.chart.source ∧
      wordLayer e.X (e.chart (c.symm q)) 4 = ⊤ := by
  let U (e : Γ.frames) := (c.symm.trans e.val.chart).source
  have covers (q) (hq : q ∈ c.target) : q ∈ ⋃ e, U e := by
    obtain ⟨e,he,inside⟩ := Γ.cover (c.symm q)
    exact mem_iUnion.mpr ⟨⟨e,he⟩,hq,inside⟩
  obtain ⟨T,count,cov⟩ := (IsLindelof.of_coe : IsLindelof c.target).elim_countable_subcover
    U (fun e => (c.symm.trans e.val.chart).open_source) covers
  letI : Countable T := count.to_subtype
  have good (e : Γ.frames) : ∀ᵐ q : State, q ∈ U e → wordLayer e.val.X (e.val.chart (c.symm q)) 4 = ⊤ := by
    apply ae_chart_overlap e.val.chart c e.val.compatible hc (fun p => wordLayer e.val.X p 4 = ⊤)
    exact (ae_frame_growth_bounds e.val hm).mono fun _ h inside => (h inside).2.2
  filter_upwards [ae_all_iff.mpr (fun e : T => good e.val)] with q all
  intro hq
  obtain ⟨e,hit⟩ := mem_iUnion.mp (cov hq)
  obtain ⟨he,inside⟩ := mem_iUnion.mp hit
  exact ⟨e.val,e.property,inside.2,all ⟨e,he⟩ inside⟩

theorem ae_compatible_step_four [IsManifold 𝓘(ℝ,State) ∞ M] (Γ : Geometry M 2)
    (c : OpenPartialHomeomorph M State) (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) :
    ∀ᵐ q : State, q ∈ c.target → ∃ e ∈ Γ.frames, c.symm q ∈ e.chart.source ∧
      wordLayer e.X (e.chart (c.symm q)) 4 = ⊤ :=
  ae_compatible_step_four_at_rank Γ (by decide) c hc

#print axioms ae_compatible_step_four

/-- The original pointed length is locally continuous and has a two-point
fourth-root estimate in arbitrary compatible target charts, simultaneously
for all reachable sources at almost every center. -/
theorem ae_compatible_chart_value_of_profiles {m : ℕ} [IsManifold 𝓘(ℝ,State) ∞ M] (Γ : Geometry M m) (hm : 2 ≤ m)
    (profiles : ∀ e ∈ Γ.frames, HasGeneratorProfiles e)
    (c : OpenPartialHomeomorph M State) (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) :
    ∀ᵐ q : State, q ∈ c.target → ∀ x : M, (attainableLengths Γ x (c.symm q)).Nonempty →
      let D := fun z => pointedLengthValue Γ x (c.symm z)
      (∃ U : Set State, IsOpen U ∧ q ∈ U ∧ ContinuousOn D U) ∧
      ∃ K : ℝ, ∀ᶠ p : State × State in 𝓝 (q,q), |D p.2-D p.1| ≤ K*‖p.2-p.1‖^(1/4:ℝ) := by
  filter_upwards [ae_compatible_step_four_at_rank Γ hm c hc] with q good
  intro hq x reach D
  obtain ⟨e,he,inside,full⟩ := good hq
  let T := e.chart ∘ c.symm
  let E (z : State) := pointedLengthValue Γ x (e.chart.symm z)
  let U := (c.symm.trans e.chart).source
  have uq : q ∈ U := ⟨hq,inside⟩
  have op : IsOpen U := (c.symm.trans e.chart).open_source
  have same {z} (hz : z ∈ U) : E (T z) = D z := congrArg (pointedLengthValue Γ x) (e.chart.left_inv hz.2)
  have smooth := transition_contDiffOn c e.chart hc e.compatible
  have atT {z} (hz : z ∈ U) : ContDiffAt ℝ 1 T z := ((smooth z hz).contDiffAt (op.mem_nhds hz)).of_le (by simp)
  have source : (attainableLengths Γ x (e.chart.symm (T q))).Nonempty := by
    simpa only [T,Function.comp_apply,e.chart.left_inv inside] using reach
  obtain ⟨⟨V,hV,vq,cv⟩,K,bound⟩ := frame_step_four_value_of_profiles e (profiles e he) he (e.chart.map_source inside) full x source
  have near : ∀ᶠ z in 𝓝 q, z ∈ U ∧ T z ∈ V :=
    inter_mem (op.mem_nhds uq) ((atT uq).continuousAt.tendsto (hV.mem_nhds vq))
  obtain ⟨r,rp,ball⟩ := Metric.mem_nhds_iff.mp near
  constructor
  · refine ⟨Metric.ball q r,Metric.isOpen_ball,Metric.mem_ball_self rp,?_⟩
    have compose : ContinuousOn (E ∘ T) (Metric.ball q r) := cv.comp
      (fun z hz => (atT (ball hz).1).continuousAt.continuousWithinAt) (fun z hz => (ball hz).2)
    exact compose.congr (fun z hz => (same (ball hz).1).symm)
  · obtain ⟨L,S,hs,lip⟩ := (atT uq).exists_lipschitzOnWith
    let C := max 0 K
    refine ⟨C * (L:ℝ)^(1/4:ℝ),?_⟩
    have ct := (atT uq).continuousAt
    have push : Tendsto (fun p : State × State => (T p.1,T p.2)) (𝓝 (q,q)) (𝓝 (T q,T q)) :=
      (ct.tendsto.comp (continuous_fst.tendsto (q,q))).prodMk_nhds (ct.tendsto.comp (continuous_snd.tendsto (q,q)))
    have both : U ∩ S ∈ 𝓝 q := inter_mem (op.mem_nhds uq) hs
    filter_upwards [push bound,continuous_fst.continuousAt.tendsto both,
      continuous_snd.continuousAt.tendsto both] with p bh h₁ h₂
    rw [← same h₁.1,← same h₂.1]
    have dist : ‖T p.2-T p.1‖ ≤ (L:ℝ)*‖p.2-p.1‖ := by
      simpa only [dist_eq_norm] using lip.dist_le_mul _ h₂.2 _ h₁.2
    calc
      _ ≤ K*‖T p.2-T p.1‖^(1/4:ℝ) := bh
      _ ≤ C*‖T p.2-T p.1‖^(1/4:ℝ) := mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity)
      _ ≤ C*((L:ℝ)*‖p.2-p.1‖)^(1/4:ℝ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (norm_nonneg _) dist (by norm_num)) (le_max_left ..)
      _ = _ := by rw [Real.mul_rpow L.coe_nonneg (norm_nonneg _),mul_assoc]

theorem ae_compatible_chart_value [IsManifold 𝓘(ℝ,State) ∞ M] (Γ : Geometry M 2)
    (c : OpenPartialHomeomorph M State) (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) :
    ∀ᵐ q : State, q ∈ c.target → ∀ x : M, (attainableLengths Γ x (c.symm q)).Nonempty →
      let D := fun z => pointedLengthValue Γ x (c.symm z)
      (∃ U : Set State, IsOpen U ∧ q ∈ U ∧ ContinuousOn D U) ∧
      ∃ K : ℝ, ∀ᶠ p : State × State in 𝓝 (q,q), |D p.2-D p.1| ≤ K*‖p.2-p.1‖^(1/4:ℝ) :=
  ae_compatible_chart_value_of_profiles Γ (by decide) (fun e _ => fun {_} h i n hn => generator_flow_profile e h i n hn) c hc

#print axioms ae_compatible_chart_value

theorem ae_compatible_value_repair [IsManifold 𝓘(ℝ,State) ∞ M] (Γ : Geometry M 2)
    (c : OpenPartialHomeomorph M State) (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) : ChartValueRepair Γ c := by
  filter_upwards [ae_compatible_chart_value Γ c hc] with q good
  intro hq x reach
  obtain ⟨cont,K,bound⟩ := good hq x reach
  exact ⟨cont,⟨K,bound⟩,fourth_root_repair (fun z => pointedLengthValue Γ x (c.symm z)) q K bound⟩

#print axioms ae_compatible_value_repair
end MinimizingSard.Five
