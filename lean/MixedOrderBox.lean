import QuarticReturn
import QuadraticCubic

/-! Uniform openness of the normalized two-dimensional endpoint family.
Only the two auxiliary control parameters are differentiated. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace MinimizingSard.Return
private abbrev Plane := ℝ × ℝ
private def e₁ : Plane := (1,0)
private def e₂ : Plane := (0,1)

private theorem plane_bound (D : Plane →L[ℝ] Plane)
    (h₁ : ‖D e₁ - e₁‖ ≤ 1/4) (h₂ : ‖D e₂ - e₂‖ ≤ 1/4) :
    ‖D - ContinuousLinearMap.id ℝ Plane‖ ≤ 1/2 := by
  let T := D - ContinuousLinearMap.id ℝ Plane
  apply T.opNorm_le_bound (by norm_num)
  intro p
  have decomp : p = p.1 • e₁ + p.2 • e₂ := by ext <;> simp [e₁,e₂]
  have eq : T p = p.1 • T e₁ + p.2 • T e₂ := by
    conv_lhs => rw [decomp,map_add,map_smul,map_smul]
  have b₁ := mul_le_mul_of_nonneg_left h₁ (norm_nonneg p.1)
  have b₂ := mul_le_mul_of_nonneg_left h₂ (norm_nonneg p.2)
  have b₃ : ‖p.1‖ ≤ ‖p‖ := le_max_left _ _
  have b₄ : ‖p.2‖ ≤ ‖p‖ := le_max_right _ _
  change ‖p.1‖ * ‖T e₁‖ ≤ _ at b₁
  change ‖p.2‖ * ‖T e₂‖ ≤ _ at b₂
  rw [eq]
  have tri := norm_add_le (p.1 • T e₁) (p.2 • T e₂)
  rw [norm_smul,norm_smul] at tri
  linarith

private theorem fills_ball (F : Plane → Plane) {r : ℝ} (hr : 0 < r)
    (bound : ∀ p ∈ closedBall (0:Plane) r, ∃ D : Plane →L[ℝ] Plane,
      HasFDerivAt F D p ∧ ‖D e₁-e₁‖ ≤ 1/4 ∧ ‖D e₂-e₂‖ ≤ 1/4) :
    SurjOn F (closedBall (0:Plane) r) (closedBall (F 0) (r/2)) := by
  let I := ContinuousLinearMap.id ℝ Plane
  have near : ApproximatesLinearOn F I (closedBall 0 r) (1/2) := by
    intro y hy x hx
    apply (convex_closedBall (0:Plane) r).norm_image_sub_le_of_norm_hasFDerivWithin_le'
      (f' := fderiv ℝ F) (fun p hp => (bound p hp).choose_spec.1.fderiv ▸
        (bound p hp).choose_spec.1.hasFDerivWithinAt) _ hx hy
    intro p hp
    obtain ⟨D,df,h₁,h₂⟩ := bound p hp
    rw [df.fderiv]
    exact plane_bound D h₁ h₂
  let inv : I.NonlinearRightInverse :=
    { toFun := id, nnnorm := 1, bound' := by simp, right_inv' := fun _ => rfl }
  have sur := near.surjOn_closedBall_of_nonlinearRightInverse inv hr.le (Subset.rfl)
  convert sur using 2
  norm_num [inv]
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private def directional (f : E → ℝ) (b : E) (x : E) := fderiv ℝ f x b

private theorem partial_smooth (f : E → ℝ) (n : ℕ) (b : E) (hf : ContDiffAt ℝ (n+1 : ℕ) f 0) :
    ContDiffAt ℝ n (directional f b) 0 :=
  (hf.fderiv_right (m := (n : WithTop ℕ∞)) (by simp)).clm_apply contDiffAt_const

private def coord (f : E → ℝ) (k : ℕ) (h : E) (B : Plane →L[ℝ] E) (t : ℝ) (p : Plane) :=
  f (t • (h+B p))/t^k

private theorem coord_deriv (f : E → ℝ) (k : ℕ) (h : E) (B : Plane →L[ℝ] E) (t : ℝ) (p : Plane)
    (d : DifferentiableAt ℝ f (t • (h+B p))) :
    ∃ D : Plane →L[ℝ] ℝ, HasFDerivAt (coord f (k+1) h B t) D p ∧
      ∀ w, t ≠ 0 → D w = directional f (B w) (t • (h+B p))/t^k := by
  have hpre := ((B.hasFDerivAt (x := p)).const_add h).const_smul t
  have hh := ((d.hasFDerivAt.comp p hpre).const_smul (t^(k+1))⁻¹)
  refine ⟨(t^(k+1))⁻¹ • (fderiv ℝ f (t • (h+B p))).comp (t • B),?_,?_⟩
  · convert hh using 1
    funext w
    change f (t • (h+B w))/t^(k+1) = (t^(k+1))⁻¹ * f (t • (h+B w))
    ring
  · intro w ht
    simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,map_smul,smul_eq_mul,directional]
    rw [pow_succ]
    field_simp

private theorem near_profile (f : E → ℝ) (n : ℕ) (h : E) (B : Plane →L[ℝ] E)
    (hf : ContDiffAt ℝ (n+1 : ℕ) f 0)
    (flat : ∀ j ≤ n, ∀ v : E, iteratedFDeriv ℝ j f 0 (fun _ => v) = 0)
    {ε : ℝ} (he : 0 < ε) :
    ∀ᶠ p : ℝ × Plane in 𝓝 0, 0 < p.1 →
      |coord f (n+1) h B p.1 p.2 - coeff f (n+1) 0 h| < ε := by
  obtain ⟨δ,hδ,prof⟩ := radial_profile f n h hf flat he
  have vcont : Continuous (fun p : ℝ × Plane => h+B p.2) := continuous_const.add (B.continuous.comp continuous_snd)
  have vc : Tendsto (fun p : ℝ × Plane => h+B p.2) (𝓝 0) (𝓝 h) := by simpa using vcont.tendsto 0
  have tcont : ∀ᶠ p : ℝ × Plane in 𝓝 0, p.1 < δ := continuousAt_fst.eventually_lt continuousAt_const hδ
  filter_upwards [tcont,vc (ball_mem_nhds h hδ)] with p hp hv
  exact fun ht => prof _ ht hp _ hv

private theorem row_approx (f : E → ℝ) (n : ℕ) (h : E) (B : Plane →L[ℝ] E)
    (hf : ContDiffAt ℝ (n+2 : ℕ) f 0)
    (flat : ∀ b : E, ∀ j ≤ n, ∀ v : E,
      iteratedFDeriv ℝ j (directional f b) 0 (fun _ => v) = 0) :
    ∀ᶠ p : ℝ × Plane in 𝓝 0, 0 < p.1 →
      ∃ D : Plane →L[ℝ] ℝ, HasFDerivAt (coord f (n+2) h B p.1) D p.2 ∧
        |D e₁ - coeff (directional f (B e₁)) (n+1) 0 h| ≤ 1/4 ∧
        |D e₂ - coeff (directional f (B e₂)) (n+1) 0 h| ≤ 1/4 := by
  have approx (w : Plane) := near_profile (directional f (B w)) n h B
    (partial_smooth f (n+1) (B w) hf) (flat _) (by norm_num : 0 < (1/4:ℝ))
  have co : Continuous (fun p : ℝ × Plane => p.1 • (h+B p.2)) :=
    continuous_fst.smul (continuous_const.add (B.continuous.comp continuous_snd))
  have to0 : Tendsto (fun p : ℝ × Plane => p.1 • (h+B p.2)) (𝓝 0) (𝓝 0) := by simpa using co.tendsto 0
  have finite : ((n+2 : ℕ) : WithTop ℕ∞) ≠ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact fun eq => ENat.coe_ne_top (n+2) (WithTop.coe_injective eq)
  have df := (hf.eventually finite).mono fun x hx => hx.differentiableAt (by exact_mod_cast (show 1 ≤ n+2 by omega))
  filter_upwards [approx e₁,approx e₂,to0 df] with p a b dif
  intro ht
  obtain ⟨D,der,eval⟩ := coord_deriv f (n+1) h B p.1 p.2 dif
  refine ⟨D,der,?_,?_⟩
  · rw [eval _ ht.ne']
    exact (a ht).le
  · rw [eval _ ht.ne']
    exact (b ht).le

/-- An open box of scaled endpoints when the limiting two columns of
the normalized Jacobian are the two coordinate vectors. -/
private theorem open_box_of_cone (n : ℕ) (f g : E → ℝ) (V : ℝ × ℝ → ℝ) (h : E) (B : (ℝ × ℝ) →L[ℝ] E)
    (hf : ContDiffAt ℝ 2 f 0) (hg : ContDiffAt ℝ (n+2 : ℕ) g 0)
    (f0 : f 0 = 0) (f1 : fderiv ℝ f 0 = 0)
    (vg : ∀ j ≤ n+1, ∀ v : E, iteratedFDeriv ℝ j g 0 (fun _ => v) = 0)
    (dg : ∀ b : E, ∀ j ≤ n, ∀ v : E, iteratedFDeriv ℝ j (directional g b) 0 (fun _ => v) = 0)
    (col₁ : ∀ w, coeff (fun x => fderiv ℝ f x (B w)) 1 0 h = w.1)
    (col₂ : ∀ w, coeff (fun x => fderiv ℝ g x (B w)) (n+1) 0 h = w.2)
    (c : ℝ) (save : ∀ᶠ p : ℝ × Plane in 𝓝 0, 0 < p.1 →
      V (f (p.1 • (h+B p.2)),g (p.1 • (h+B p.2))) ≤ V 0-c*p.1) :
    ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ → ∀ a b : ℝ,
      |a-coeff f 2 0 h| < δ → |b-coeff g (n+2) 0 h| < δ →
      V (t^2*a,t^(n+2)*b) ≤ V 0 - c*t := by
  have vf : ∀ j ≤ 1, ∀ v : E, iteratedFDeriv ℝ j f 0 (fun _ => v) = 0 := by
    intro j hj v
    interval_cases j <;> simp [f0,f1]
  have fc := row_approx f 0 h B hf (by
    intro b j hj v
    obtain rfl : j = 0 := by omega
    simp [directional,f1])
  have gc := row_approx g n h B hg dg
  let F (t : ℝ) (p : Plane) := (coord f 2 h B t p,coord g (n+2) h B t p)
  let center : Plane := (coeff f 2 0 h,coeff g (n+2) 0 h)
  obtain ⟨R,hR,tube⟩ := Metric.mem_nhds_iff.mp ((fc.and gc).and save)
  let r := R/2
  have hr : 0 < r := half_pos hR
  have rr : r < R := half_lt_self hR
  obtain ⟨δ₁,h₁,p₁⟩ := radial_profile f 1 h hf vf (show 0 < r/4 by positivity)
  obtain ⟨δ₂,h₂,p₂⟩ := radial_profile g (n+1) h hg vg (show 0 < r/4 by positivity)
  let δ := min (min δ₁ δ₂) (r/4)
  refine ⟨δ,lt_min (lt_min h₁ h₂) (by positivity),?_⟩
  intro t ht htd a b ha hb
  have ts := lt_min_iff.mp htd
  have tr : t < R := by linarith [ts.2]
  have hp (p : Plane) (mem : p ∈ closedBall 0 r) := tube (show (t,p) ∈ ball (0 : ℝ × Plane) R by
    have pn : ‖p‖ < R := (show ‖p‖ ≤ r by simpa [mem_closedBall] using mem).trans_lt rr
    simp [mem_ball,abs_of_pos ht,tr,pn])
  have sur := fills_ball (F t) hr (by
    intro p mem
    obtain ⟨A,da,a₁,a₂⟩ := (hp p mem).1.1 ht
    obtain ⟨C,dc,c₁,c₂⟩ := (hp p mem).1.2 ht
    refine ⟨A.prod C,da.prodMk dc,?_,?_⟩
    · change max |A e₁-e₁.1| |C e₁-e₁.2| ≤ _
      exact max_le ((col₁ e₁) ▸ a₁) ((col₂ e₁) ▸ c₁)
    · change max |A e₂-e₂.1| |C e₂-e₂.2| ≤ _
      exact max_le ((col₁ e₂) ▸ a₂) ((col₂ e₂) ▸ c₂))
  have base : dist (F t 0) center < r/4 := by
    simpa [F,coord,center,Prod.dist_eq,Real.dist_eq] using And.intro
      (p₁ t ht (lt_min_iff.mp ts.1).1 h (by simpa using h₁))
      (p₂ t ht (lt_min_iff.mp ts.1).2 h (by simpa using h₂))
  have dest : dist (a,b) center < r/4 := by
    change max |a-_| |b-_| < _
    exact max_lt (ha.trans_le (min_le_right _ _)) (hb.trans_le (min_le_right _ _))
  obtain ⟨p,mem,eq⟩ := sur (show (a,b) ∈ closedBall (F t 0) (r/2) by
    apply mem_closedBall.mpr
    have tri := dist_triangle_right (a,b) (F t 0) center
    linarith)
  let x := t • (h+B p)
  have eq₁ : f x = t^2*a := ((div_eq_iff (pow_ne_zero 2 ht.ne')).mp (congrArg Prod.fst eq)).trans (mul_comm _ _)
  have eq₂ : g x = t^(n+2)*b := ((div_eq_iff (pow_ne_zero (n+2) ht.ne')).mp (congrArg Prod.snd eq)).trans (mul_comm _ _)
  have use := (hp p mem).2 ht
  change V (f x,g x) ≤ _ at use
  rwa [eq₁,eq₂] at use

private theorem open_box (n : ℕ) (f g cost : E → ℝ) (V : ℝ × ℝ → ℝ) (h : E) (B : (ℝ × ℝ) →L[ℝ] E)
    (hf : ContDiffAt ℝ 2 f 0) (hg : ContDiffAt ℝ (n+2 : ℕ) g 0) (hc : ContDiffAt ℝ 1 cost 0)
    (f0 : f 0 = 0) (f1 : fderiv ℝ f 0 = 0)
    (vg : ∀ j ≤ n+1, ∀ v : E, iteratedFDeriv ℝ j g 0 (fun _ => v) = 0)
    (dg : ∀ b : E, ∀ j ≤ n, ∀ v : E, iteratedFDeriv ℝ j (directional g b) 0 (fun _ => v) = 0)
    (col₁ : ∀ w, coeff (fun x => fderiv ℝ f x (B w)) 1 0 h = w.1)
    (col₂ : ∀ w, coeff (fun x => fderiv ℝ g x (B w)) (n+1) 0 h = w.2)
    (cz : cost 0 = 0) (down : coeff cost 1 0 h < 0)
    (competitors : ∀ᶠ x in 𝓝 0, V (f x,g x) ≤ V 0 + cost x) :
    ∃ c > 0, ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ → ∀ a b : ℝ,
      |a-coeff f 2 0 h| < δ → |b-coeff g (n+2) 0 h| < δ →
      V (t^2*a,t^(n+2)*b) ≤ V 0 - c*t := by
  let c := -(coeff cost 1 0 h)/2
  have pos : 0 < c := by dsimp [c]; linarith
  have costFlat : ∀ j ≤ 0, ∀ v : E, iteratedFDeriv ℝ j cost 0 (fun _ => v) = 0 := by
    intro j hj v
    obtain rfl : j = 0 := by omega
    simp [cz]
  have nearCost := near_profile cost 0 h B hc costFlat pos
  have co : Continuous (fun p : ℝ × Plane => p.1 • (h+B p.2)) :=
    continuous_fst.smul (continuous_const.add (B.continuous.comp continuous_snd))
  have to0 : Tendsto (fun p : ℝ × Plane => p.1 • (h+B p.2)) (𝓝 0) (𝓝 0) := by simpa using co.tendsto 0
  refine ⟨c,pos,open_box_of_cone n f g V h B hf hg f0 f1 vg dg col₁ col₂ c ?_⟩
  filter_upwards [nearCost,to0 competitors] with p profile comp
  intro ht
  let x := p.1 • (h+B p.2)
  have save := (abs_lt.mp (profile ht)).2
  change cost x/p.1^(0+1) - coeff cost 1 0 h < c at save
  rw [zero_add,pow_one] at save
  have val : cost x/p.1 < -c := by dsimp [c] at *; linarith
  change V (f x,g x) ≤ V 0 + cost x at comp
  linarith [(div_lt_iff₀ ht).mp val]

/-- An open box of scaled endpoints when the limiting two columns of
the normalized Jacobian are the two coordinate vectors. -/
theorem mixed_box (f g cost : E → ℝ) (V : ℝ × ℝ → ℝ) (h : E) (B : (ℝ × ℝ) →L[ℝ] E)
    (hf : ContDiffAt ℝ 2 f 0) (hg : ContDiffAt ℝ 3 g 0) (hc : ContDiffAt ℝ 1 cost 0)
    (f0 : f 0 = 0) (f1 : fderiv ℝ f 0 = 0) (g0 : g 0 = 0)
    (g1 : fderiv ℝ g 0 = 0) (g2 : fderiv ℝ (fderiv ℝ g) 0 = 0)
    (col₁ : ∀ w, coeff (fun x => fderiv ℝ f x (B w)) 1 0 h = w.1)
    (col₂ : ∀ w, coeff (fun x => fderiv ℝ g x (B w)) 2 0 h = w.2)
    (cz : cost 0 = 0) (down : coeff cost 1 0 h < 0)
    (competitors : ∀ᶠ x in 𝓝 0, V (f x,g x) ≤ V 0 + cost x) :
    ∃ c > 0, ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ → ∀ a b : ℝ,
      |a-coeff f 2 0 h| < δ → |b-coeff g 3 0 h| < δ →
      V (t^2*a,t^3*b) ≤ V 0 - c*t := by
  have vg : ∀ j ≤ 2, ∀ v : E, iteratedFDeriv ℝ j g 0 (fun _ => v) = 0 := by
    intro j hj v
    interval_cases j <;> simp [g0,g1,g2,iteratedFDeriv_two_apply]
  apply open_box 1 f g cost V h B hf hg hc f0 f1 vg _ col₁ col₂ cz down competitors
  intro b j hj v
  have df := ((hg.fderiv_right (m := 1) (by decide)).differentiableAt le_rfl).hasFDerivAt.clm_apply
    (hasFDerivAt_const (𝕜 := ℝ) b (0:E))
  have dz : fderiv ℝ (directional g b) 0 = 0 := by
    change fderiv ℝ (fun x => (fderiv ℝ g x) b) 0 = 0
    rw [df.fderiv,g1,g2]
    ext
    simp
  interval_cases j
  · simp [directional,g1]
  · simp [dz]

/-- The row of the normalized Jacobian, as a linear map in the column. -/
def polarRow (f : E → ℝ) (n : ℕ) (h : E) : E →L[ℝ] ℝ :=
  (n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n (fderiv ℝ f) 0 (fun _ => h)

private theorem polarRow_apply (f : E → ℝ) (n : ℕ) (hf : ContDiffAt ℝ (n+1 : ℕ) f 0)
    (h b : E) : coeff (fun x => fderiv ℝ f x b) n 0 h = polarRow f n h b := by
  have reg := hf.fderiv_right (m := (n : WithTop ℕ∞)) (by simp)
  obtain ⟨U,uo,h0,smooth⟩ := reg.contDiffOn' le_rfl (by simp)
  simp at smooth
  have eq := iteratedFDerivWithin_clm_apply_const_apply uo.uniqueDiffOn smooth
    (i := n) le_rfl h0 (u := b) (m := fun _ => h)
  rw [iteratedFDerivWithin_of_isOpen n uo h0,iteratedFDerivWithin_of_isOpen n uo h0] at eq
  simp [coeff,polarRow,eq,div_eq_inv_mul]

private theorem regular_descent (n : ℕ) (f g cost : E → ℝ) (v a b : E)
    (reg : polarRow f 1 v a * polarRow g n v b ≠ polarRow f 1 v b * polarRow g n v a)
    (strict : fderiv ℝ cost 0 ≠ 0) :
    ∃ h, coeff cost 1 0 h < 0 ∧
      polarRow f 1 h a * polarRow g n h b ≠ polarRow f 1 h b * polarRow g n h a := by
  let L := fderiv ℝ cost 0
  let minor (h : E) := polarRow f 1 h a * polarRow g n h b - polarRow f 1 h b * polarRow g n h a
  have cont (F : E → ℝ) (n : ℕ) (w : E) : Continuous (fun h => polarRow F n h w) := by
    unfold polarRow
    simp only [ContinuousLinearMap.smul_apply,smul_eq_mul]
    exact continuous_const.mul ((ContinuousLinearMap.apply ℝ ℝ w).continuous.comp
      ((iteratedFDeriv ℝ n (fderiv ℝ F) 0).cont.comp (continuous_pi fun _ => continuous_id)))
  have cm : Continuous minor := ((cont f 1 a).mul (cont g n b)).sub ((cont f 1 b).mul (cont g n a))
  have flip (F : E → ℝ) (n : ℕ) (h w : E) :
      polarRow F n (-h) w = (-1:ℝ)^n * polarRow F n h w := by
    have eq := (iteratedFDeriv ℝ n (fderiv ℝ F) 0).map_smul_univ (fun _ => (-1:ℝ)) (fun _ => h)
    simp at eq
    simp [polarRow,eq]
    ring
  have take (h : E) (m : minor h ≠ 0) (lh : L h ≠ 0) :
      ∃ z, coeff cost 1 0 z < 0 ∧
        polarRow f 1 z a * polarRow g n z b ≠ polarRow f 1 z b * polarRow g n z a := by
    rcases lt_or_gt_of_ne lh with neg | pos
    · exact ⟨h,by simpa [coeff,L] using neg,sub_ne_zero.mp m⟩
    · refine ⟨-h,by simpa [coeff,L] using neg_neg_of_pos pos,?_⟩
      have nonzero : (-1:ℝ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
      intro eq
      simp only [flip,pow_one] at eq
      apply sub_ne_zero.mp m
      apply mul_left_cancel₀ nonzero
      linarith only [eq]
  have mv : minor v ≠ 0 := sub_ne_zero.mpr reg
  by_cases lv : L v = 0
  · have ex : ∃ u, L u ≠ 0 := by
      by_contra! all
      exact strict (ContinuousLinearMap.ext fun u => all u)
    obtain ⟨u,hu⟩ := ex
    have tend : ContinuousAt (fun s : ℝ => minor (v+s • u)) 0 :=
      cm.continuousAt.comp (continuousAt_const.add (continuousAt_id.smul continuousAt_const))
    have event : ∀ᶠ s : ℝ in 𝓝 0, minor (v+s • u) ≠ 0 :=
      tend.eventually_ne (by simpa using mv)
    obtain ⟨r,hr,good⟩ := Metric.mem_nhds_iff.mp event
    let s := r/2
    have hs : 0 < s := half_pos hr
    have sr : s < r := half_lt_self hr
    exact take (v+s • u) (good (by simpa [mem_ball,abs_of_pos hs] using sr))
      (by simp [lv,hs.ne',hu])
  · exact take v mv lv

private theorem normalized_columns (P Q : E →L[ℝ] ℝ) (a b : E)
    (rh : P a * Q b ≠ P b * Q a) :
    ∃ B : Plane →L[ℝ] E, (∀ w : Plane, P (B w) = w.1) ∧ (∀ w : Plane, Q (B w) = w.2) := by
  let d := P a * Q b - P b * Q a
  have hd : d ≠ 0 := sub_ne_zero.mpr rh
  let x := d⁻¹ • (Q b • a - Q a • b)
  let y := d⁻¹ • (P a • b - P b • a)
  have px : P x = 1 := by
    simp only [x,map_smul,map_sub,smul_eq_mul]
    rw [mul_comm (Q b),mul_comm (Q a)]
    exact inv_mul_cancel₀ hd
  have qx : Q x = 0 := by simp [x,smul_eq_mul,mul_comm]
  have py : P y = 0 := by simp [y,smul_eq_mul,mul_comm]
  have qy : Q y = 1 := by
    simp only [y,map_smul,map_sub,smul_eq_mul]
    exact inv_mul_cancel₀ hd
  let B := (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight x + (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight y
  have col (w : Plane) : B w = w.1 • x + w.2 • y := rfl
  exact ⟨B,fun w => by simp [col,px,py],fun w => by simp [col,qx,qy]⟩

/-- A single independent pair anywhere and a nonzero cost differential
suffice for a full box. The control plane is constructed from that pair. -/
theorem cubic_box_from_reduced_jets (f g cost : E → ℝ) (V : ℝ × ℝ → ℝ)
    (hf : ContDiffAt ℝ 2 f 0) (hg : ContDiffAt ℝ 3 g 0) (hc : ContDiffAt ℝ 1 cost 0)
    (f0 : f 0 = 0) (f1 : fderiv ℝ f 0 = 0) (g0 : g 0 = 0)
    (g1 : fderiv ℝ g 0 = 0) (g2 : fderiv ℝ (fderiv ℝ g) 0 = 0)
    (rank : ∃ v a b, polarRow f 1 v a * polarRow g 2 v b ≠ polarRow f 1 v b * polarRow g 2 v a)
    (cz : cost 0 = 0) (strict : fderiv ℝ cost 0 ≠ 0)
    (competitors : ∀ᶠ x in 𝓝 0, V (f x,g x) ≤ V 0 + cost x) :
    ∃ A B c : ℝ, 0 < c ∧ ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ → ∀ a b : ℝ,
      |a-A| < δ → |b-B| < δ → V (t^2*a,t^3*b) ≤ V 0 - c*t := by
  obtain ⟨v,a,b,rk⟩ := rank
  obtain ⟨h,down,rh⟩ := regular_descent 2 f g cost v a b rk strict
  obtain ⟨B,p₁,p₂⟩ := normalized_columns _ _ a b rh
  apply Exists.intro _
  apply Exists.intro _
  apply mixed_box f g cost V h B hf hg hc f0 f1 g0 g1 g2 _ _ cz down competitors
  · intro w
    rw [polarRow_apply f 1 hf]
    exact p₁ w
  · intro w
    rw [polarRow_apply g 2 hg]
    exact p₂ w

#print axioms cubic_box_from_reduced_jets
#print axioms mixed_box

/-- Before choosing a third-layer axis, full rank of the quadratic
polar pair already gives an ordinary quadratic box on fixed axes. -/
theorem quadratic_box_from_reduced_jets (f g cost : E → ℝ) (V : ℝ × ℝ → ℝ)
    (hf : ContDiffAt ℝ 2 f 0) (hg : ContDiffAt ℝ 2 g 0) (hc : ContDiffAt ℝ 1 cost 0)
    (f0 : f 0 = 0) (f1 : fderiv ℝ f 0 = 0) (g0 : g 0 = 0) (g1 : fderiv ℝ g 0 = 0)
    (rank : ∃ v a b, polarRow f 1 v a * polarRow g 1 v b ≠ polarRow f 1 v b * polarRow g 1 v a)
    (cz : cost 0 = 0) (strict : fderiv ℝ cost 0 ≠ 0)
    (competitors : ∀ᶠ x in 𝓝 0, V (f x,g x) ≤ V 0 + cost x) :
    ∃ A B c : ℝ, 0 < c ∧ ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ → ∀ a b : ℝ,
      |a-A| < δ → |b-B| < δ → V (t^2*a,t^2*b) ≤ V 0-c*t := by
  obtain ⟨v,a,b,rk⟩ := rank
  obtain ⟨h,down,rh⟩ := regular_descent 1 f g cost v a b rk strict
  obtain ⟨B,p₁,p₂⟩ := normalized_columns _ _ a b rh
  refine ⟨_,_,open_box 0 f g cost V h B hf hg hc f0 f1 ?_ ?_ ?_ ?_ cz down competitors⟩
  · intro j hj w
    interval_cases j <;> simp [g0,g1]
  · intro w j hj z
    obtain rfl : j = 0 := by omega
    simp [directional,g1]
  · intro w
    exact (polarRow_apply f 1 hf h (B w)).trans (p₁ w)
  · intro w
    exact (polarRow_apply g 1 hg h (B w)).trans (p₂ w)

#print axioms quadratic_box_from_reduced_jets

/-- An open set of strictly descending directions suffices even if the cost
has no derivative. A nonzero quadratic minor is nonzero somewhere in this set. -/
theorem quadratic_box_from_descent_cones (f g : E → ℝ) (V : ℝ × ℝ → ℝ)
    (hf : ContDiffAt ℝ 2 f 0) (hg : ContDiffAt ℝ 2 g 0)
    (f0 : f 0 = 0) (f1 : fderiv ℝ f 0 = 0) (g0 : g 0 = 0) (g1 : fderiv ℝ g 0 = 0)
    (v a b : E)
    (rank : fderiv ℝ (fderiv ℝ f) 0 v a * fderiv ℝ (fderiv ℝ g) 0 v b ≠
      fderiv ℝ (fderiv ℝ f) 0 v b * fderiv ℝ (fderiv ℝ g) 0 v a)
    (O : Set E) (ho : IsOpen O) (ne : O.Nonempty)
    (cone : ∀ h ∈ O, ∀ B : Plane →L[ℝ] E, ∃ c > 0, ∀ᶠ p : ℝ × Plane in 𝓝 0,
      0 < p.1 → V (f (p.1 • (h+B p.2)),g (p.1 • (h+B p.2))) ≤ V 0-c*p.1) :
    ∃ A B c : ℝ, 0 < c ∧ ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ → ∀ a b : ℝ,
      |a-A| < δ → |b-B| < δ → V (t^2*a,t^2*b) ≤ V 0-c*t := by
  let P := fderiv ℝ (fderiv ℝ f) 0
  let Q := fderiv ℝ (fderiv ℝ g) 0
  let D (u : E) := P u a * Q u b - P u b * Q u a
  have dv : D v ≠ 0 := sub_ne_zero.mpr rank
  obtain ⟨d,hd⟩ := ne
  have existsReg : ∃ h ∈ O, D h ≠ 0 := by
    by_contra! vanish
    have plus : Continuous (fun s : ℝ => d + s • v) := continuous_const.add (continuous_id.smul continuous_const)
    have minus : Continuous (fun s : ℝ => d - s • v) := continuous_const.sub (continuous_id.smul continuous_const)
    have near (sgn : ℝ → E) (hc : Continuous sgn) (hz : sgn 0 = d) :
        ∀ᶠ s in 𝓝[>] (0:ℝ), sgn s ∈ O :=
      (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) (ho.mem_nhds (hz ▸ hd))
    have spos : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < s := self_mem_nhdsWithin
    obtain ⟨s,hs,hp,hm⟩ := (spos.and
      ((near _ plus (by simp)).and (near _ minus (by simp)))).exists
    have diff : D (d+s • v) + D (d-s • v) - 2*D d = 2*s^2*D v := by
      simp only [D,map_add,map_sub,map_smul,ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.smul_apply,smul_eq_mul]
      ring
    rw [vanish _ hp,vanish _ hm,vanish _ hd] at diff
    have hn : s ≠ 0 := ne_of_gt hs
    exact (mul_ne_zero (mul_ne_zero (two_ne_zero : (2:ℝ) ≠ 0) (pow_ne_zero 2 hn)) dv) (by linarith)
  obtain ⟨h,hh,dh⟩ := existsReg
  obtain ⟨B,p₁,p₂⟩ := normalized_columns (P h) (Q h) a b (sub_ne_zero.mp dh)
  obtain ⟨c,cp,save⟩ := cone h hh B
  refine ⟨_,_,c,cp,open_box_of_cone 0 f g V h B hf hg f0 f1 ?_ ?_ ?_ ?_ c save⟩
  · intro j hj w
    interval_cases j <;> simp [g0,g1]
  · intro w j hj z
    obtain rfl : j = 0 := by omega
    simp [directional,g1]
  · intro w
    exact (polarRow_apply f 1 hf h (B w)).trans (by simpa [polarRow,P] using p₁ w)
  · intro w
    exact (polarRow_apply g 1 hg h (B w)).trans (by simpa [polarRow,Q] using p₂ w)

#print axioms quadratic_box_from_descent_cones

private theorem third_symmetric_last (g : E → ℝ) (hg : ContDiffAt ℝ 3 g 0) (a b c : E) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ g)) 0 a b c =
      fderiv ℝ (fderiv ℝ (fderiv ℝ g)) 0 a c b := by
  let H := fderiv ℝ (fderiv ℝ g)
  have dH : DifferentiableAt ℝ H 0 :=
    ((hg.fderiv_right (m := 2) (by decide)).fderiv_right (m := 1) (by decide)).differentiableAt le_rfl
  have eq : (fun x => H x b c) =ᶠ[𝓝 0] (fun x => H x c b) :=
    (hg.eventually (by decide)).mono fun x hx => (hx.of_le (show (2 : WithTop ℕ∞) ≤ 3 by decide)).isSymmSndFDerivAt (by simp) b c
  have evalD (u v : E) :
      fderiv ℝ (fun x => H x u v) 0 a = fderiv ℝ H 0 a u v := by
    let U := ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) u
    let V := ContinuousLinearMap.apply ℝ ℝ v
    have deriv := DifferentiableAt.hasFDerivAt (𝕜 := ℝ) (f := H) (x := 0) dH
    have first := (U.hasFDerivAt (x := H 0)).comp 0 deriv
    have second := (V.hasFDerivAt (x := U (H 0))).comp 0 first
    exact DFunLike.congr_fun second.fderiv a
  rw [← evalD b c,← evalD c b,eq.fderiv_eq]

/-- Dependence of the actual normalized endpoint rows forces vanishing
of the diagonal third jet, provided the quadratic row has rank at least two. -/
theorem third_jet_zero_of_dependent_rows (f g : E → ℝ) (hf : ContDiffAt ℝ 2 f 0)
    (hg : ContDiffAt ℝ 3 g 0)
    (rank : ∃ a b c d, polarRow f 1 a c * polarRow f 1 b d ≠ polarRow f 1 a d * polarRow f 1 b c)
    (dep : ∀ h a b, polarRow f 1 h a * polarRow g 2 h b = polarRow f 1 h b * polarRow g 2 h a) :
    ∀ x : E, iteratedFDeriv ℝ 3 g 0 (fun _ => x) = 0 := by
  let A := fderiv ℝ (fderiv ℝ f) 0
  let T := fderiv ℝ (fderiv ℝ (fderiv ℝ g)) 0
  let C : E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
    { toFun := fun x => (T x).toLinearMap₁₂
      map_add' := by intro x y; ext a b; simp
      map_smul' := by intro t x; ext a b; simp }
  have p (h a : E) : polarRow f 1 h a = A h a := by simp [polarRow,A]
  have q (h b : E) : polarRow g 2 h b = (2:ℝ)⁻¹ * T h h b := by
    simp [polarRow,T,iteratedFDeriv_two_apply,show Nat.factorial 2 = 2 from rfl]
  have syA : ∀ v w, A v w = A w v := hf.isSymmSndFDerivAt (by simp)
  have syT := (hg.fderiv_right (m := 2) (by decide)).isSymmSndFDerivAt (by simp)
  have result := MinimizingSard.Jets.cubic_zero_of_dependent_polars A.toLinearMap₁₂ C syA
    (fun x y z => DFunLike.congr_fun (syT x y) z)
    (third_symmetric_last g hg)
    (by simpa only [p,ContinuousLinearMap.toLinearMap₁₂_apply] using rank)
    (by
      intro h a b
      change A h a * T h h b = A h b * T h h a
      have use := dep h a b
      simp only [p,q] at use
      linarith)
  intro x
  rw [iteratedFDeriv_succ_apply_right,iteratedFDeriv_two_apply]
  exact result x

/-- The two analytic cases exhaust the normalized endpoint jets. -/
theorem descent_box_from_reduced_jets (f g cost : E → ℝ) (V : ℝ × ℝ → ℝ)
    (hf : ContDiffAt ℝ 2 f 0) (hg : ContDiffAt ℝ 4 g 0) (hc : ContDiffAt ℝ 1 cost 0)
    (f0 : f 0 = 0) (f1 : fderiv ℝ f 0 = 0) (g0 : g 0 = 0)
    (g1 : fderiv ℝ g 0 = 0) (g2 : fderiv ℝ (fderiv ℝ g) 0 = 0)
    (rank : ∃ a b c d, polarRow f 1 a c * polarRow f 1 b d ≠ polarRow f 1 a d * polarRow f 1 b c)
    (cz : cost 0 = 0) (strict : fderiv ℝ cost 0 ≠ 0)
    (competitors : ∀ᶠ x in 𝓝 0, V (f x,g x) ≤ V 0 + cost x)
    (K : ℝ) (holder : ∀ᶠ p : ℝ × ℝ × ℝ in 𝓝 0,
       V (p.1,p.2.1) ≤ V (p.1,p.2.2) + K * |p.2.1-p.2.2|^(1/4:ℝ)) :
    ∃ k : ℕ, (k = 3 ∨ k = 4) ∧ ∃ A B c : ℝ, 0 < c ∧ ∃ δ > 0,
      ∀ t : ℝ, 0 < t → t < δ → ∀ a b : ℝ,
      |a-A| < δ → |b-B| < δ → V (t^2*a,t^k*b) ≤ V 0 - c*t := by
  by_cases reg : ∃ v a b, polarRow f 1 v a * polarRow g 2 v b ≠ polarRow f 1 v b * polarRow g 2 v a
  · exact ⟨3,Or.inl rfl,cubic_box_from_reduced_jets f g cost V hf (hg.of_le (by decide)) hc
      f0 f1 g0 g1 g2 reg cz strict competitors⟩
  · push_neg at reg
    have flat := third_jet_zero_of_dependent_rows f g hf (hg.of_le (by decide)) rank reg
    have quad : fderiv ℝ (fderiv ℝ f) 0 ≠ 0 := by
      intro eq
      obtain ⟨a,b,c,d,ne⟩ := rank
      exact ne (by simp [polarRow,eq])
    refine ⟨4,Or.inr rfl,quartic_box_from_reduced_jets f g cost V hf hg hc ?_ ?_ quad cz strict competitors K holder⟩
    · intro j hj v
      interval_cases j <;> simp [f0,f1]
    · intro j hj v
      interval_cases j <;> simp [g0,g1,g2,iteratedFDeriv_two_apply,flat]

#print axioms third_jet_zero_of_dependent_rows
#print axioms descent_box_from_reduced_jets

/-- A regular cubic minor at a shortening direction fills the cubic box
using a uniform saving on the two-column family. -/
theorem cubic_box_of_regular_cone (f g : E → ℝ) (V : ℝ × ℝ → ℝ) (h a b : E)
    (hf : ContDiffAt ℝ 2 f 0) (hg : ContDiffAt ℝ 3 g 0)
    (f0 : f 0 = 0) (f1 : fderiv ℝ f 0 = 0) (g0 : g 0 = 0)
    (g1 : fderiv ℝ g 0 = 0) (g2 : fderiv ℝ (fderiv ℝ g) 0 = 0)
    (rk : polarRow f 1 h a * polarRow g 2 h b ≠ polarRow f 1 h b * polarRow g 2 h a)
    (save : ∀ B : Plane →L[ℝ] E, ∃ c > 0, ∀ᶠ p : ℝ × Plane in 𝓝 0, 0 < p.1 →
      V (f (p.1 • (h+B p.2)),g (p.1 • (h+B p.2))) ≤ V 0-c*p.1) :
    ∃ c > 0, ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ → ∀ a b : ℝ,
      |a-coeff f 2 0 h| < δ → |b-coeff g 3 0 h| < δ → V (t^2*a,t^3*b) ≤ V 0-c*t := by
  obtain ⟨B,p₁,p₂⟩ := normalized_columns _ _ a b rk
  obtain ⟨c,cp,cone⟩ := save B
  refine ⟨c,cp,open_box_of_cone 1 f g V h B hf hg f0 f1 ?_ ?_ ?_ ?_ c cone⟩
  · intro j hj v
    interval_cases j <;> simp [g0,g1,g2,iteratedFDeriv_two_apply]
  · intro w j hj v
    have df := ((hg.fderiv_right (m := 1) (by decide)).differentiableAt le_rfl).hasFDerivAt.clm_apply
      (hasFDerivAt_const (𝕜 := ℝ) w (0:E))
    have dz : fderiv ℝ (directional g w) 0 = 0 := by
      change fderiv ℝ (fun x => (fderiv ℝ g x) w) 0 = 0
      rw [df.fderiv,g1,g2]
      ext
      simp
    interval_cases j
    · simp [directional,g1]
    · simp [dz]
  · intro w
    exact (polarRow_apply f 1 hf h (B w)).trans (p₁ w)
  · intro w
    exact (polarRow_apply g 2 hg h (B w)).trans (p₂ w)

#print axioms cubic_box_of_regular_cone
end MinimizingSard.Return
