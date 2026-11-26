import QuarticReturn
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace MinimizingSard.Five
private abbrev Pair := ℝ × ℝ

/-- A one-sided Taylor quotient, continuously filled at its base point. -/
theorem ray_profile (f : ℝ → ℝ) (n : ℕ) (hf : ContDiffAt ℝ (n+1 : ℕ) f 0)
    (van : ∀ j ≤ n, ∀ v : ℝ, iteratedFDeriv ℝ j f 0 (fun _ => v) = 0) :
    ∃ F : ℝ → ℝ, ContinuousAt F 0 ∧ F 0 = Return.coeff f (n+1) 0 1 ∧
      ∀ t > 0, f t = t^(n+1)*F t := by
  let a := Return.coeff f (n+1) 0 1
  let F (t : ℝ) := if 0 < t then f t/t^(n+1) else a
  refine ⟨F,?_,by simp [F,a],?_⟩
  · apply Metric.continuousAt_iff.mpr
    intro ε he
    obtain ⟨δ,hδ,lim⟩ := Return.radial_profile f n 1 hf van he
    refine ⟨δ,hδ,?_⟩
    intro t ht
    by_cases pos : 0 < t
    · simpa [F,pos,Real.dist_eq,a] using lim t pos (by simpa [Real.dist_eq,abs_of_pos pos] using ht) 1 (by simpa using hδ)
    · simpa [F,pos] using he
  · intro t ht
    simp [F,ht,mul_div_cancel₀,(pow_pos ht (n+1)).ne']

/-- A thick rectangle along a shrinking ray yields a fixed descent box
when its transverse coordinate first appears at the third order. -/
theorem cubic_ray_box (V : Pair → ℝ) (F G : ℝ → ℝ) (c : ℝ)
    (cf : ContinuousAt F 0) (cg : ContinuousAt G 0)
    (save : ∀ᶠ p : ℝ × Pair in 𝓝 0, 0 < p.1 →
      V (p.1^2*(F p.1+p.2.1),p.1^3*(G p.1+p.2.2)) ≤ V 0-c*p.1) :
    ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ → ∀ a b : ℝ, |a-F 0| < δ → |b-G 0| < δ →
      V (t^2*a,t^3*b) ≤ V 0-c*t := by
  let T (p : ℝ × Pair) := (p.1,p.2.1-F p.1,p.2.2-G p.1)
  let base : ℝ × Pair := (0,F 0,G 0)
  have ct : ContinuousAt T base := continuousAt_fst.prodMk
    (((continuous_fst.comp continuous_snd).continuousAt.sub (cf.comp (f := (Prod.fst : ℝ × Pair → ℝ)) continuousAt_fst)).prodMk
      ((continuous_snd.comp continuous_snd).continuousAt.sub (cg.comp (f := (Prod.fst : ℝ × Pair → ℝ)) continuousAt_fst)))
  have t0 : T base = 0 := by simp [T,base]
  obtain ⟨δ,hδ,ball⟩ := Metric.mem_nhds_iff.mp ((t0 ▸ ct.tendsto) save)
  refine ⟨δ,hδ,?_⟩
  intro t ht st a b ha hb
  have h := ball (show (t,a,b) ∈ Metric.ball base δ by simpa [base,Metric.mem_ball,Prod.dist_eq,Real.dist_eq,abs_of_pos ht] using ⟨st,ha,hb⟩) ht
  simpa [T] using h

/-- Along a ray with nonzero transverse quadratic coefficient, varying
the traversal time fills a square. Only the first coordinate needs an
order-two lateral motion. -/
theorem square_ray_box (V : Pair → ℝ) (g F G : ℝ → ℝ) {c : ℝ} (cp : 0 < c)
    (cf : ContinuousAt F 0) (cg : ContinuousAt G 0) (nz : G 0 ≠ 0)
    (gc : ∀ᶠ t in 𝓝 0, ContinuousAt g t) (expand : ∀ t > 0, g t = t^2*G t)
    (save : ∀ᶠ p : Pair in 𝓝 0, 0 < p.1 →
      V (p.1^2*(F p.1+p.2),g p.1) ≤ V 0-c*p.1) :
    ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ → ∀ a b : ℝ, |a-F 0| < δ → |b-G 0| < δ →
      V (t^2*a,t^2*b) ≤ V 0-(c/2)*t := by
  let base : ℝ × Pair := (0,1,F 0)
  let T (p : ℝ × Pair) : Pair := (p.1*p.2.1,p.2.2/p.2.1^2-F (p.1*p.2.1))
  have ct : ContinuousAt T base := by
    have m : ContinuousAt (fun p : ℝ × Pair => p.1*p.2.1) base := by fun_prop
    have fc : ContinuousAt (fun p : ℝ × Pair => F (p.1*p.2.1)) base :=
      (show ContinuousAt F (base.1*base.2.1) by simpa [base] using cf).comp (f := fun p : ℝ × Pair => p.1*p.2.1) m
    apply m.prodMk
    exact (((continuous_snd.comp continuous_snd).continuousAt.div
      ((continuous_fst.comp continuous_snd).continuousAt.pow 2) (by norm_num [base])).sub fc)
  have t0 : T base = 0 := by simp [base,T]
  have gc' : ∀ᶠ p : ℝ × Pair in 𝓝 base, ContinuousAt g (p.1*p.2.1) :=
    (show Tendsto (fun p : ℝ × Pair => p.1*p.2.1) (𝓝 base) (𝓝 0) by
      have h : Continuous (fun p : ℝ × Pair => p.1*p.2.1) := by fun_prop
      simpa [base] using h.tendsto base) gc
  have uses : ∀ᶠ p : ℝ × Pair in 𝓝 base, 0 < (T p).1 →
      V ((T p).1^2*(F (T p).1+(T p).2),g (T p).1) ≤ V 0-c*(T p).1 := (t0 ▸ ct.tendsto) save
  obtain ⟨R,rp,ball⟩ := Metric.mem_nhds_iff.mp (uses.and gc')
  obtain ⟨d,dp,dr,dh⟩ : ∃ d : ℝ, 0 < d ∧ d < R ∧ d < 1/2 :=
    exists_between (lt_min rp (by norm_num : (0:ℝ)<1/2)) |>.imp (fun d h => ⟨h.1,(lt_min_iff.mp h.2).1,(lt_min_iff.mp h.2).2⟩)
  let l := 1-d
  let r := 1+d
  have lp : 0 < l := by dsimp [l]; linarith
  have lr : l < r := by dsimp [l,r]; linarith
  have sides : G 0 ∈ uIoo (l^2*G 0) (r^2*G 0) := by
    have sl : l^2 < 1 := by dsimp [l]; nlinarith
    have sr : 1 < r^2 := by dsimp [r]; nlinarith
    rcases lt_or_gt_of_ne nz with neg | pos
    · rw [uIoo_of_ge (by nlinarith [mul_neg_of_neg_of_pos neg (sub_pos.mpr (sl.trans sr))] : r^2*G 0 ≤ l^2*G 0)]
      exact ⟨by nlinarith [mul_neg_of_neg_of_pos neg (sub_pos.mpr sr)], by nlinarith [mul_neg_of_neg_of_pos neg (sub_pos.mpr sl)]⟩
    · rw [uIoo_of_le (by nlinarith [mul_pos pos (sub_pos.mpr (sl.trans sr))] : l^2*G 0 ≤ r^2*G 0)]
      exact ⟨by nlinarith [mul_pos pos (sub_pos.mpr sl)],by nlinarith [mul_pos pos (sub_pos.mpr sr)]⟩
  let H (s t : ℝ) := s^2*G (t*s)
  have ch (s : ℝ) : ContinuousAt (H s) 0 := continuousAt_const.mul
    ((show ContinuousAt G (0*s) by simpa using cg).comp (f := fun t : ℝ => t*s) (continuousAt_id.mul continuousAt_const))
  have near : ∀ᶠ p : Pair in 𝓝 (0,G 0), p.2 ∈ uIcc (H l p.1) (H r p.1) := by
    have low : ContinuousAt (fun p : Pair => min (H l p.1) (H r p.1)) (0,G 0) :=
      ((ch l).comp (f := (Prod.fst : Pair → ℝ)) (x := ((0:ℝ),G 0)) continuousAt_fst).min ((ch r).comp (f := (Prod.fst : Pair → ℝ)) (x := ((0:ℝ),G 0)) continuousAt_fst)
    have high : ContinuousAt (fun p : Pair => max (H l p.1) (H r p.1)) (0,G 0) :=
      ((ch l).comp (f := (Prod.fst : Pair → ℝ)) (x := ((0:ℝ),G 0)) continuousAt_fst).max ((ch r).comp (f := (Prod.fst : Pair → ℝ)) (x := ((0:ℝ),G 0)) continuousAt_fst)
    have lo := low.eventually_lt (g := Prod.snd) continuousAt_snd (by simpa [H] using sides.1)
    have hi := continuousAt_snd.eventually_lt high (by simpa [H] using sides.2)
    filter_upwards [lo,hi] with p h k using ⟨h.le,k.le⟩
  obtain ⟨R',rp',hit⟩ := Metric.mem_nhds_iff.mp near
  refine ⟨min R R',lt_min rp rp',?_⟩
  intro t ht td a b ha hb
  have localBound (s : ℝ) (hs : s ∈ Icc l r) : (t,s,a) ∈ Metric.ball base R := by
    dsimp [l,r] at hs
    have ds : |s-1| < R := abs_lt.mpr ⟨by linarith [hs.1],by linarith [hs.2]⟩
    simpa [base,Metric.mem_ball,Prod.dist_eq,Real.dist_eq,abs_of_pos ht] using
      And.intro (lt_min_iff.mp td).1 (And.intro ds (lt_min_iff.mp ha).1)
  have cs : ContinuousOn (fun s : ℝ => g (t*s)/t^2) (uIcc l r) := by
    rw [uIcc_of_le lr.le]
    intro s hs
    exact (((ball (localBound s hs)).2.comp (f := fun s : ℝ => t*s) (continuousAt_const.mul continuousAt_id)).div_const _).continuousWithinAt
  have val (s : ℝ) (pos : 0 < s) : g (t*s)/t^2 = H s t := by
    rw [expand _ (mul_pos ht pos)]
    dsimp [H]
    field_simp
  have inRange := hit (show (t,b) ∈ Metric.ball (0,G 0) R' by
    simpa [Metric.mem_ball,Prod.dist_eq,Real.dist_eq,abs_of_pos ht] using And.intro (lt_min_iff.mp td).2 (lt_min_iff.mp hb).2)
  change b ∈ uIcc (H l t) (H r t) at inRange
  rw [← val l lp,← val r (lp.trans lr)] at inRange
  obtain ⟨s,hs,eq⟩ := intermediate_value_uIcc cs inRange
  rw [uIcc_of_le lr.le] at hs
  have sp := lp.trans_le hs.1
  have saved := (ball (localBound s hs)).1 (mul_pos ht sp)
  have first : (t*s)^2*(F (t*s)+(a/s^2-F (t*s))) = t^2*a := by field_simp; ring
  have second : g (t*s) = t^2*b := ((div_eq_iff (pow_ne_zero 2 ht.ne')).mp eq).trans (mul_comm _ _)
  change V ((t*s)^2*(F (t*s)+(a/s^2-F (t*s))),g (t*s)) ≤ _ at saved
  rw [first,second] at saved
  have half : 1/2 ≤ s := by dsimp [l] at hs; linarith [hs.1]
  exact saved.trans (by nlinarith only [mul_le_mul_of_nonneg_left half (mul_pos cp ht).le])

#print axioms ray_profile
#print axioms cubic_ray_box
#print axioms square_ray_box

/-- The two possible fixed boxes for a single smooth shortened arc.
The attainable perturbations have widths of order two and three. -/
theorem box_of_shortened_ray (V : Pair → ℝ) (f g : ℝ → ℝ) {c : ℝ} (cp : 0 < c)
    (cf : ContDiffAt ℝ 3 f 0) (cg : ContDiffAt ℝ 3 g 0) (f0 : f 0 = 0) (g0 : g 0 = 0)
    (df : fderiv ℝ f 0 = 0) (dg : fderiv ℝ g 0 = 0)
    (save : ∀ᶠ p : ℝ × Pair in 𝓝 0, 0 < p.1 →
      V (f p.1+p.1^2*p.2.1,g p.1+p.1^3*p.2.2) ≤ V 0-c*p.1) :
    ∃ k : ℕ, (k = 2 ∨ k = 3) ∧ ∃ A B σ : ℝ, 0 < σ ∧ ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
      ∀ a b : ℝ, |a-A| < δ → |b-B| < δ → V (t^2*a,t^k*b) ≤ V 0-σ*t := by
  have flat (h : ℝ → ℝ) (z : h 0 = 0) (d : fderiv ℝ h 0 = 0) :
      ∀ j ≤ 1, ∀ v : ℝ, iteratedFDeriv ℝ j h 0 (fun _ => v) = 0 := by
    intro j hj v
    interval_cases j <;> simp [z,d]
  obtain ⟨F,hF,_,ef⟩ := ray_profile f 1 (cf.of_le (by decide)) (flat f f0 df)
  obtain ⟨G,hG,G0,eg⟩ := ray_profile g 1 (cg.of_le (by decide)) (flat g g0 dg)
  by_cases b : G 0 = 0
  · have v2 : ∀ v : ℝ, iteratedFDeriv ℝ 2 g 0 (fun _ => v) = 0 := by
      have z : iteratedFDeriv ℝ 2 g 0 (fun _ => (1:ℝ)) = 0 := by
        simpa [Return.coeff] using G0.symm.trans b
      intro v
      simpa [z] using (iteratedFDeriv ℝ 2 g 0).map_smul_univ (fun _ => v) (fun _ => (1:ℝ))
    obtain ⟨B,hB,_,eb⟩ := ray_profile g 2 cg (by
      intro j hj v
      rcases (show j ≤ 1 ∨ j = 2 by omega) with one | rfl
      · exact flat g g0 dg _ one v
      · exact v2 v)
    refine ⟨3,Or.inr rfl,F 0,B 0,c,cp,cubic_ray_box V F B c hF hB ?_⟩
    filter_upwards [save] with p h
    intro ht
    simpa only [ef _ ht,eb _ ht,mul_add] using h ht
  · refine ⟨2,Or.inl rfl,F 0,G 0,c/2,half_pos cp,square_ray_box V g F G cp hF hG b
      ((cg.eventually (by decide)).mono fun _ smooth => smooth.continuousAt) eg ?_⟩
    let I (p : Pair) := (p.1,p.2,(0:ℝ))
    have ti : Tendsto I (𝓝 0) (𝓝 0) := (continuous_fst.prodMk (continuous_snd.prodMk continuous_const)).tendsto (0:Pair)
    filter_upwards [ti save] with p h
    intro ht
    simpa only [I,ef _ ht,mul_zero,add_zero,mul_add] using h ht

#print axioms box_of_shortened_ray

end MinimizingSard.Five
