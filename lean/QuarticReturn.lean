import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! The fourth-order return in reduced endpoint coordinates. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace MinimizingSard.Return
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def coeff (f : E → ℝ) (j : ℕ) (x v : E) : ℝ :=
  iteratedFDeriv ℝ j f x (fun _ => v) / j.factorial

private theorem ray_deriv (f : E → ℝ) (j : ℕ) (s : ℝ) (v : E)
    (hf : ContDiffAt ℝ j f (s • v)) :
    iteratedDeriv j (fun t : ℝ => f (t • v)) s =
      iteratedFDeriv ℝ j f (s • v) (fun _ => v) := by
  let g := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  obtain ⟨U,Uo,mem,smooth⟩ := hf.contDiffOn' le_rfl (by simp)
  simp at smooth
  have pre : IsOpen (g ⁻¹' U) := Uo.preimage g.continuous
  have eq := g.iteratedFDerivWithin_comp_right smooth Uo.uniqueDiffOn pre.uniqueDiffOn mem (i := j) le_rfl
  have cs : ContDiffAt ℝ j (f ∘ g) s := hf.comp s g.contDiff.contDiffAt
  change ContDiffAt ℝ j f (g s) at hf
  change g s ∈ U at mem
  rw [iteratedFDerivWithin_eq_iteratedFDeriv pre.uniqueDiffOn cs mem,
      iteratedFDerivWithin_eq_iteratedFDeriv Uo.uniqueDiffOn hf mem] at eq
  change iteratedFDeriv ℝ j (f ∘ g) s (fun _ => 1) = _
  rw [eq]
  simp [g]

/-- Uniform Taylor division while both the amplitude and the direction vary.
Only a germ of the reduced endpoint at the reference control is used. -/
theorem radial_profile (f : E → ℝ) (n : ℕ) (h : E)
    (hf : ContDiffAt ℝ (n+1 : ℕ) f 0)
    (flat : ∀ j ≤ n, ∀ v : E, iteratedFDeriv ℝ j f 0 (fun _ => v) = 0)
    {ε : ℝ} (he : 0 < ε) :
    ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ → ∀ v : E, dist v h < δ →
      |f (t • v) / t^(n+1) - coeff f (n+1) 0 h| < ε := by
  have cd : ContinuousAt (iteratedFDeriv ℝ (n+1) f) 0 :=
    (hf.iteratedFDeriv_right (m := 0) (by simp)).continuousAt
  have at0 : ContinuousAt (fun p : ℝ × E => p.1 • p.2) (0,h) := by fun_prop
  have cd' : ContinuousAt (fun p : ℝ × E => iteratedFDeriv ℝ (n+1) f (p.1 • p.2)) (0,h) :=
    ContinuousAt.comp (f := fun p : ℝ × E => p.1 • p.2)
      (show ContinuousAt (iteratedFDeriv ℝ (n+1) f) ((0:ℝ) • h) by simpa using cd) at0
  have cp : ContinuousAt (fun p : ℝ × E => coeff f (n+1) (p.1 • p.2) p.2) (0,h) := by
    unfold coeff
    exact (continuous_eval.continuousAt.comp (cd'.prodMk
      (continuous_pi (fun _ => continuous_snd)).continuousAt)).div_const _
  have near := hf.eventually (by simp)
  have localReg : ∀ᶠ p : ℝ × E in 𝓝 (0,h), ContDiffAt ℝ (n+1 : ℕ) f (p.1 • p.2) :=
    at0 (by simpa using near)
  obtain ⟨δ,hδ,both⟩ := Metric.mem_nhds_iff.mp (localReg.and (cp.eventually
    (Metric.ball_mem_nhds _ he)))
  refine ⟨δ,hδ,?_⟩
  intro t ht htd v hv
  have tube (u : ℝ) (hu : u ∈ Icc 0 t) := both (show (u,v) ∈ ball ((0:ℝ),h) δ by
    simp [Metric.mem_ball,Prod.dist_eq,abs_of_nonneg hu.1,hu.2.trans_lt htd,hv])
  let g (u : ℝ) := f (u • v)
  have reg (u : ℝ) (hu : u ∈ Icc 0 t) : ContDiffAt ℝ (n+1 : ℕ) g u :=
    (tube u hu).1.comp u (contDiffAt_id.smul contDiffAt_const)
  obtain ⟨u,hu,eq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv ht (n := n)
    (f := g) (fun u hu => (reg u hu).contDiffWithinAt)
  have z : taylorWithinEval g n (Icc 0 t) 0 t = 0 := by
    rw [taylor_within_apply]
    apply Finset.sum_eq_zero
    intro j hj
    have jl : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have bound : (j : WithTop ℕ∞) ≤ (↑(n+1 : ℕ) : WithTop ℕ∞) := by exact_mod_cast jl.trans (Nat.le_succ n)
    have h0 := left_mem_Icc.mpr ht.le
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc ht) ((reg 0 h0).of_le bound) h0,
      ray_deriv f j 0 v (by simpa using hf.of_le bound),zero_smul,flat j jl]
    simp
  have result := (tube u ⟨hu.1.le,hu.2.le⟩).2
  change dist (coeff f (n+1) (u • v) v) (coeff f (n+1) ((0:ℝ) • h) h) < ε at result
  rw [zero_smul,Real.dist_eq] at result
  rw [z,sub_zero,sub_zero,ray_deriv f (n+1) u v (tube u ⟨hu.1.le,hu.2.le⟩).1] at eq
  have val : f (t • v) / t^(n+1) = coeff f (n+1) (u • v) v := by
    change g t / t^(n+1) = _
    rw [eq,coeff]
    field_simp
  rwa [val]
/-- A regular quadratic coordinate fills an interval exactly, using only
the intermediate value theorem on a small convex ball of directions. -/
theorem quadratic_coordinate (f : E → ℝ) (h : E) (hf : ContDiffAt ℝ 2 f 0)
    (flat : ∀ j ≤ 1, ∀ v : E, iteratedFDeriv ℝ j f 0 (fun _ => v) = 0)
    (regular : fderiv ℝ (coeff f 2 0) h ≠ 0) {R : ℝ} (hR : 0 < R) :
    ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ → ∀ a : ℝ, |a - coeff f 2 0 h| < δ →
      ∃ v ∈ ball h R, f (t • v) = t^2*a := by
  let Q := coeff f 2 0
  have localReg : ∀ᶠ p : ℝ × E in 𝓝 (0,h), ContinuousAt f (p.1 • p.2) := by
    have cont : ContinuousAt (fun p : ℝ × E => p.1 • p.2) (0,h) := by fun_prop
    have near : ∀ᶠ x in 𝓝 (0:E), ContinuousAt f x := (hf.eventually (by simp)).mono fun _ hx => hx.continuousAt
    exact cont (by simpa using near)
  obtain ⟨r,hr,tube⟩ := Metric.mem_nhds_iff.mp localReg
  let α := min r R
  have hα : 0 < α := lt_min hr hR
  have hm : ∃ v ∈ ball h α, Q v < Q h := by
    by_contra! none
    exact regular (IsLocalMin.fderiv_eq_zero (show IsLocalMin Q h from
      Filter.mem_of_superset (ball_mem_nhds h hα) fun v hv => none v hv))
  have hp : ∃ v ∈ ball h α, Q h < Q v := by
    by_contra! none
    exact regular (IsLocalMax.fderiv_eq_zero (show IsLocalMax Q h from
      Filter.mem_of_superset (ball_mem_nhds h hα) fun v hv => none v hv))
  obtain ⟨u,hu,lo⟩ := hm
  obtain ⟨w,hw,hi⟩ := hp
  let ε := min (Q h - Q u) (Q w - Q h) / 3
  have he : 0 < ε := div_pos (lt_min (sub_pos.mpr lo) (sub_pos.mpr hi)) (by norm_num)
  obtain ⟨l,hl,left⟩ := radial_profile f 1 u hf flat he
  obtain ⟨b,hb,right⟩ := radial_profile f 1 w hf flat he
  let δ := min (min l b) (min r ε)
  refine ⟨δ,lt_min (lt_min hl hb) (lt_min hr he),?_⟩
  intro t ht hδ a ha
  have hparts := lt_min_iff.mp hδ
  have tr := (lt_min_iff.mp hparts.2).1
  let G (v : E) := f (t • v)/t^2
  have c : ContinuousOn G (ball h α) := by
    intro v hv
    have cf := tube (show (t,v) ∈ ball ((0:ℝ),h) r by
      simpa [Metric.mem_ball,Prod.dist_eq,abs_of_pos ht,tr] using
        (lt_of_lt_of_le (Metric.mem_ball.mp hv) (min_le_left r R)))
    exact ((cf.comp (f := fun x : E => t • x) (continuous_const.smul continuous_id).continuousAt).div_const _).continuousWithinAt
  have small := (abs_lt.mp ha)
  have reach := (convex_ball h α).isPreconnected.intermediate_value hu hw c
  have gapL : 3*ε ≤ Q h - Q u := by dsimp [ε]; linarith [min_le_left (Q h-Q u) (Q w-Q h)]
  have gapR : 3*ε ≤ Q w - Q h := by dsimp [ε]; linarith [min_le_right (Q h-Q u) (Q w-Q h)]
  have δe : δ ≤ ε := (min_le_right _ _).trans (min_le_right _ _)
  have upper := (abs_lt.mp (left t ht (lt_min_iff.mp hparts.1).1 u (by simpa using hl))).2
  have lower := (abs_lt.mp (right t ht (lt_min_iff.mp hparts.1).2 w (by simpa using hb))).1
  change G u - Q u < ε at upper
  change -ε < G w - Q w at lower
  obtain ⟨v,hv,eq⟩ := reach (show a ∈ Icc (G u) (G w) from ⟨by linarith,by linarith⟩)
  refine ⟨v,ball_subset_ball (min_le_right r R) hv,?_⟩
  exact (div_eq_iff (pow_ne_zero 2 ht.ne')).mp eq |>.trans (mul_comm _ _)

private theorem fourth_scale (t b u : ℝ) (ht : 0 ≤ t) :
    |t^4*b-t^4*u|^(1/4:ℝ) = t * |b-u|^(1/4:ℝ) := by
  rw [← mul_sub,abs_mul,abs_of_nonneg (pow_nonneg ht 4),Real.mul_rpow (pow_nonneg ht _) (abs_nonneg _),
    ← Real.rpow_natCast_mul ht]
  norm_num

/-- The local one-quarter estimate pays for the transverse error on an
open interval about any quartic coefficient, including zero. -/
theorem uniform_fourth_repair (V : ℝ × ℝ → ℝ) (A B K σ : ℝ) (hσ : 0 < σ)
    (holder : ∀ᶠ p : ℝ × ℝ × ℝ in 𝓝 0,
      V (p.1,p.2.1) ≤ V (p.1,p.2.2) + K * |p.2.1-p.2.2|^(1/4:ℝ)) :
    ∃ δ > 0, ∀ t : ℝ, 0 ≤ t → t < δ → ∀ a b u : ℝ,
      |a-A| < δ → |b-B| < δ → |u-B| < δ →
      V (t^2*a,t^4*b) ≤ V (t^2*a,t^4*u) + σ*t := by
  let center : ℝ × ℝ × ℝ × ℝ := (0,A,B,B)
  let out (p : ℝ × ℝ × ℝ × ℝ) := (p.1^2*p.2.1,p.1^4*p.2.2.1,p.1^4*p.2.2.2)
  have co : Continuous out := by dsimp [out]; fun_prop
  have out0 : out center = 0 := by simp [center,out]
  have near : ∀ᶠ p in 𝓝 center, V ((out p).1,(out p).2.1) ≤ V ((out p).1,(out p).2.2) +
      K * |(out p).2.1-(out p).2.2|^(1/4:ℝ) := co.continuousAt (out0.symm ▸ holder)
  let err (p : ℝ × ℝ × ℝ × ℝ) := K * |p.2.2.1-p.2.2.2|^(1/4:ℝ)
  have ce : Continuous err := continuous_const.mul ((Real.continuous_rpow_const (by norm_num : 0 ≤ (1/4:ℝ))).comp
    (show Continuous (fun p : ℝ × ℝ × ℝ × ℝ => |p.2.2.1-p.2.2.2|) by fun_prop))
  have small : ∀ᶠ p in 𝓝 center, err p < σ := ce.continuousAt.eventually_lt continuousAt_const
    (by simpa [err,center] using hσ)
  obtain ⟨δ,hδ,both⟩ := Metric.mem_nhds_iff.mp (near.and small)
  refine ⟨δ,hδ,?_⟩
  intro t ht htd a b u ha hb hu
  have v := both (show (t,a,b,u) ∈ ball center δ by
    simp [center,Metric.mem_ball,Prod.dist_eq,Real.dist_eq,abs_of_nonneg ht,htd,ha,hb,hu])
  have cost := v.1
  change V (t^2*a,t^4*b) ≤ V (t^2*a,t^4*u) + K * |t^4*b-t^4*u|^(1/4:ℝ) at cost
  rw [fourth_scale _ _ _ ht] at cost
  have pay := mul_le_mul_of_nonneg_right v.2.le ht
  change K*|b-u|^(1/4:ℝ)*t ≤ σ*t at pay
  linarith

/-- Reduced-coordinate fourth-order branch. The cost, both endpoint
coordinates and all of their jets refer to the same controls. -/
theorem fourth_order_descent_box (f g cost : E → ℝ) (V : ℝ × ℝ → ℝ) (h : E)
    (hf : ContDiffAt ℝ 2 f 0) (hg : ContDiffAt ℝ 4 g 0) (hc : ContDiffAt ℝ 1 cost 0)
    (fvan : ∀ j ≤ 1, ∀ v : E, iteratedFDeriv ℝ j f 0 (fun _ => v) = 0)
    (gvan : ∀ j ≤ 3, ∀ v : E, iteratedFDeriv ℝ j g 0 (fun _ => v) = 0)
    (regular : fderiv ℝ (coeff f 2 0) h ≠ 0) (cz : cost 0 = 0)
    (down : coeff cost 1 0 h < 0)
    (competitors : ∀ᶠ x in 𝓝 0, V (f x,g x) ≤ V 0 + cost x)
    (K : ℝ) (holder : ∀ᶠ p : ℝ × ℝ × ℝ in 𝓝 0,
       V (p.1,p.2.1) ≤ V (p.1,p.2.2) + K * |p.2.1-p.2.2|^(1/4:ℝ)) :
    ∃ c > 0, ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ → ∀ a b : ℝ,
      |a-coeff f 2 0 h| < δ → |b-coeff g 4 0 h| < δ →
      V (t^2*a,t^4*b) ≤ V 0 - c*t := by
  let c := -(coeff cost 1 0 h)/4
  have pos : 0 < c := by dsimp [c]; linarith
  obtain ⟨r,hr,repair⟩ := uniform_fourth_repair V (coeff f 2 0 h) (coeff g 4 0 h) K c pos holder
  obtain ⟨s,hs,profile⟩ := radial_profile g 3 h hg gvan hr
  have cv : ∀ j ≤ 0, ∀ v : E, iteratedFDeriv ℝ j cost 0 (fun _ => v) = 0 := by
    intro j hj v
    obtain rfl : j = 0 := by omega
    simp [cz]
  obtain ⟨z,hz,saving⟩ := radial_profile cost 0 h hc cv pos
  have co : ContinuousAt (fun p : ℝ × E => p.1 • p.2) (0,h) := by fun_prop
  have near : ∀ᶠ p : ℝ × E in 𝓝 (0,h), V (f (p.1 • p.2),g (p.1 • p.2)) ≤ V 0 + cost (p.1 • p.2) :=
    co (by simpa using competitors)
  obtain ⟨u,hu,use⟩ := Metric.mem_nhds_iff.mp near
  let R := min z (min s u)
  have hR : 0 < R := lt_min hz (lt_min hs hu)
  obtain ⟨d,hd,solve⟩ := quadratic_coordinate f h hf fvan regular hR
  let δ := min d (min r R)
  refine ⟨c,pos,δ,lt_min hd (lt_min hr hR),?_⟩
  intro t ht htd a b ha hb
  have td := lt_min_iff.mp htd
  have tR := (lt_min_iff.mp td.2).2
  have ts := lt_min_iff.mp tR
  obtain ⟨v,hv,eq⟩ := solve t ht td.1 a (lt_min_iff.mp ha).1
  have vv := lt_min_iff.mp (mem_ball.mp hv)
  have normalized := profile t ht (lt_min_iff.mp ts.2).1 v (lt_min_iff.mp vv.2).1
  have net := (abs_lt.mp (saving t ht ts.1 v vv.1)).2
  simp only [Nat.zero_add,pow_one] at net
  have costBound : cost (t • v) ≤ -(2*c)*t := by
    have val : cost (t • v)/t < coeff cost 1 0 h + c := by linarith
    have res := (div_lt_iff₀ ht).mp val
    dsimp [c] at *
    nlinarith only [res,mul_neg_of_neg_of_pos down ht]
  have cand := use (show (t,v) ∈ ball ((0:ℝ),h) u by
    simp [Metric.mem_ball,Prod.dist_eq,abs_of_pos ht,(lt_min_iff.mp ts.2).2,(lt_min_iff.mp vv.2).2])
  change V (f (t • v),g (t • v)) ≤ V 0 + cost (t • v) at cand
  rw [eq] at cand
  have fixed := repair t ht.le (lt_min_iff.mp td.2).1 a b (g (t • v)/t^4)
    (lt_min_iff.mp (lt_min_iff.mp ha).2).1 (lt_min_iff.mp (lt_min_iff.mp hb).2).1 normalized
  rw [show t^4 * (g (t • v)/t^4) = g (t • v) by field_simp] at fixed
  linarith

/-- Uniformity in both endpoints follows by inverting the signed motion
parameters together with the moving starting point. -/
theorem holder_of_signed_motions {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [CompleteSpace E] [CompleteSpace P] (y : E) (A : E × P → E)
    (basis : P ≃L[ℝ] E) (zero : ∀ᶠ z in 𝓝 y, A (z,0) = 0)
    (jet : HasStrictFDerivAt A ((basis : P →L[ℝ] E).comp (ContinuousLinearMap.snd ℝ E P)) (y,0))
    (V : E → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (cost : ∀ᶠ x : E × P in 𝓝 (y,0), V (x.1 + A x) ≤ V x.1 + L*‖x.2‖^(1/4:ℝ)) :
    ∃ K : ℝ, ∀ᶠ p : E × E in 𝓝 (y,y), V p.2 ≤ V p.1 + K*‖p.2-p.1‖^(1/4:ℝ) := by
  let H (p : E × P) := (p.1,A p)
  let e := (ContinuousLinearEquiv.refl ℝ E).prodCongr basis
  have hd : HasStrictFDerivAt H (e : (E × P) →L[ℝ] (E × E)) (y,0) :=
    (hasStrictFDerivAt_fst (𝕜 := ℝ) (p := (y,(0:P)))).prodMk jet
  let S := hd.localInverse H e (y,0)
  have h0 : H (y,0) = (y,0) := Prod.ext rfl zero.self_of_nhds
  have ds : HasStrictFDerivAt S (e.symm : (E × E) →L[ℝ] E × P) (y,0) := h0 ▸ hd.to_localInverse
  obtain ⟨C,U,hU,lip⟩ := ds.exists_lipschitzOnWith
  let w (p : E × E) := (p.1,p.2-p.1)
  let w0 (p : E × E) := (p.1,(0:E))
  let v0 (p : E × E) := (p.1,(0:P))
  have cw : Tendsto w (𝓝 (y,y)) (𝓝 (y,0)) := by
    have con : Continuous w := continuous_fst.prodMk (continuous_snd.sub continuous_fst)
    simpa [w] using con.tendsto (y,y)
  have cw0 : Tendsto w0 (𝓝 (y,y)) (𝓝 (y,0)) := continuousAt_fst.prodMk continuousAt_const
  have cv0 : Tendsto v0 (𝓝 (y,y)) (𝓝 (y,0)) := continuousAt_fst.prodMk continuousAt_const
  have left : ∀ᶠ p : E × P in 𝓝 (y,0), S (H p) = p := hd.eventually_left_inverse
  have right : ∀ᶠ p : E × E in 𝓝 (y,0), H (S p) = p := h0 ▸ hd.eventually_right_inverse
  have s0 : S (y,0) = (y,0) := h0 ▸ hd.localInverse_apply_image
  have cs : Tendsto S (𝓝 (y,0)) (𝓝 (y,0)) := s0 ▸ ds.continuousAt
  refine ⟨L*(C:ℝ)^(1/4:ℝ),?_⟩
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
  change V ((S (w p)).1 + A (S (w p))) ≤ V (S (w p)).1 + L*‖(S (w p)).2‖^(1/4:ℝ) at use
  rw [xeq,aeq,add_sub_cancel] at use
  have bound := lip.dist_le_mul _ hu _ hu0
  rw [hleft] at bound
  have parm : ‖(S (w p)).2‖ ≤ (C:ℝ) * ‖p.2-p.1‖ := by
    have le := (le_max_right (dist (S (w p)).1 p.1) (dist (S (w p)).2 0)).trans bound
    simpa [w,w0,v0,Prod.dist_eq] using le
  have root := Real.rpow_le_rpow (norm_nonneg _) parm (by norm_num : 0 ≤ (1/4:ℝ))
  rw [Real.mul_rpow (by positivity) (norm_nonneg _)] at root
  exact use.trans (by nlinarith only [mul_le_mul_of_nonneg_left root hL])

theorem regular_descending_direction (f cost : E → ℝ) (hf : ContDiffAt ℝ 2 f 0)
    (hne : fderiv ℝ (fderiv ℝ f) 0 ≠ 0) (hneCost : fderiv ℝ cost 0 ≠ 0) :
    ∃ h, fderiv ℝ (coeff f 2 0) h ≠ 0 ∧ coeff cost 1 0 h < 0 := by
  let A := fderiv ℝ (fderiv ℝ f) 0
  let L := fderiv ℝ cost 0
  have sym : ∀ v w, A v w = A w v := hf.isSymmSndFDerivAt (by simp)
  have dq (v : E) : fderiv ℝ (coeff f 2 0) v = A v := by
    have qeq : coeff f 2 0 = fun w => (1/2:ℝ) * (A w w) := by
      funext w
      simp only [coeff,iteratedFDeriv_two_apply,show Nat.factorial 2 = 2 from rfl,Nat.cast_ofNat,A]
      ring
    have df := (((A.hasFDerivAt).clm_apply (hasFDerivAt_id v)).const_mul (1/2:ℝ)).fderiv
    simp only [id_eq] at df
    rw [qeq,df]
    ext w
    change (1/2:ℝ) * (A v w + A w v) = A v w
    rw [sym w v]
    ring
  have hasCost : ∃ v, L v ≠ 0 := by
    by_contra! no
    exact hneCost (ContinuousLinearMap.ext fun v => no v)
  obtain ⟨v,hv⟩ := hasCost
  have neg : ∃ x, L x < 0 := by
    rcases lt_or_gt_of_ne hv with hv | hv
    · exact ⟨v,hv⟩
    · exact ⟨-v,by simpa using neg_neg_of_pos hv⟩
  obtain ⟨x,hx⟩ := neg
  have C (v : E) : coeff cost 1 0 v = L v := by simp [coeff,L]
  by_cases h : A x = 0
  · have has : ∃ z, A z ≠ 0 := by
      by_contra! no
      exact hne (ContinuousLinearMap.ext fun z => no z)
    obtain ⟨z,hz⟩ := has
    by_cases pos : L z ≤ 0
    · exact ⟨x+z,by simpa [dq,map_add,h] using hz,by rw [C,map_add]; linarith⟩
    · exact ⟨x-z,by simpa [dq,map_sub,h] using hz,by rw [C,map_sub]; linarith⟩
  · exact ⟨x,dq x ▸ h,C x ▸ hx⟩

/-- Neither the descending direction nor a regular perturbation in that
direction is supplied. Both follow from the nonzero restricted cost row
and quadratic endpoint row. -/
theorem quartic_box_from_reduced_jets (f g cost : E → ℝ) (V : ℝ × ℝ → ℝ)
    (hf : ContDiffAt ℝ 2 f 0) (hg : ContDiffAt ℝ 4 g 0) (hc : ContDiffAt ℝ 1 cost 0)
    (fvan : ∀ j ≤ 1, ∀ v : E, iteratedFDeriv ℝ j f 0 (fun _ => v) = 0)
    (gvan : ∀ j ≤ 3, ∀ v : E, iteratedFDeriv ℝ j g 0 (fun _ => v) = 0)
    (quad : fderiv ℝ (fderiv ℝ f) 0 ≠ 0) (cz : cost 0 = 0)
    (strict : fderiv ℝ cost 0 ≠ 0)
    (competitors : ∀ᶠ x in 𝓝 0, V (f x,g x) ≤ V 0 + cost x)
    (K : ℝ) (holder : ∀ᶠ p : ℝ × ℝ × ℝ in 𝓝 0,
       V (p.1,p.2.1) ≤ V (p.1,p.2.2) + K * |p.2.1-p.2.2|^(1/4:ℝ)) :
    ∃ A B c : ℝ, 0 < c ∧ ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ → ∀ a b : ℝ,
      |a-A| < δ → |b-B| < δ → V (t^2*a,t^4*b) ≤ V 0 - c*t := by
  obtain ⟨h,reg,des⟩ := regular_descending_direction f cost hf quad strict
  exact ⟨_,_,fourth_order_descent_box f g cost V h hf hg hc fvan gvan reg cz des competitors K holder⟩

#print axioms regular_descending_direction
#print axioms quartic_box_from_reduced_jets
#print axioms holder_of_signed_motions
#print axioms uniform_fourth_repair
#print axioms fourth_order_descent_box
#print axioms quadratic_coordinate
#print axioms radial_profile
end MinimizingSard.Return
