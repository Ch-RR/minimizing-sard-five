import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

noncomputable section
open Filter Set
open scoped Topology
namespace MinimizingSard.Return
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The small prefactor removes the unbounded Lipschitz constant of the root. -/
private theorem root_secant {s t a : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ha : 0 < a) (ha1 : a ≤ 1) :
    s * |s^a-t^a| ≤ s^a * |s-t| := by
  rw [abs_of_nonpos (sub_nonpos.mpr (Real.rpow_le_rpow hs hst ha.le)),abs_of_nonpos (sub_nonpos.mpr hst)]
  rcases hs.eq_or_lt with h | h
  · simp [← h, Real.zero_rpow ha.ne']
  have ht := h.trans_le hst
  have rel := Real.rpow_le_rpow_of_nonpos h hst (sub_nonpos.mpr ha1)
  rw [Real.rpow_sub_one ht.ne',Real.rpow_sub_one h.ne',div_le_div_iff₀ ht h] at rel
  linarith

private theorem root_remainder (q b : E) (Z : E × ℝ → E)
    (hz : ContDiffAt ℝ 1 Z (q,0)) (z0 : Z (q,0) = b)
    (u : E × ℝ → ℝ) (hu : LipschitzWith 1 u) (u0 : u (q,0) = 0) (upos : ∀ x, 0 ≤ u x)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    HasStrictFDerivAt (𝕜 := ℝ) (fun x => u x • (Z (x.1,(u x)^a)-b)) 0 (q,0) := by
  let T (x : E × ℝ) := (x.1,(u x)^a)
  have tc : Continuous T := continuous_fst.prodMk ((Real.continuous_rpow_const ha.le).comp hu.continuous)
  have tz : T (q,0) = (q,0) := by simp [T,u0,Real.zero_rpow ha.ne']
  have tend : Tendsto T (𝓝 (q,0)) (𝓝 (q,0)) := by simpa only [tz] using tc.tendsto (q,0)
  obtain ⟨C,U,nh,lip⟩ := hz.exists_lipschitzOnWith
  rw [hasStrictFDerivAt_iff_isLittleO,Asymptotics.isLittleO_iff]
  intro ε hε
  let small (x : E × ℝ) := ‖Z (T x)-b‖ + C * (u x + (u x)^a)
  have cont : ContinuousAt small (q,0) :=
    ((hz.continuousAt.comp_of_eq tc.continuousAt tz).sub continuousAt_const).norm.add
      (continuousAt_const.mul (hu.continuous.continuousAt.add ((Real.continuous_rpow_const ha.le).comp hu.continuous).continuousAt))
  have tiny : ∀ᶠ x in 𝓝 (q,0), small x < ε := cont.eventually_lt_const (by
    simpa [small,tz,z0,u0,Real.zero_rpow ha.ne'] using hε)
  have inU : ∀ᶠ x in 𝓝 (q,0), T x ∈ U := tend nh
  have near := inU.and tiny
  let R (x : E × ℝ) := u x • (Z (T x)-b)
  have ordered (x y : E × ℝ) (hx : T x ∈ U) (hy : T y ∈ U) (sy : small y < ε)
      (ord : u x ≤ u y) : ‖R x-R y‖ ≤ ε * dist x y := by
    let d := dist x y
    have ud : |u x-u y| ≤ d := by simpa [Real.dist_eq,d] using hu.dist_le_mul x y
    have xd : dist x.1 y.1 ≤ d := le_max_left _ _
    have sc := root_secant (upos x) ord ha ha1
    have mm : u x * dist (T x) (T y) ≤ (u x+(u x)^a)*d := by
      change u x * max (dist x.1 y.1) |(u x)^a-(u y)^a| ≤ _
      rw [mul_max_of_nonneg _ _ (upos x)]
      apply max_le
      · exact (mul_le_mul_of_nonneg_left xd (upos x)).trans
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (Real.rpow_nonneg (upos x) _)) dist_nonneg)
      · exact (sc.trans (mul_le_mul_of_nonneg_left ud (Real.rpow_nonneg (upos x) _))).trans
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (upos x)) dist_nonneg)
    have zz := lip.dist_le_mul (T x) hx (T y) hy
    have split : R x - R y = u x • (Z (T x)-Z (T y)) + (u x-u y) • (Z (T y)-b) := by
      simp only [R,smul_sub,sub_smul]; abel
    rw [split]
    apply (norm_add_le _ _).trans
    rw [norm_smul,norm_smul,Real.norm_eq_abs,abs_of_nonneg (upos x),Real.norm_eq_abs]
    rw [dist_eq_norm] at zz
    have a1 := mul_le_mul_of_nonneg_left zz (upos x)
    have a2 := mul_le_mul_of_nonneg_left mm C.property
    have a3 := mul_le_mul_of_nonneg_right ud (norm_nonneg (Z (T y)-b))
    have bound : ‖Z (T y)-b‖ + C*(u x+(u x)^a) ≤ ε := by
      apply le_trans _ sy.le
      exact add_le_add_left (mul_le_mul_of_nonneg_left
        (add_le_add ord (Real.rpow_le_rpow (upos x) ord ha.le)) C.property) _
    have a4 := mul_le_mul_of_nonneg_right bound (dist_nonneg (x := x) (y := y))
    dsimp only [d] at *
    rw [mul_left_comm] at a1
    calc
      _ ≤ C*((u x+(u x)^a)*dist x y) + dist x y*‖Z (T y)-b‖ := add_le_add (a1.trans a2) a3
      _ = (‖Z (T y)-b‖ + C*(u x+(u x)^a))*dist x y := by ring
      _ ≤ _ := a4
  filter_upwards [continuous_fst.continuousAt.tendsto near, continuous_snd.continuousAt.tendsto near]
    with p hx hy
  change ‖R p.1-R p.2-(0 : (E × ℝ) →L[ℝ] E) _‖ ≤ _
  rw [ContinuousLinearMap.zero_apply,sub_zero,← dist_eq_norm p.1 p.2]
  rcases le_total (u p.1) (u p.2) with h | h
  · exact ordered _ _ hx.1 hy.1 hy.2 h
  · rw [norm_sub_rev,dist_comm]
    exact ordered _ _ hy.1 hx.1 hx.2 h

/-- At a signed parameter, use the profile of the inverse word on the negative side. -/
def signedMove (Z W : E × ℝ → E) (a : ℝ) (p : E × ℝ) : E :=
  if 0 ≤ p.2 then p.2 • Z (p.1,p.2^a) else p.2 • W (p.1,(-p.2)^a)

/-- Joint strict derivative in state and signed parameter. The exponent includes
all roots of positive integral orders; the derivative in the state variable vanishes. -/
theorem signed_root_displacement (Z W : E × ℝ → E) (q : E) {a : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hz : ContDiffAt ℝ 1 Z (q,0)) (hw : ContDiffAt ℝ 1 W (q,0))
    (match0 : W (q,0) = Z (q,0)) :
    HasStrictFDerivAt (signedMove Z W a) ((ContinuousLinearMap.snd ℝ E ℝ).smulRight (Z (q,0))) (q,0) := by
  let pos (p : E × ℝ) := max p.2 0
  let neg (p : E × ℝ) := max (-p.2) 0
  have lp : LipschitzWith 1 pos := LipschitzWith.of_dist_le_mul fun x y => by
    simpa [pos,Real.dist_eq] using (abs_max_sub_max_le_abs x.2 y.2 0).trans (show |x.2-y.2| ≤ dist x y from le_max_right _ _)
  have ln : LipschitzWith 1 neg := LipschitzWith.of_dist_le_mul fun x y => by
    have bound := abs_max_sub_max_le_abs (-x.2) (-y.2) 0
    rw [neg_sub_neg,abs_sub_comm y.2 x.2] at bound
    simpa [neg,Real.dist_eq] using bound.trans (show |x.2-y.2| ≤ dist x y from le_max_right _ _)
  have dp := root_remainder q _ Z hz rfl pos lp (by simp [pos]) (fun p => le_max_right _ _) ha ha1
  have dn := root_remainder q _ W hw match0 neg ln (by simp [neg]) (fun p => le_max_right _ _) ha ha1
  let L := (ContinuousLinearMap.snd ℝ E ℝ).smulRight (Z (q,0))
  have deriv := ((L.hasStrictFDerivAt (x := (q,0))).add dp).sub dn
  rw [add_zero,sub_zero] at deriv
  convert deriv using 1
  ext p
  change signedMove Z W a p = p.2 • Z (q,0) + pos p • (Z (p.1,(pos p)^a)-Z (q,0))
    - neg p • (W (p.1,(neg p)^a)-Z (q,0))
  by_cases h : 0 ≤ p.2
  · simp [signedMove,h,pos,neg,smul_sub]
  · have h' := le_of_lt (lt_of_not_ge h)
    simp [signedMove,h,pos,neg,max_eq_right h',max_eq_left (neg_nonneg.mpr h'),smul_sub]

#print axioms signed_root_displacement

/-- Physical endpoint obtained by running the word or its inverse for a nonnegative time. -/
def rootEndpoint (F B : E × ℝ → E) (k : ℕ) (p : E × ℝ) : E :=
  let t := |p.2|^((k:ℝ)⁻¹)
  if 0 ≤ p.2 then F (p.1,t) else B (p.1,t)

theorem inverse_word_root_jet (F B Z : E × ℝ → E) (q : E) {k : ℕ} (hk : 0 < k)
    (hz : ContDiffAt ℝ 1 Z (q,0)) (hb : ContDiffAt ℝ 1 B (q,0)) (b0 : B (q,0) = q)
    (form : ∀ᶠ p in 𝓝 (q,(0:ℝ)), F p = p.1 + p.2^k • Z p)
    (undo : ∀ᶠ p in 𝓝 (q,(0:ℝ)), F (B p,p.2) = p.1) :
    HasStrictFDerivAt (rootEndpoint F B k)
      ((ContinuousLinearMap.fst ℝ E ℝ) + (ContinuousLinearMap.snd ℝ E ℝ).smulRight (Z (q,0))) (q,0) := by
  let a := (k:ℝ)⁻¹
  have kp : (0:ℝ) < k := by exact_mod_cast hk
  have ha : 0 < a := inv_pos.mpr kp
  have ha1 : a ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hk)
  let R (p : E × ℝ) := (B p,p.2)
  have r0 : R (q,0) = (q,0) := Prod.ext b0 rfl
  have cr : ContDiffAt ℝ 1 R (q,0) := hb.prodMk contDiffAt_snd
  have invform : ∀ᶠ p in 𝓝 (q,(0:ℝ)), B p = p.1 - p.2^k • Z (R p) := by
    have rr : Tendsto R (𝓝 (q,0)) (𝓝 (q,0)) := by simpa only [r0] using cr.continuousAt.tendsto
    filter_upwards [rr form,undo] with p h j
    exact eq_sub_of_add_eq (h.symm.trans j)
  let T (p : E × ℝ) := (p.1, |p.2|^a)
  have tc : Continuous T := continuous_fst.prodMk ((Real.continuous_rpow_const ha.le).comp continuous_snd.abs)
  have to0 : Tendsto T (𝓝 (q,0)) (𝓝 (q,0)) := by simpa [T,Real.zero_rpow ha.ne'] using tc.tendsto (q,0)
  have power (s : ℝ) : (|s|^a)^k = |s| := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (abs_nonneg s),inv_mul_cancel₀ kp.ne',Real.rpow_one]
  have deriv := (hasStrictFDerivAt_fst (𝕜 := ℝ) (p := (q,(0:ℝ)))).add
    (signed_root_displacement Z (Z ∘ R) q ha ha1 hz ((r0.symm ▸ hz).comp (q,0) cr) (congrArg Z r0))
  apply deriv.congr_of_eventuallyEq
  filter_upwards [to0 form,to0 invform] with p pos neg
  change F (T p) = p.1 + (|p.2|^a)^k • Z (T p) at pos
  change B (T p) = p.1 - (|p.2|^a)^k • Z (R (T p)) at neg
  rw [power] at pos neg
  by_cases h : 0 ≤ p.2
  · simpa [rootEndpoint,signedMove,T,a,h,abs_of_nonneg h] using pos.symm
  · have lt := lt_of_not_ge h
    simpa [rootEndpoint,signedMove,T,a,h,abs_of_neg lt,sub_eq_add_neg] using neg.symm

#print axioms inverse_word_root_jet
end MinimizingSard.Return
