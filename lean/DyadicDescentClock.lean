import RightSlopeNull

/-! Midpoints of dyadic cells, counted with their exact order.
Level j consists of the odd multiples of 2^(-(j+1)). -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace MinimizingSard.Clock

def clipped (t : ℝ) := max 0 (min 1 t)
def count (j : ℕ) (t : ℝ) : ℝ := (⌊(2:ℝ)^j * clipped t + 1/2⌋ : ℤ)
def clock (q t : ℝ) := ∑' j : ℕ, count j t * q^j

private theorem clip_eq {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : clipped t = t := by
  simp [clipped,min_eq_right ht.2,max_eq_right ht.1]

private theorem count_mono (j : ℕ) : Monotone (count j) := by
  intro t s h
  have hc : clipped t ≤ clipped s := max_le_max_left _ (min_le_min_left _ h)
  unfold count
  exact_mod_cast Int.floor_mono (add_le_add_right (mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ (2:ℝ)^j)) (1/2:ℝ))

private theorem count_bounds (j : ℕ) (t : ℝ) : 0 ≤ count j t ∧ count j t ≤ 2^j := by
  have h0 : 0 ≤ clipped t := le_max_left _ _
  have h1 : clipped t ≤ 1 := max_le zero_le_one (min_le_left _ _)
  have p : (0:ℝ) < 2^j := by positivity
  unfold count
  constructor
  · exact_mod_cast Int.floor_nonneg.mpr (show 0 ≤ (2:ℝ)^j * clipped t + 1/2 by positivity)
  · have h : ⌊(2:ℝ)^j * clipped t + 1/2⌋ ≤ (2:ℤ)^j := Int.floor_le_iff.mpr (by
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left h1 p.le])
    exact_mod_cast h

theorem clock_summable {q : ℝ} (hq : 0 ≤ q) (h : 2*q < 1) (t : ℝ) :
    Summable (fun j : ℕ => count j t * q^j) := by
  apply Summable.of_nonneg_of_le (fun j => mul_nonneg (count_bounds j t).1 (pow_nonneg hq j)) _
    (summable_geometric_of_lt_one (by positivity : 0 ≤ 2*q) h)
  intro j
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right (count_bounds j t).2 (pow_nonneg hq j)

theorem clock_measurable {q : ℝ} (hq : 0 ≤ q) (h : 2*q < 1) : Measurable (clock q) := by
  apply Monotone.measurable
  intro t s hts
  exact (clock_summable hq h t).tsum_le_tsum
    (fun j => mul_le_mul_of_nonneg_right (count_mono j hts) (pow_nonneg hq j)) (clock_summable hq h s)

def jumps (t s : ℝ) (j : ℕ) := count j s - count j t

/-- Finer levels in an interval of length at most 2^(-J) contribute
at most two times 2^m midpoints at level J+m. -/
theorem jump_bound {t s : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (hs : s ∈ Icc (0:ℝ) 1)
    (J m : ℕ) (width : (2:ℝ)^J * (s-t) ≤ 1) :
    jumps t s (J+m) ≤ 2 * (2:ℝ)^m := by
  have low := Int.lt_floor_add_one ((2:ℝ)^(J+m)*t + 1/2)
  have high := Int.floor_le ((2:ℝ)^(J+m)*s + 1/2)
  dsimp [jumps,count]
  rw [clip_eq ht,clip_eq hs]
  have bound := mul_le_mul_of_nonneg_right width (by positivity : 0 ≤ (2:ℝ)^m)
  have one : (1:ℝ) ≤ 2^m := one_le_pow₀ (by norm_num)
  rw [pow_add] at low high ⊢
  nlinarith

/-- Absolute displacement remaining after cutting off the fine levels.
The bound is uniform in the starting time. -/
theorem tail_bound {t s q : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (hs : s ∈ Icc (0:ℝ) 1)
    (hts : t ≤ s) (hq : 0 ≤ q) (h : 2*q < 1) (J L : ℕ)
    (width : (2:ℝ)^J * (s-t) ≤ 1) :
    (∑' m : ℕ, jumps t s (J+(L+m)) * q^(J+(L+m))) ≤
      (2*q^J*(2*q)^L) * (1-2*q)⁻¹ := by
  let C := 2*q^J*(2*q)^L
  have cs := (summable_geometric_of_lt_one (by positivity : 0 ≤ 2*q) h).mul_left C
  have bd (m : ℕ) : jumps t s (J+(L+m)) * q^(J+(L+m)) ≤ C * (2*q)^m := by
    calc
      _ ≤ (2 * (2:ℝ)^(L+m)) * q^(J+(L+m)) := mul_le_mul_of_nonneg_right
        (jump_bound ht hs J (L+m) width) (pow_nonneg hq _)
      _ = _ := by simp only [C,pow_add,mul_pow]; ring
  have pos (m : ℕ) : 0 ≤ jumps t s (J+(L+m)) * q^(J+(L+m)) :=
    mul_nonneg (sub_nonneg.mpr (count_mono _ hts)) (pow_nonneg hq _)
  have e := (Summable.of_nonneg_of_le pos bd cs).tsum_le_tsum bd cs
  rwa [tsum_mul_left,tsum_geometric_of_lt_one (by positivity : 0 ≤ 2*q) h] at e

private theorem floor_double (x : ℝ) : ⌊2*x⌋ = ⌊x⌋ + ⌊x+1/2⌋ := by
  have a := Int.floor_le x
  have b := Int.lt_floor_add_one x
  by_cases mid : x < (⌊x⌋ : ℝ) + 1/2
  · have eq : ⌊x+1/2⌋ = ⌊x⌋ := Int.floor_eq_iff.mpr ⟨by linarith,by linarith⟩
    rw [eq, Int.floor_eq_iff]
    push_cast
    constructor <;> linarith
  · have eq : ⌊x+1/2⌋ = ⌊x⌋ + 1 := Int.floor_eq_iff.mpr (by push_cast; constructor <;> linarith)
    rw [eq, Int.floor_eq_iff]
    push_cast
    constructor <;> linarith

private def grid (n : ℕ) (x : ℝ) : ℝ := (⌊(2:ℝ)^n * x⌋ : ℤ)

private theorem grid_next (n : ℕ) {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
    grid (n+1) x = grid n x + count n x := by
  simp only [grid,count,clip_eq hx,pow_succ']
  rw [mul_assoc,floor_double,Int.cast_add]

/-- The unique coarsest level contributes exactly one atom. All levels
before it contribute zero and its parent cell bounds the interval width. -/
theorem first_level {t s : ℝ} (ht : t ∈ Ico (0:ℝ) 1) (hs : s ∈ Ico (0:ℝ) 1)
    (hts : t < s) : ∃ J : ℕ, (∀ j < J, jumps t s j = 0) ∧
      jumps t s J = 1 ∧ (2:ℝ)^J * (s-t) < 1 := by
  classical
  have tc : t ∈ Icc (0:ℝ) 1 := ⟨ht.1,ht.2.le⟩
  have sc : s ∈ Icc (0:ℝ) 1 := ⟨hs.1,hs.2.le⟩
  have init : grid 0 s = grid 0 t := by simp [grid,Int.floor_eq_zero_iff.mpr ht,Int.floor_eq_zero_iff.mpr hs]
  have width (j : ℕ) (same : grid j s = grid j t) : (2:ℝ)^j * (s-t) < 1 := by
    have a := Int.floor_le ((2:ℝ)^j*t)
    have b := Int.lt_floor_add_one ((2:ℝ)^j*s)
    change (2:ℝ)^j*s < grid j s + 1 at b
    change grid j t ≤ (2:ℝ)^j*t at a
    rw [same] at b
    linarith only [a,b]
  have existsJ : ∃ j, jumps t s j ≠ 0 := by
    by_contra! allZero
    have eq (j : ℕ) : grid j s = grid j t := by
      induction j with
      | zero => exact init
      | succ n ih => rw [grid_next n sc,grid_next n tc,ih,sub_eq_zero.mp (allZero n)]
    obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (1/(s-t)) (by norm_num : (1:ℝ) < 2)
    exact (not_lt_of_ge (le_of_lt (width n (eq n)))) ((div_lt_iff₀ (sub_pos.mpr hts)).mp hn)
  let J := Nat.find existsJ
  have before (j : ℕ) (hj : j < J) : jumps t s j = 0 := not_not.mp (Nat.find_min existsJ hj)
  have eq (n : ℕ) (hn : n ≤ J) : grid n s = grid n t := by
    induction n with
    | zero => exact init
    | succ n ih => rw [grid_next n sc,grid_next n tc,ih (by omega),sub_eq_zero.mp (before n (by omega))]
  have narrow := width J (eq J le_rfl)
  refine ⟨J,before,?_,narrow⟩
  have nonzero := Nat.find_spec existsJ
  change jumps t s J ≠ 0 at nonzero
  let x := (2:ℝ)^J*t+1/2
  let y := (2:ℝ)^J*s+1/2
  have heq : jumps t s J = ((⌊y⌋ : ℤ) : ℝ) - ⌊x⌋ := by simp [jumps,count,clip_eq tc,clip_eq sc,x,y]
  have ne : ⌊y⌋ ≠ ⌊x⌋ := fun h => nonzero (by simp [heq,h])
  have mono : ⌊x⌋ ≤ ⌊y⌋ := Int.floor_mono (by dsimp [x,y]; gcongr)
  have le : ⌊y⌋ ≤ ⌊x⌋ + 1 := Int.floor_le_iff.mpr (by
    push_cast
    have h := Int.lt_floor_add_one x
    have dy : y-x < 1 := by dsimp [x,y]; linarith only [narrow]
    linarith)
  have one : ⌊y⌋ - ⌊x⌋ = 1 := by omega
  rw [heq]
  exact_mod_cast one

/-- Cutting the actual clock displacement after level J+L-1 leaves
a nonnegative error with an explicit geometric bound. -/
theorem clock_truncation {t s q : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (hs : s ∈ Icc (0:ℝ) 1)
    (hts : t ≤ s) (hq : 0 ≤ q) (h : 2*q < 1) (J L : ℕ)
    (width : (2:ℝ)^J*(s-t) ≤ 1) :
    let R := clock q s - clock q t - ∑ j ∈ Finset.range (J+L), jumps t s j * q^j
    0 ≤ R ∧ R ≤ (2*q^J*(2*q)^L) * (1-2*q)⁻¹ := by
  let f (j : ℕ) := jumps t s j * q^j
  have sf : Summable f := by
    simpa only [f,jumps,sub_mul] using (clock_summable hq h s).sub (clock_summable hq h t)
  have allSum : clock q s - clock q t = ∑' j, f j := by
    rw [clock,clock,← (clock_summable hq h s).tsum_sub (clock_summable hq h t)]
    simp only [f,jumps,sub_mul]
  dsimp only
  rw [allSum,← sf.sum_add_tsum_nat_add (J+L)]
  change 0 ≤ (∑ j ∈ Finset.range (J+L), f j) + _ - _ ∧ _
  simp only [show (∑ j ∈ Finset.range (J+L), jumps t s j*q^j) = ∑ j ∈ Finset.range (J+L), f j from rfl,
    add_sub_cancel_left]
  constructor
  · exact tsum_nonneg fun m => mul_nonneg (sub_nonneg.mpr (count_mono _ hts)) (pow_nonneg hq _)
  · simpa only [f,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using tail_bound ht hs hts hq h J L width

private theorem eventually_same {t : ℝ} (ht : t ∈ Ico (0:ℝ) 1) (j : ℕ) :
    ∀ᶠ s in 𝓝[>] t, jumps t s j = 0 := by
  let x := (2:ℝ)^j*t+1/2
  have cont : ContinuousAt (fun s : ℝ => (2:ℝ)^j*s+1/2) t := by fun_prop
  have near := cont.eventually_lt continuousAt_const (Int.lt_floor_add_one x)
  filter_upwards [Ioo_mem_nhdsGT ht.2, near.filter_mono nhdsWithin_le_nhds] with s hs hh
  have sc : s ∈ Icc (0:ℝ) 1 := ⟨ht.1.trans hs.1.le,hs.2.le⟩
  simp only [jumps,count,clip_eq sc,clip_eq (show t ∈ Icc (0:ℝ) 1 from ⟨ht.1,ht.2.le⟩)]
  have eq : ⌊(2:ℝ)^j*s+1/2⌋ = ⌊x⌋ := Int.floor_eq_iff.mpr ⟨(Int.floor_le x).trans
    (by dsimp [x]; gcongr; exact hs.1.le),hh⟩
  rw [eq]
  exact sub_self _

/-- Includes dyadic starting times: no jump at the starting time is counted. -/
theorem coarsest_escapes {t : ℝ} (ht : t ∈ Ico (0:ℝ) 1) (N : ℕ) :
    ∀ᶠ s in 𝓝[>] t, ∀ J : ℕ, jumps t s J ≠ 0 → N ≤ J := by
  have many := (Filter.eventually_all_finset (Finset.range N)).mpr (fun j _ => eventually_same ht j)
  filter_upwards [many] with s all
  intro J hj
  by_contra! bad
  exact hj (all J (Finset.mem_range.mpr bad))

/-- Convert the estimates at the leading atom into the right-hand slope
required by the translated slicing theorem. -/
theorem slope_of_leading_drop (g : ℝ → ℝ) {t c ρ : ℝ} (ht : t ∈ Ico (0:ℝ) 1)
    (hc : 0 < c) (hρ : 1 < 2*ρ)
    (drop : ∀ᶠ s in 𝓝[>] t, ∃ J : ℕ, jumps t s J ≠ 0 ∧ (2:ℝ)^J*(s-t) ≤ 1 ∧
      g s ≤ g t - c*ρ^J) : Tendsto (slope g t) (𝓝[>] t) atBot := by
  apply tendsto_atBot.mpr
  intro M
  obtain ⟨N,hN⟩ := pow_unbounded_of_one_lt ((|M|+1)/c) hρ
  filter_upwards [drop,coarsest_escapes ht N,self_mem_nhdsWithin] with s hs far right
  obtain ⟨J,hj,hw,hd⟩ := hs
  have ratio : (|M|+1)/c < (2*ρ)^J := hN.trans_le (pow_le_pow_right₀ hρ.le (far J hj))
  have big := (div_lt_iff₀ hc).mp ratio
  have hpos : 0 < s-t := sub_pos.mpr (show t < s from right)
  have hmul := mul_lt_mul_of_pos_right big hpos
  have hp : 0 ≤ c*ρ^J := mul_nonneg hc.le (pow_nonneg (by linarith) _)
  have small := mul_le_mul_of_nonneg_left hw hp
  rw [mul_pow] at hmul
  rw [slope_def_field,div_le_iff₀ hpos]
  have hm := mul_le_mul_of_nonneg_right (neg_le_abs M) hpos.le
  nlinarith only [small,hmul,hd,hm,hpos]

/-- Replace nominal intermediate points by points in the descent set.
The final point is prescribed, and may lie outside that set. A coordinate
error is charged only to the two steps incident to a displaced point. -/
theorem finite_box_descent {d N : ℕ} (k : Fin d → ℕ) (a : Fin d → ℝ)
    (E : Set (Fin d → ℝ)) (V : (Fin d → ℝ) → ℝ) (e c : ℝ)
    (p : ℕ → Fin d → ℝ) (s : ℕ → ℝ) (err : ℕ → Fin d → ℝ)
    (x y : Fin d → ℝ) (start : x ∈ E) (hN : 0 < N)
    (startErr : ∀ i, |x i - p 0 i| ≤ err 0 i)
    (lastErr : ∀ i, |y i - p N i| ≤ err N i)
    (hit : ∀ j, 0 < j → j < N → ∃ z ∈ E, ∀ i, |z i-p j i| ≤ err j i)
    (nominal : ∀ j < N, ∀ i, p (j+1) i - p j i = (s j)^(k i)*a i)
    (room : ∀ j < N, ∀ i, err (j+1) i + err j i < e*(s j)^(k i))
    (cheap : ∀ j < N, ∀ z ∈ E, ∀ v : Fin d → ℝ,
      (∀ i, |v i - (s j)^(k i)*a i| < e*(s j)^(k i)) → V (z+v) ≤ V z - c*s j) :
    V y ≤ V x - c * ∑ j ∈ Finset.range N, s j := by
  classical
  let z (j : ℕ) := if j = 0 then x else if j = N then y else
    if h : 0 < j ∧ j < N then (hit j h.1 h.2).choose else x
  have z0 : z 0 = x := by simp [z]
  have zN : z N = y := by simp [z,Nat.ne_of_gt hN]
  have mem (j : ℕ) (hj : j < N) : z j ∈ E := by
    by_cases h0 : j = 0
    · simpa [z,h0] using start
    · have h : 0 < j ∧ j < N := ⟨Nat.pos_of_ne_zero h0,hj⟩
      simpa [z,h0,hj.ne,h] using (hit j h.1 h.2).choose_spec.1
  have close (j : ℕ) (hj : j ≤ N) (i : Fin d) : |z j i - p j i| ≤ err j i := by
    rcases eq_or_ne j 0 with rfl | h0
    · rw [z0]; exact startErr i
    rcases hj.eq_or_lt with rfl | hj
    · rw [zN]; exact lastErr i
    have h : 0 < j ∧ j < N := ⟨Nat.pos_of_ne_zero h0,hj⟩
    simpa [z,h0,hj.ne,h] using (hit j h.1 h.2).choose_spec.2 i
  have step (j : ℕ) (hj : j < N) : V (z (j+1)) ≤ V (z j) - c*s j := by
    have fits (i : Fin d) : |(z (j+1)-z j) i - (s j)^(k i)*a i| < e*(s j)^(k i) := by
      rw [← nominal j hj i]
      change |z (j+1) i - z j i - (p (j+1) i - p j i)| < _
      have v := abs_sub_le (z (j+1) i - p (j+1) i) 0 (z j i - p j i)
      simp only [sub_zero,zero_sub,abs_neg] at v
      rw [show z (j+1) i - z j i - (p (j+1) i - p j i) =
        (z (j+1) i - p (j+1) i) - (z j i - p j i) by ring]
      exact (v.trans (add_le_add (close _ hj i) (close _ hj.le i))).trans_lt (room j hj i)
    simpa using cheap j hj (z j) (mem j hj) (z (j+1) - z j) fits
  have total (n : ℕ) (hn : n ≤ N) : V (z n) ≤ V x - c * ∑ j ∈ Finset.range n, s j := by
    induction n with
    | zero => simp [z0]
    | succ n ih =>
      have prev := ih (by omega)
      have next := step n (by omega)
      rw [Finset.sum_range_succ,mul_add]
      linarith
  simpa [zN] using total N le_rfl

/-- The same clock is used for every translate. Its coordinates may have
different geometric weights, and the box centre may have either sign. -/
theorem null_of_clock_chains {d : ℕ} (q a : Fin d → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hsmall : ∀ i, 2*q i < 1)
    (V : (Fin d → ℝ) → ℝ) (S : Set (Fin d → ℝ)) (hS : MeasurableSet S)
    {ρ c : ℝ} (hρ : 1 < 2*ρ) (hc : 0 < c)
    (chains : ∀ z t, t ∈ Ioo (0:ℝ) 1 → (z + fun i => a i * clock (q i) t) ∈ S →
      ∀ᶠ s in 𝓝[>] t, ∃ J : ℕ, jumps t s J ≠ 0 ∧ (2:ℝ)^J*(s-t) ≤ 1 ∧
        V (z + fun i => a i * clock (q i) s) ≤ V (z + fun i => a i * clock (q i) t) - c*ρ^J) :
    volume S = 0 := by
  let D (s : ℝ) (i : Fin d) := a i * clock (q i) s
  have meas : Measurable D := measurable_pi_lambda _ fun i => measurable_const.mul (clock_measurable (hq i) (hsmall i))
  apply Slicing.null_of_translated_clock hS V D meas
  intro z t ht hz
  exact slope_of_leading_drop _ ⟨ht.1.le,ht.2⟩ hc hρ (chains z t ht hz)

/-- A box of prescribed coordinate radii cannot be missed when its
volume exceeds the missing volume in the surrounding rectangle. This
uses the product of unequal coordinate lengths without a ball comparison. -/
theorem box_hits_of_missing_volume {d : ℕ} (E B : Set (Fin d → ℝ))
    (p w : Fin d → ℝ)
    (inside : (Set.pi univ (fun i => Ioo (p i - w i) (p i + w i))) ⊆ B)
    (missing : volume (B \ E) < ∏ i, ENNReal.ofReal (2*w i)) :
    ∃ z ∈ E, ∀ i, |z i - p i| < w i := by
  let R := Set.pi univ (fun i => Ioo (p i - w i) (p i + w i))
  have vol : volume R = ∏ i, ENNReal.ofReal (2*w i) := by
    dsimp only [R]
    rw [Real.volume_pi_Ioo]
    apply Finset.prod_congr rfl
    intro i _
    congr 1
    ring
  by_contra! empty
  have sub : R ⊆ B \ E := by
    intro z hz
    refine ⟨inside hz,fun he => ?_⟩
    obtain ⟨i,hi⟩ := empty z he
    have pair := hz i (mem_univ i)
    exact (not_lt.mpr hi) (abs_lt.mpr ⟨by linarith [pair.1],by linarith [pair.2]⟩)
  exact (not_le.mpr missing) (vol ▸ measure_mono sub)

/-- One concrete choice of the manuscript's geometric scales works
simultaneously for every integer weight at least two. -/
theorem weights_admissible (k : ℕ) (hk : 2 ≤ k) :
    1 < 2*(3/5:ℝ) ∧ 0 ≤ (3/5:ℝ)^k ∧ 2*(3/5:ℝ)^k < 1 := by
  have h := pow_le_pow_of_le_one (by norm_num : 0 ≤ (3/5:ℝ)) (by norm_num : (3/5:ℝ) ≤ 1) hk
  exact ⟨by norm_num,by positivity,by norm_num at h; linarith⟩

#print axioms box_hits_of_missing_volume
#print axioms weights_admissible
#print axioms finite_box_descent
#print axioms null_of_clock_chains
#print axioms clock_truncation
#print axioms coarsest_escapes
#print axioms slope_of_leading_drop
#print axioms first_level
#print axioms clock_summable
#print axioms clock_measurable
#print axioms jump_bound
#print axioms tail_bound
end MinimizingSard.Clock
