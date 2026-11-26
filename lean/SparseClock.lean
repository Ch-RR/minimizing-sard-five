import DyadicDescentClock
import RectangleDensity

/-! A large integer radix permits distributing the entire fine tail
equally among the jumps of the first active level. -/
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology BigOperators
namespace MinimizingSard.Sparse

def digit (b j : ℕ) (t : ℝ) : ℤ := ⌊(b:ℝ)^j * max 0 (min 1 t)⌋
def value (b : ℕ) (q t : ℝ) := ∑' j : ℕ, (digit b j t : ℝ) * q^j

private theorem digit_eq {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (b j : ℕ) :
    digit b j t = ⌊(b:ℝ)^j*t⌋ := by simp [digit,min_eq_right ht.2,max_eq_right ht.1]

private theorem series (b : ℕ) (q t : ℝ) (hq : 0 ≤ q) (h : b*q < 1) :
    Summable (fun j : ℕ => (digit b j t : ℝ)*q^j) := by
  have bound (j : ℕ) : 0 ≤ (digit b j t : ℝ) ∧ (digit b j t : ℝ) ≤ (b:ℝ)^j := by
    constructor
    · exact_mod_cast Int.floor_nonneg.mpr (mul_nonneg (by positivity) (le_max_left _ _))
    · exact (Int.floor_le _).trans (mul_le_of_le_one_right (by positivity)
        (max_le zero_le_one (min_le_left _ _)))
  apply Summable.of_nonneg_of_le (fun j => mul_nonneg (bound j).1 (pow_nonneg hq _))
      _ (summable_geometric_of_lt_one (by positivity : 0 ≤ (b:ℝ)*q) h)
  intro j
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right (bound j).2 (pow_nonneg hq _)

theorem measurable_value (b : ℕ) (q : ℝ) (hq : 0 ≤ q) (h : b*q < 1) : Measurable (value b q) := by
  apply Monotone.measurable
  intro t s hts
  apply (series b q t hq h).tsum_le_tsum _ (series b q s hq h)
  intro j
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hq _)
  apply Int.cast_le.mpr
  exact Int.floor_mono (mul_le_mul_of_nonneg_left
    (max_le_max_left 0 (min_le_min_left 1 hts)) (show (0:ℝ) ≤ (b:ℝ)^j by positivity))

private theorem first (b : ℕ) (hb : 1 < b) {t s : ℝ} (ht : t ∈ Ioo (0:ℝ) 1)
    (hs : s ∈ Ioo t 1) :
    ∃ J : ℕ, (∀ j < J, digit b j s = digit b j t) ∧
      0 < digit b J s - digit b J t ∧ (b:ℝ)^J*(s-t) < b := by
  have tc : t ∈ Icc (0:ℝ) 1 := ⟨ht.1.le,ht.2.le⟩
  have sc : s ∈ Icc (0:ℝ) 1 := ⟨(ht.1.trans hs.1).le,hs.2.le⟩
  have width (j : ℕ) (eq : digit b j s = digit b j t) : (b:ℝ)^j*(s-t) < 1 := by
    have l := Int.floor_le ((b:ℝ)^j*t)
    have u := Int.lt_floor_add_one ((b:ℝ)^j*s)
    rw [← digit_eq sc b j,eq,digit_eq tc] at u
    linarith only [l,u]
  have ex : ∃ j, digit b j s ≠ digit b j t := by
    obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (1/(s-t)) (show (1:ℝ) < b by exact_mod_cast hb)
    exact ⟨n,fun eq => (not_lt_of_ge (width n eq).le) ((div_lt_iff₀ (sub_pos.mpr hs.1)).mp hn)⟩
  let J := Nat.find ex
  have before (j : ℕ) (hj : j < J) := not_not.mp (Nat.find_min ex hj)
  have diff : digit b J s ≠ digit b J t := Nat.find_spec ex
  have mono : digit b J t ≤ digit b J s := by
    rw [digit_eq tc,digit_eq sc]
    exact Int.floor_mono (mul_le_mul_of_nonneg_left hs.1.le (by positivity))
  have early : J ≠ 0 := by
    intro eq
    apply diff
    rw [eq,digit_eq sc,digit_eq tc]
    simp [Int.floor_eq_zero_iff.mpr (show s ∈ Ico (0:ℝ) 1 from ⟨sc.1,hs.2⟩),
      Int.floor_eq_zero_iff.mpr (show t ∈ Ico (0:ℝ) 1 from ⟨ht.1.le,ht.2⟩)]
  refine ⟨J,before,sub_pos.mpr (lt_of_le_of_ne mono diff.symm),?_⟩
  obtain ⟨k,ek⟩ := Nat.exists_eq_succ_of_ne_zero early
  have w := width k (before k (by omega))
  rw [ek,pow_succ']
  simpa [mul_assoc] using mul_lt_mul_of_pos_left w (show (0:ℝ) < b by exact_mod_cast (by omega : 0 < b))

/-- Error per leading atom after replacing the whole clock displacement
by equally sized pieces. The bound is independent of the number of atoms. -/
theorem equal_piece_error (b J : ℕ) (hb : 1 < b) {q t s : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) (hs : s ∈ Icc (0:ℝ) 1) (ts : t ≤ s)
    (hq : 0 < q) (small : (b:ℝ)*q < 1)
    (before : ∀ j < J, digit b j s = digit b j t)
    (pos : 0 < digit b J s - digit b J t) :
    let m : ℝ := (digit b J s : ℝ) - digit b J t
    |(value b q s - value b q t)/m - q^J| ≤
      q^J * (3*((b:ℝ)*q) / (1-(b:ℝ)*q)) := by
  let d (j : ℕ) : ℝ := (digit b j s : ℝ) - digit b j t
  have dm : 1 ≤ d J := by dsimp [d]; exact_mod_cast (show 1 ≤ digit b J s - digit b J t by omega)
  have dp : 0 < d J := zero_lt_one.trans_le dm
  have mono (j : ℕ) : 0 ≤ d j := by
    apply sub_nonneg.mpr
    exact_mod_cast (show digit b j t ≤ digit b j s by
      rw [digit_eq ht,digit_eq hs]
      exact Int.floor_mono (mul_le_mul_of_nonneg_left ts (by positivity)))
  have u (j : ℕ) : d j < (b:ℝ)^j*(s-t)+1 := by
    have lo := Int.lt_floor_add_one ((b:ℝ)^j*t)
    have hi := Int.floor_le ((b:ℝ)^j*s)
    simp only [d,digit_eq ht,digit_eq hs]
    linarith only [lo,hi]
  have w : (b:ℝ)^J*(s-t) < d J+1 := by
    have hi := Int.lt_floor_add_one ((b:ℝ)^J*s)
    have lo := Int.floor_le ((b:ℝ)^J*t)
    simp only [d,digit_eq ht,digit_eq hs]
    linarith only [lo,hi]
  let f (j : ℕ) := d j*q^j
  have sf : Summable f := by
    simpa only [f,d,sub_mul] using (series b q s hq.le small).sub (series b q t hq.le small)
  have total : value b q s - value b q t = ∑' j, f j := by
    rw [value,value,← (series b q s hq.le small).tsum_sub (series b q t hq.le small)]
    simp only [f,d,sub_mul]
  have early : ∑ j ∈ Finset.range J, f j = 0 :=
    Finset.sum_eq_zero fun j hj => by simp [f,d,before j (Finset.mem_range.mp hj)]
  let C := 3*d J*q^J*((b:ℝ)*q)
  have bs : 0 ≤ (b:ℝ)*q := by positivity
  have cs := (summable_geometric_of_lt_one bs small).mul_left C
  have bound (n : ℕ) : f (J+1+n) ≤ C*((b:ℝ)*q)^n := by
    have b1 : (1:ℝ) ≤ (b:ℝ)^(1+n) := one_le_pow₀ (by exact_mod_cast hb.le)
    have ww := mul_le_mul_of_nonneg_left w.le (zero_le_one.trans b1)
    have dd := u (J+1+n)
    rw [Nat.add_assoc,pow_add] at dd
    have prod := mul_le_mul_of_nonneg_left dm (zero_le_one.trans b1)
    have dj : d (J+1+n) ≤ 3*d J*(b:ℝ)^(1+n) := by
      rw [Nat.add_assoc]
      nlinarith only [dd,ww,prod,b1]
    calc
      _ ≤ (3*d J*(b:ℝ)^(1+n))*q^(J+1+n) := mul_le_mul_of_nonneg_right dj (pow_nonneg hq.le _)
      _ = _ := by simp only [C,pow_add,pow_one,mul_pow]; ring
  have tail := (Summable.of_nonneg_of_le (fun n => mul_nonneg (mono _) (pow_nonneg hq.le _)) bound cs).tsum_le_tsum bound cs
  rw [tsum_mul_left,tsum_geometric_of_lt_one bs small] at tail
  have low : 0 ≤ ∑' n, f (J+1+n) := tsum_nonneg fun n => mul_nonneg (mono _) (pow_nonneg hq.le _)
  have form := sf.sum_add_tsum_nat_add (J+1)
  rw [Finset.sum_range_succ,early,zero_add] at form
  dsimp only
  rw [total,← form]
  simp_rw [Nat.add_comm _ (J+1)]
  change |(d J*q^J + ∑' n, f (J+1+n))/d J-q^J| ≤ _
  rw [add_div,mul_div_cancel_left₀ _ dp.ne',add_sub_cancel_left,abs_of_nonneg (div_nonneg low dp.le)]
  apply (div_le_iff₀ dp).mpr
  apply tail.trans
  dsimp [C]
  rw [div_eq_mul_inv]
  exact le_of_eq (by ring)

#print axioms equal_piece_error

private abbrev Plane := Fin 2 → ℝ
private def Hits (E : Set Plane) (x v : Plane) (B η : ℝ) : Prop :=
  ∀ p : Plane, (∀ i, |p i-x i| ≤ B*v i) → ∃ z ∈ E, ∀ i, |z i-p i| ≤ η*v i

private theorem density (E : Set Plane) (hE : MeasurableSet E) (q : Plane)
    (qp : ∀ i, 0 < q i) (qs : ∀ i, q i < 1) (B η : ℝ) (hp : 0 < η) :
    ∀ᵐ x : Plane, x ∈ E → ∀ᶠ J : ℕ in atTop, Hits E x (fun i => q i^J) B η := by
  let T := @MeasurableEquiv.finTwoArrow ℝ _
  have meas := T.symm.measurable hE
  have plane := MinimizingSard.Density.ae_uniform_rectangles _ meas
    (fun n => q 0^n) (fun n => q 1^n)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (qp 0).le (qs 0))
    (tendsto_pow_atTop_nhds_zero_of_lt_one (qp 1).le (qs 1))
    (fun _ => pow_pos (qp 0) _) (fun _ => pow_pos (qp 1) _) B η hp
  filter_upwards [(volume_preserving_finTwoArrow ℝ).quasiMeasurePreserving.ae plane] with x hx
  intro mem
  have mx : T x ∈ T.symm ⁻¹' E := by simpa using mem
  filter_upwards [hx mx] with J hit
  intro p bd
  let u (i : Fin 2) := (p i-x i)/q i^J
  have pu (i : Fin 2) : |u i| ≤ B := by
    dsimp only [u]
    rw [abs_div,abs_of_pos (pow_pos (qp i) _),div_le_iff₀ (pow_pos (qp i) _)]
    exact bd i
  obtain ⟨a,b,mem',a0,b1⟩ := hit (u 0) (u 1) (pu 0) (pu 1)
  refine ⟨T.symm (a,b),mem',?_⟩
  have eq (i : Fin 2) : x i+u i*q i^J = p i := by
    dsimp only [u]
    rw [div_mul_cancel₀ _ (pow_pos (qp i) _).ne']; ring
  intro i
  fin_cases i
  · change |a-p 0| ≤ _
    change |a-(x 0+u 0*q 0^J)| < _ at a0
    rw [eq] at a0
    exact a0.le
  · change |b-p 1| ≤ _
    change |b-(x 1+u 1*q 1^J)| < _ at b1
    rw [eq] at b1
    exact b1.le

private theorem equal_chain (E : Set Plane) (V : Plane → ℝ) (x y a v : Plane)
    (m : ℕ) (hm : 0 < m) (c h e B : ℝ) (eh : 0 < e)
    (vp : ∀ i, 0 < v i) (mem : x ∈ E)
    (hit : Hits E x v B (e/8))
    (len : ∀ i, |y i-x i| ≤ B*v i)
    (approx : ∀ i, |(y i-x i)/(m:ℝ)-v i*a i| ≤ (e/4)*v i)
    (cheap : ∀ z ∈ E, ∀ w : Plane, (∀ i, |w i-v i*a i| < e*v i) → V (z+w) ≤ V z-c*h) :
    V y ≤ V x-(m:ℝ)*(c*h) := by
  let u (i : Fin 2) := (y i-x i)/(m:ℝ)
  let p (j : ℕ) (i : Fin 2) := x i + (j:ℝ)*u i
  have mp : (0:ℝ) < m := by exact_mod_cast hm
  have p0 : p 0 = x := by ext i; simp [p]
  have pm : p m = y := by
    ext i
    dsimp [p,u]
    field_simp
    ring
  have bound (j : ℕ) (hj : j ≤ m) (i : Fin 2) : |p j i-x i| ≤ B*v i := by
    simp only [p,add_sub_cancel_left,abs_mul,u,abs_div,abs_of_nonneg (Nat.cast_nonneg _ : (0:ℝ) ≤ j),abs_of_pos mp]
    calc
      _ ≤ (m:ℝ)*(|y i-x i|/m) := mul_le_mul_of_nonneg_right (by exact_mod_cast hj)
        (div_nonneg (abs_nonneg _) mp.le)
      _ = |y i-x i| := by field_simp
      _ ≤ _ := len i
  have choose (j : ℕ) (hj : j ≤ m) := hit (p j) (bound j hj)
  classical
  let z (j : ℕ) := if j = 0 then x else if j = m then y else if hj : j ≤ m then (choose j hj).choose else x
  have z0 : z 0 = x := by simp [z]
  have zm : z m = y := by simp [z,Nat.ne_of_gt hm]
  have cpos (i : Fin 2) : 0 ≤ e/8 * v i := mul_nonneg (by positivity) (vp i).le
  have err (j : ℕ) (hj : j ≤ m) (i : Fin 2) : |z j i-p j i| ≤ e/8*v i := by
    rcases eq_or_ne j 0 with rfl | hj0
    · simpa [z0,p0] using cpos i
    rcases hj.eq_or_lt with rfl | hlt
    · simpa [zm,pm] using cpos i
    · simp only [z,if_neg hj0,if_neg hlt.ne,dif_pos hj]
      exact (choose j hj).choose_spec.2 i
  have live (j : ℕ) (hj : j < m) : z j ∈ E := by
    rcases eq_or_ne j 0 with rfl | ne
    · simpa [z0] using mem
    · simpa [z,ne,hj.ne,hj.le] using (choose j hj.le).choose_spec.1
  have step (j : ℕ) (hj : j < m) : V (z (j+1)) ≤ V (z j)-c*h := by
    have applyCheap := cheap (z j) (live j hj) (z (j+1)-z j) (by
      intro i
      have en := abs_le.mp (err (j+1) hj i)
      have ec := abs_le.mp (err j hj.le i)
      have ap := abs_le.mp (approx i)
      change -(e/4*v i) ≤ u i-v i*a i ∧ u i-v i*a i ≤ e/4*v i at ap
      have shift : p (j+1) i = p j i + u i := by simp [p]; ring
      rw [shift] at en
      change |z (j+1) i-z j i-v i*a i| < _
      have extra : 0 < e*v i := mul_pos eh (vp i)
      rw [abs_lt]
      constructor <;> linarith only [en.1,en.2,ec.1,ec.2,ap.1,ap.2,extra])
    simpa using applyCheap
  have total (j : ℕ) (hj : j ≤ m) : V (z j) ≤ V x-(j:ℝ)*(c*h) := by
    induction j with
    | zero => simp [z0]
    | succ j ih =>
      have h1 := ih (by omega)
      have h2 := step j (by omega)
      push_cast
      linarith
  simpa [zm] using total m le_rfl


private theorem choose_radix (k : Fin 2 → ℕ) (hk : ∀ i, 2 ≤ k i) (a : Plane) (e : ℝ) (ep : 0 < e) :
    ∃ b : ℕ, 1 < b ∧ ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ (b:ℝ)*ρ = 2 ∧
      ∀ i, let z := (b:ℝ)*ρ^(k i)
           z < 1 ∧ |a i| * (3*z/(1-z)) ≤ e/4 := by
  obtain ⟨b,large⟩ := exists_nat_gt (max 8 (96*(‖a‖+1)/e))
  have big := lt_of_le_of_lt (le_max_left _ _) large
  have bp : (0:ℝ) < b := by linarith
  have hb : 1 < b := by exact_mod_cast (show (1:ℝ) < b by linarith)
  have lr := (div_lt_iff₀ ep).mp (lt_of_le_of_lt (le_max_right _ _) large)
  let ρ := 2/(b:ℝ)
  have pos : 0 < ρ := div_pos (by norm_num) bp
  have small : ρ < 1 := (div_lt_one bp).mpr (by linarith)
  have br : (b:ℝ)*ρ = 2 := by dsimp [ρ]; field_simp
  refine ⟨b,hb,ρ,pos,small,br,?_⟩
  intro i
  let z := (b:ℝ)*ρ^(k i)
  have low : 0 ≤ z := mul_nonneg bp.le (pow_nonneg pos.le _)
  have bound : z ≤ 4/(b:ℝ) := by
    apply (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one pos.le small.le (hk i)) bp.le).trans
    dsimp [ρ]
    apply le_of_eq
    field_simp
    ring
  have half : z < 1/2 := bound.trans_lt ((div_lt_iff₀ bp).mpr (by linarith))
  have ez : 3*z/(1-z) ≤ 6*z := (div_le_iff₀ (by linarith)).mpr (by nlinarith [mul_nonneg low (sub_nonneg.mpr half.le)])
  have est : |a i| ≤ ‖a‖ := by simpa using (norm_le_pi_norm a i)
  have app := (mul_le_mul_of_nonneg_left ez (abs_nonneg (a i))).trans
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left bound (by norm_num : (0:ℝ) ≤ 6)) (abs_nonneg _))
  refine ⟨by change z < 1; linarith,app.trans ?_⟩
  field_simp
  nlinarith only [lr,est]

private theorem stable_levels (b : ℕ) {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) (N : ℕ) :
    ∀ᶠ s in 𝓝[>] t, ∀ j < N, digit b j s = digit b j t := by
  have each (j : ℕ) : ∀ᶠ s in 𝓝[>] t, digit b j s = digit b j t := by
    have con : ContinuousAt (fun s : ℝ => (b:ℝ)^j*s) t := by fun_prop
    have upper := con.eventually_lt continuousAt_const (Int.lt_floor_add_one ((b:ℝ)^j*t))
    filter_upwards [Ioo_mem_nhdsGT ht.2,upper.filter_mono nhdsWithin_le_nhds] with s hs near
    rw [digit_eq ⟨(ht.1.trans hs.1).le,hs.2.le⟩,digit_eq ⟨ht.1.le,ht.2.le⟩]
    exact Int.floor_eq_iff.mpr ⟨(Int.floor_le _).trans (mul_le_mul_of_nonneg_left hs.1.le (by positivity)),near⟩
  simpa using (Filter.eventually_all_finset (Finset.range N)).mpr fun j _ => each j

/-- A measurable planar set on which a fixed genuine descent box is
available at every sufficiently small scale has measure zero. -/
theorem fixed_box_null (E : Set (Fin 2 → ℝ)) (hE : MeasurableSet E)
    (V : (Fin 2 → ℝ) → ℝ) (k : Fin 2 → ℕ) (hk : ∀ i, 2 ≤ k i)
    (a : Fin 2 → ℝ) (e c r : ℝ) (ep : 0 < e) (cp : 0 < c) (rp : 0 < r)
    (cheap : ∀ z ∈ E, ∀ h ∈ Ioo (0:ℝ) r, ∀ w : Fin 2 → ℝ,
      (∀ i, |w i-h^(k i)*a i| < e*h^(k i)) → V (z+w) ≤ V z-c*h) :
    volume E = 0 := by
  obtain ⟨b,hb,ρ,pos,small,br,good⟩ := choose_radix k hk a e ep
  let q (i : Fin 2) := ρ^(k i)
  have qp (i : Fin 2) : 0 < q i := pow_pos pos _
  have qs (i : Fin 2) : q i < 1 := pow_lt_one₀ pos.le small (by have := hk i; omega)
  let B := ((b:ℝ)+1)*(‖a‖+e/4)
  have hit := density E hE q qp qs B (e/8) (by positivity)
  let Fail := {x : Plane | ¬ (x ∈ E → ∀ᶠ J in atTop, Hits E x (fun i => q i^J) B (e/8))}
  have nf : volume Fail = 0 := measure_eq_zero_iff_ae_notMem.mpr (hit.mono fun _ h => not_not.mpr h)
  obtain ⟨N,subN,mN,nul⟩ := exists_measurable_superset_of_null nf
  suffices he : volume (E \ N) = 0 by
    exact measure_mono_null (t := (E \ N) ∪ N) (fun x hx => by by_cases h : x ∈ N <;> simp [hx,h])
      (measure_union_null he nul)
  let D (t : ℝ) (i : Fin 2) := a i*value b (q i) t
  apply MinimizingSard.Slicing.null_of_translated_clock (hE.diff mN) V D
    (measurable_pi_lambda _ fun i => measurable_const.mul (measurable_value _ _ (qp i).le (good i).1))
  intro z t ht hx
  let x := z+D t
  have notFail : x ∉ Fail := fun h => hx.2 (subN h)
  have goodHit := (not_not.mp notFail) hx.1
  obtain ⟨n,hn⟩ := eventually_atTop.mp goodHit
  have sizes := (tendsto_pow_atTop_nhds_zero_of_lt_one pos.le small).eventually_lt_const rp
  obtain ⟨n',hn'⟩ := eventually_atTop.mp sizes
  apply tendsto_atBot.mpr
  intro M
  obtain ⟨l,hl⟩ := pow_unbounded_of_one_lt (((|M|+1)*(b:ℝ))/c) (by norm_num : (1:ℝ)<2)
  filter_upwards [Ioo_mem_nhdsGT ht.2,stable_levels b ht (max n (max n' l))] with s hs stable
  obtain ⟨J,early,dp,width⟩ := first b hb ht hs
  have late : max n (max n' l) ≤ J := by
    by_contra! bad
    rw [stable J bad,sub_self] at dp
    exact lt_irrefl _ dp
  have jn := (le_max_left n (max n' l)).trans late
  have jn' := (le_max_left n' l).trans ((le_max_right n (max n' l)).trans late)
  have jl := (le_max_right n' l).trans ((le_max_right n (max n' l)).trans late)
  let m := (digit b J s-digit b J t).toNat
  have mp : 0 < m := by dsimp [m]; omega
  have mc : (m:ℝ) = (digit b J s : ℝ)-digit b J t := by exact_mod_cast Int.toNat_of_nonneg dp.le
  have mr : (0:ℝ) < m := by exact_mod_cast mp
  have tc : t ∈ Icc (0:ℝ) 1 := ⟨ht.1.le,ht.2.le⟩
  have sc : s ∈ Icc (0:ℝ) 1 := ⟨(ht.1.trans hs.1).le,hs.2.le⟩
  have mb : (m:ℝ) ≤ (b:ℝ)+1 := by
    have l0 := Int.lt_floor_add_one ((b:ℝ)^J*t)
    have u0 := Int.floor_le ((b:ℝ)^J*s)
    rw [mc,digit_eq tc,digit_eq sc]
    linarith only [u0,l0,width]
  let y := z+D s
  have app (i : Fin 2) : |(y i-x i)/m-q i^J*a i| ≤ (e/4)*q i^J := by
    have bound := equal_piece_error b J hb tc sc hs.1.le (qp i) (good i).1 early dp
    change |(value b (q i) s-value b (q i) t)/_-_| ≤ _ at bound
    rw [← mc] at bound
    have eq : (y i-x i)/m-q i^J*a i = a i*((value b (q i) s-value b (q i) t)/m-q i^J) := by
      change ((z i+_)-(z i+_))/_-_=_
      dsimp [D]
      ring
    rw [eq,abs_mul]
    apply (mul_le_mul_of_nonneg_left bound (abs_nonneg _)).trans
    have use := mul_le_mul_of_nonneg_right (good i).2 (pow_nonneg (qp i).le J)
    change |a i| * (3*((b:ℝ)*q i)/(1-(b:ℝ)*q i))*q i^J ≤ (e/4)*q i^J at use
    linarith only [use]
  have lengthBound (i : Fin 2) : |y i-x i| ≤ B*q i^J := by
    have norm : |a i| ≤ ‖a‖ := by simpa using norm_le_pi_norm a i
    have qpos := (pow_pos (qp i) J).le
    have w := abs_sub_le ((y i-x i)/(m:ℝ)) (q i^J*a i) 0
    simp only [sub_zero,abs_mul,abs_of_nonneg qpos] at w
    have ub : |y i-x i| / (m:ℝ) ≤ (‖a‖+e/4)*q i^J := by
      rw [abs_div,abs_of_pos mr] at w
      linarith only [w,app i,mul_le_mul_of_nonneg_left norm qpos]
    have lim := (div_le_iff₀ mr).mp ub
    apply lim.trans
    have mult := mul_le_mul_of_nonneg_right mb (mul_nonneg (by positivity : 0 ≤ ‖a‖+e/4) qpos)
    dsimp [B]
    linarith only [mult]
  have same (i : Fin 2) : (ρ^J)^(k i) = q i^J := by simp [q,← pow_mul,Nat.mul_comm]
  have save := equal_chain E V x y a (fun i => q i^J) m mp c (ρ^J) e B ep (fun i => pow_pos (qp i) _)
    hx.1 (hn J jn) lengthBound app (by simpa only [same] using fun z hz => cheap z hz (ρ^J) ⟨pow_pos pos _,hn' J jn'⟩)
  change slope (fun u => V (z+D u)) t s ≤ M
  rw [slope_def_field,div_le_iff₀ (sub_pos.mpr hs.1)]
  change V y - V x ≤ M*(s-t)
  have m1 : (1:ℝ) ≤ m := by exact_mod_cast mp
  have weak := mul_le_mul_of_nonneg_right m1 (mul_nonneg cp.le (pow_pos pos J).le)
  have big := (div_lt_iff₀ cp).mp (hl.trans_le (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) jl))
  rw [← br,mul_pow] at big
  have w1 := mul_le_mul_of_nonneg_left width.le (abs_nonneg M)
  have bp : (0:ℝ) < (b:ℝ)^J := pow_pos (by exact_mod_cast (by omega : 0 < b)) _
  have w2 := mul_le_mul_of_nonneg_right (neg_le_abs M) (sub_pos.mpr hs.1).le
  have need : |M| * (s-t) ≤ c*ρ^J := by
    apply (le_of_mul_le_mul_left _ bp)
    nlinarith only [big,w1,show (0:ℝ) ≤ b by positivity]
  linarith only [save,weak,need,w2]

#print axioms fixed_box_null


private def bases (V : Plane → ℝ) (k : Fin 2 → ℕ) (a : Plane) (e c r : ℝ) :=
  ⋂ h : Ioo (0:ℝ) r, ⋂ w : {w : Plane // ∀ i, |w i-(h:ℝ)^(k i)*a i| < e*(h:ℝ)^(k i)},
    {x : Plane | V (x+w) ≤ V x-c*h}

private def width (n : ℕ) : ℝ := 1/(n+1:ℝ)
private theorem width_pos (n : ℕ) : 0 < width n := by dsimp [width]; positivity

def descentSet (V : (Fin 2 → ℝ) → ℝ) (k : Fin 2 → ℕ) :=
  {x : Fin 2 → ℝ | ∃ a : Fin 2 → ℝ, ∃ e c r : ℝ, 0 < e ∧ 0 < c ∧ 0 < r ∧
    ∀ h ∈ Ioo (0:ℝ) r, ∀ w : Fin 2 → ℝ,
      (∀ i, |w i-h^(k i)*a i| < e*h^(k i)) → V (x+w) ≤ V x-c*h}

private theorem rational_cover (V : Plane → ℝ) (k : Fin 2 → ℕ) :
    descentSet V k ⊆ ⋃ A : Fin 2 → ℚ, ⋃ n : ℕ, bases V k (fun i => (A i:ℝ)) (width n) (width n) (width n) := by
  rintro x ⟨a,e,c,r,ep,cp,rp,save⟩
  have choose (i : Fin 2) := exists_rat_btwn (show a i-e/2 < a i+e/2 by linarith)
  choose A lo hi using choose
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt (lt_min (half_pos ep) (lt_min cp rp))
  change width n < min (e/2) (min c r) at hn
  obtain ⟨he,cr⟩ := lt_min_iff.mp hn
  obtain ⟨hc,hr⟩ := lt_min_iff.mp cr
  refine mem_iUnion.mpr ⟨A,mem_iUnion.mpr ⟨n,mem_iInter.mpr fun h => mem_iInter.mpr fun w => ?_⟩⟩
  have use := save h ⟨h.2.1,h.2.2.trans hr⟩ w (by
    intro i
    let H := (h:ℝ)^(k i)
    have Hpos : 0 < H := pow_pos h.2.1 _
    have diff : |(A i:ℝ)-a i| < e/2 := abs_lt.mpr ⟨by linarith only [lo i],by linarith only [hi i]⟩
    have tri := abs_sub_le (w.val i) (H*(A i:ℝ)) (H*a i)
    rw [← mul_sub,abs_mul,abs_of_pos Hpos] at tri
    have fit := w.property i
    change |w.val i-H*(A i:ℝ)| < width n*H at fit
    have s1 := mul_lt_mul_of_pos_right he Hpos
    have s2 := mul_lt_mul_of_pos_left diff Hpos
    change |w.val i-H*a i| < e*H
    linarith only [tri,fit,s1,s2])
  exact use.trans (sub_le_sub_left (mul_le_mul_of_nonneg_right hc.le h.2.1.le) _)

/-- The center, width, saving and cutoff may vary arbitrarily with the
base point. No measurable choice of witnesses is required. -/
theorem planar_descent_null (V : (Fin 2 → ℝ) → ℝ) (continuousV : Continuous V)
    (k : Fin 2 → ℕ) (hk : ∀ i, 2 ≤ k i) : volume (descentSet V k) = 0 := by
  apply measure_mono_null (rational_cover V k)
  apply measure_iUnion_null
  intro a
  apply measure_iUnion_null
  intro n
  let S := bases V k (fun i => (a i:ℝ)) (width n) (width n) (width n)
  have cl : IsClosed S := isClosed_iInter fun h => isClosed_iInter fun w =>
    isClosed_le (continuousV.comp (continuous_id.add continuous_const)) (continuousV.sub continuous_const)
  apply fixed_box_null S cl.measurableSet V k hk _ _ _ _ (width_pos n) (width_pos n) (width_pos n)
  intro x hx h hh w hw
  exact mem_iInter.mp (mem_iInter.mp hx (⟨h,hh⟩ : Ioo (0:ℝ) (width n))) ⟨w,hw⟩

/-- Outer nullity on parallel two-planes in product coordinates on
five-space, allowing all descent data to depend on the ambient point. -/
theorem parallel_planes_null (V : (Fin 3 → ℝ) × (Fin 2 → ℝ) → ℝ) (cV : Continuous V)
    (k : Fin 2 → ℕ) (hk : ∀ i, 2 ≤ k i) :
    volume {p : (Fin 3 → ℝ) × (Fin 2 → ℝ) | p.2 ∈ descentSet (fun y => V (p.1,y)) k} = 0 := by
  let S (A : Fin 2 → ℚ) (n : ℕ) :=
    {p : (Fin 3 → ℝ) × Plane | p.2 ∈ bases (fun y => V (p.1,y)) k (fun i => (A i:ℝ)) (width n) (width n) (width n)}
  apply measure_mono_null (t := ⋃ A : Fin 2 → ℚ, ⋃ n : ℕ, S A n)
  · intro p hp
    have cover := rational_cover (fun y => V (p.1,y)) k (a := p.2) hp
    obtain ⟨a,ha⟩ := mem_iUnion.mp cover
    obtain ⟨n,hn⟩ := mem_iUnion.mp ha
    exact mem_iUnion.mpr ⟨a,mem_iUnion.mpr ⟨n,hn⟩⟩
  · apply measure_iUnion_null
    intro A
    apply measure_iUnion_null
    intro n
    let T := ⋂ h : Ioo (0:ℝ) (width n),
      ⋂ w : {w : Plane // ∀ i, |w i-(h:ℝ)^(k i)*(A i:ℝ)| < width n*(h:ℝ)^(k i)},
        {p : (Fin 3 → ℝ) × Plane | V (p.1,p.2+w) ≤ V p-width n*h}
    have eq : S A n = T := by ext p; simp [S,T,bases]
    have cl : IsClosed T := isClosed_iInter fun h => isClosed_iInter fun w =>
      isClosed_le (cV.comp (continuous_fst.prodMk (continuous_snd.add continuous_const))) (cV.sub continuous_const)
    rw [Measure.volume_eq_prod,Measure.prod_apply (eq ▸ cl.measurableSet)]
    apply lintegral_eq_zero_of_ae_eq_zero
    apply Filter.Eventually.of_forall
    intro p
    have cv : Continuous (fun y : Plane => V (p,y)) := cV.comp (continuous_const.prodMk continuous_id)
    apply measure_mono_null _ (planar_descent_null (fun y => V (p,y)) cv k hk)
    intro y hy
    refine ⟨fun i => (A i:ℝ),width n,width n,width n,width_pos n,width_pos n,width_pos n,?_⟩
    intro h hh w hw
    exact mem_iInter.mp (mem_iInter.mp hy (⟨h,hh⟩ : Ioo (0:ℝ) (width n))) ⟨w,hw⟩

#print axioms parallel_planes_null

#print axioms planar_descent_null

end MinimizingSard.Sparse
