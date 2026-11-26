import Mathlib.Analysis.Calculus.Monotone
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! The precise one-sided Denjoy–Young–Saks exclusion used on each slice.
No continuity or measurability of the real-valued function is required. -/
namespace MinimizingSard.Slicing
open Filter Set MeasureTheory
open scoped Topology

private def risingUntil (f : ℝ → ℝ) (q : ℚ) : Set ℝ :=
  {x | x < (q : ℝ) ∧ ∀ y ∈ Ioo x (q : ℝ), f x ≤ f y}

private theorem rising_mono (f : ℝ → ℝ) (q : ℚ) :
    MonotoneOn f (risingUntil f q) := by
  intro x hx y hy hxy
  rcases hxy.eq_or_lt with rfl | h
  · exact le_rfl
  · exact hx.2 y ⟨h, hy.1⟩

/-- A right slope cannot tend to plus infinity on a set of positive
outer Lebesgue measure, including for nonmeasurable functions. -/
theorem right_slope_top_null (f : ℝ → ℝ) :
    volume {x | Tendsto (slope f x) (𝓝[>] x) atTop} = 0 := by
  rw [measure_eq_zero_iff_ae_notMem]
  have each (q : ℚ) : ∀ᵐ x : ℝ, x ∈ risingUntil f q →
      ¬ Tendsto (slope f x) (𝓝[>] x) atTop := by
    let s := risingUntil f q
    have outside := (countable_setOf_isolated_right_within (s := s)).ae_notMem
      (volume : Measure ℝ)
    filter_upwards [(rising_mono f q).ae_differentiableWithinAt_of_mem,
      outside]
      with x hd hi
    intro hx ht
    haveI : (𝓝[s ∩ Ioi x] x).NeBot := ⟨fun h => hi ⟨hx,h⟩⟩
    have deriv := (hd hx).hasDerivWithinAt
    have finiteSlope := (hasDerivWithinAt_iff_tendsto_slope' (s := s ∩ Ioi x)
      (by simp)).mp (deriv.mono inter_subset_left)
    have infiniteSlope := ht.mono_left (nhdsWithin_mono x
      (inter_subset_right : s ∩ Ioi x ⊆ Ioi x))
    exact not_tendsto_atTop_of_tendsto_nhds finiteSlope infiniteSlope
  filter_upwards [ae_all_iff.mpr each] with x hx
  intro ht
  have pos : ∀ᶠ y in 𝓝[>] x, 0 < slope f x y := ht.eventually_gt_atTop 0
  obtain ⟨b,hxb,hb⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp pos
  obtain ⟨q,hxq,hqb⟩ := exists_rat_btwn (show x < b from hxb)
  apply hx q ⟨hxq, ?_⟩ ht
  intro y hy
  have hs := hb (show y ∈ Ioo x b from ⟨hy.1, hy.2.trans hqb⟩)
  change 0 < slope f x y at hs
  rw [slope_def_field] at hs
  exact le_of_lt (sub_pos.mp ((div_pos_iff_of_pos_right (sub_pos.mpr hy.1)).mp hs))

/-- The descending version used for pointed energy and distance. -/
theorem right_slope_bot_null (f : ℝ → ℝ) :
    volume {x | Tendsto (slope f x) (𝓝[>] x) atBot} = 0 := by
  apply measure_mono_null _ (right_slope_top_null (fun x => -f x))
  intro x hx
  change Tendsto (slope (fun y => -f y) x) (𝓝[>] x) atTop
  have he : slope (fun y => -f y) x = fun y => -slope f x y := by
    funext y
    simp only [slope_def_field]
    ring
  rw [he]
  exact tendsto_neg_atBot_atTop.comp hx

#print axioms right_slope_top_null
#print axioms right_slope_bot_null

/-- Slicing by all translates of a *single* measurable clock. The
incidence set is measurable even when the composed cost has no assumed
regularity. The exceptional set returned is null for ambient volume. -/
theorem null_of_translated_clock {d : ℕ} {S : Set (Fin d → ℝ)} (hS : MeasurableSet S)
    (V : (Fin d → ℝ) → ℝ) (D : ℝ → (Fin d → ℝ)) (hD : Measurable D)
    (drop : ∀ z t, t ∈ Ioo (0 : ℝ) 1 → z + D t ∈ S →
      Tendsto (slope (fun s => V (z + D s)) t) (𝓝[>] t) atBot) : volume S = 0 := by
  let P (z : Fin d → ℝ) (t : ℝ) := t ∈ Ioo (0 : ℝ) 1 → z + D t ∉ S
  have measurableP : MeasurableSet {p : (Fin d → ℝ) × ℝ | P p.1 p.2} := by
    have meas := (measurable_snd (measurableSet_Ioo (a := (0 : ℝ)) (b := 1))).inter
      ((measurable_fst.add (hD.comp measurable_snd)) hS)
    convert meas.compl using 1
    ext p
    simp [P, not_and]
  have first : ∀ᵐ z : Fin d → ℝ, ∀ᵐ t : ℝ, P z t := by
    apply Filter.Eventually.of_forall
    intro z
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp
      (right_slope_bot_null (fun s => V (z + D s)))] with t h
    exact fun ht hs => h (drop z t ht hs)
  have second := (Measure.ae_ae_comm measurableP).mp first
  have pos : volume (Ioo (0 : ℝ) 1) ≠ 0 := by simp
  obtain ⟨t, ht, good⟩ := ((frequently_ae_mem_iff.mpr pos).and_eventually second).exists
  have nullPre : volume ((fun z => z + D t) ⁻¹' S) = 0 :=
    measure_eq_zero_iff_ae_notMem.mpr (good.mono (fun _ hz => hz ht))
  simpa only [measure_preimage_add_right] using nullPre

#print axioms null_of_translated_clock

private def raySet {d : ℕ} (V : (Fin d → ℝ) → ℝ) (w : Fin d → ℝ) (c r : ℝ) :=
  ⋂ a : Ioo (0 : ℝ) r, {y | V (y + (a : ℝ)^2 • w) ≤ V y - c * a}

private theorem raySet_null {d : ℕ} (V : (Fin d → ℝ) → ℝ) (hV : Continuous V)
    (w : Fin d → ℝ) {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    volume (raySet V w c r) = 0 := by
  have hS : IsClosed (raySet V w c r) := isClosed_iInter fun a =>
    isClosed_le (hV.comp (continuous_id.add continuous_const)) (hV.sub continuous_const)
  apply null_of_translated_clock hS.measurableSet V (fun t : ℝ => t • w) (by fun_prop)
  intro z t _ h
  apply tendsto_atBot.mpr
  intro M
  let b := min r (c / (|M| + 1))
  have hp : 0 < |M| + 1 := by positivity
  have hb : 0 < b := lt_min hr (div_pos hc hp)
  filter_upwards [Ioo_mem_nhdsGT (show t < t + b^2 by nlinarith [sq_pos_of_pos hb])] with s hs
  let a := Real.sqrt (s-t)
  have ha : 0 < a := Real.sqrt_pos.2 (sub_pos.mpr hs.1)
  have hsq : a^2 = s-t := Real.sq_sqrt (sub_nonneg.mpr hs.1.le)
  have hab : a < b := by nlinarith [hs.2]
  have haR : a < r := hab.trans_le (min_le_left _ _)
  have ac := (lt_div_iff₀ hp).mp (hab.trans_le (min_le_right _ _))
  have drop := mem_iInter.mp h (⟨a,ha,haR⟩ : Ioo (0 : ℝ) r)
  change V ((z + t • w) + a^2 • w) ≤ V (z + t • w) - c * a at drop
  rw [add_assoc, ← add_smul, hsq, add_sub_cancel] at drop
  rw [slope_def_field,div_le_iff₀ (sub_pos.mpr hs.1)]
  have bound : -M * a ≤ |M| * a := mul_le_mul_of_nonneg_right (neg_le_abs M) ha.le
  have ma : -M * a < c := by nlinarith
  have prod := mul_lt_mul_of_pos_right ma ha
  rw [← hsq]
  nlinarith

/-- The exceptional base points may choose their own saving, scale and
direction from a fixed countable list. No measurable choice of witnesses is needed. -/
theorem quadratic_ray_descent_null {d : ℕ} (V : (Fin d → ℝ) → ℝ) (hV : Continuous V)
    (w : ℕ → Fin d → ℝ) :
    volume {y | ∃ (i : ℕ) (c r : ℝ), 0 < c ∧ 0 < r ∧
      ∀ a ∈ Ioo (0 : ℝ) r, V (y + a^2 • w i) ≤ V y - c*a} = 0 := by
  let b (n : ℕ) : ℝ := 1 / (n + 1 : ℝ)
  have pos (n : ℕ) : 0 < b n := by dsimp [b]; positivity
  apply measure_mono_null (t := ⋃ i : ℕ, ⋃ n : ℕ, raySet V (w i) (b n) (b n))
  · rintro y ⟨i,c,r,hc,hr,save⟩
    obtain ⟨n,hn⟩ := exists_nat_one_div_lt (lt_min hc hr)
    change b n < min c r at hn
    refine mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨n,mem_iInter.mpr fun a => ?_⟩⟩
    have ha := save a ⟨a.2.1,a.2.2.trans (lt_min_iff.mp hn).2⟩
    exact ha.trans (sub_le_sub_left (mul_le_mul_of_nonneg_right (lt_min_iff.mp hn).1.le a.2.1.le) _)
  · exact measure_iUnion_null fun i => measure_iUnion_null fun n => raySet_null V hV (w i) (pos n) (pos n)

#print axioms quadratic_ray_descent_null
end MinimizingSard.Slicing
