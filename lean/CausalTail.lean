import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Terminal localization of finite-rank causal operators on actual L².
The endpoints of the unit interval have zero Lebesgue measure. -/
noncomputable section
open Set Filter MeasureTheory
namespace MinimizingSard.Causal
abbrev timeMeasure := volume.restrict (Ioo (0 : ℝ) 1)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
abbrev Signals (E : Type*) [NormedAddCommGroup E] := Lp E 2 timeMeasure

def tail (q : ℝ) : Submodule ℝ (Signals E) where
  carrier := {u | ∀ᵐ t ∂timeMeasure, t < q → u t = 0}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero E 2 timeMeasure] with t ht using fun _ => ht
  add_mem' := by
    intro u v hu hv
    filter_upwards [hu, hv, Lp.coeFn_add u v] with t ht hs he using
      fun h => he.trans (by simp [ht h,hs h])
  smul_mem' := by
    intro r u hu
    filter_upwards [hu,Lp.coeFn_smul r u] with t ht he using
      fun h => he.trans (by simp [ht h])

theorem tail_antitone : Antitone (tail (E := E)) := by
  intro a b hab u hu
  change ∀ᵐ t ∂timeMeasure, t < a → u t = 0
  change ∀ᵐ t ∂timeMeasure, t < b → u t = 0 at hu
  filter_upwards [hu] with t ht using fun h => ht (h.trans_le hab)

private theorem zero_of_all_tails (u : Signals E)
    (hu : ∀ q : ℚ, (q : ℝ) < 1 → u ∈ tail (q : ℝ)) : u = 0 := by
  apply Lp.ext
  apply Filter.EventuallyEq.trans _ (Lp.coeFn_zero E 2 timeMeasure).symm
  have atRat (q : ℚ) : ∀ᵐ (t : ℝ) ∂timeMeasure, (q : ℝ) < 1 → t < (q : ℝ) → u t = 0 := by
    by_cases h : (q : ℝ) < 1
    · have v : ∀ᵐ (t : ℝ) ∂timeMeasure, t < (q : ℝ) → u t = 0 := hu q h
      filter_upwards [v] with t ht using fun _ => ht
    · exact Filter.Eventually.of_forall fun _ h' => (h h').elim
  filter_upwards [ae_all_iff.mpr atRat, ae_restrict_mem (μ := volume)
    (measurableSet_Ioo (a := (0 : ℝ)) (b := 1))] with t ht hm
  obtain ⟨q,htq,hq⟩ := exists_rat_btwn hm.2
  exact ht q hq htq

/-- Causality means that signals supported after any cut have outputs
supported after that same cut. Finite rank forces exact annihilation
of all signals supported on some nonempty terminal subinterval. -/
theorem terminal_annihilation (T : Signals E →ₗ[ℝ] Signals E)
    [FiniteDimensional ℝ (LinearMap.range T)]
    (causal : ∀ q : ℝ, Submodule.map T (tail q) ≤ tail q) :
    ∃ q : ℚ, (q : ℝ) < 1 ∧ ∀ u ∈ tail (q : ℝ), T u = 0 := by
  classical
  let im (q : ℚ) := Submodule.map T (tail (q : ℝ))
  have anti : Antitone im := fun _ _ h =>
    Submodule.map_mono (tail_antitone (by exact_mod_cast h))
  let P (n : ℕ) := ∃ q : ℚ, (q : ℝ) < 1 ∧ Module.finrank ℝ (im q) = n
  have ex : ∃ n, P n := ⟨_, 0, by norm_num, rfl⟩
  obtain ⟨q,hq,hmin⟩ := Nat.find_spec ex
  have incl : im q ≤ LinearMap.range T := by
    rintro _ ⟨w,_,rfl⟩
    exact ⟨w,rfl⟩
  haveI : FiniteDimensional ℝ (im q) :=
    FiniteDimensional.of_injective
      (Submodule.inclusion incl)
      (Submodule.inclusion_injective _)
  refine ⟨q,hq,fun u hu => zero_of_all_tails (T u) ?_⟩
  intro r hr
  have him : T u ∈ im q := ⟨u,hu,rfl⟩
  by_cases hqr : q ≤ r
  · have eq : im r = im q := Submodule.eq_of_le_of_finrank_le (anti hqr) (by
      rw [hmin]
      exact Nat.find_min' ex ⟨r,hr,rfl⟩)
    exact causal r (eq.symm ▸ him : T u ∈ im r)
  · exact tail_antitone (by exact_mod_cast (le_of_not_ge hqr)) (causal q him)

#print axioms terminal_annihilation

def pulse (a b : ℝ) (c : E) : Signals E :=
  indicatorConstLp 2 (s := Ioo a b) measurableSet_Ioo measure_Ioo_lt_top.ne c

private theorem pulse_in_tail {q a b : ℝ} (hqa : q ≤ a) (c : E) :
    pulse a b c ∈ tail q := by
  change ∀ᵐ t ∂timeMeasure, t < q → pulse a b c t = 0
  filter_upwards [indicatorConstLp_coeFn_notMem (μ := timeMeasure) (p := 2)
    (s := Ioo a b) (hs := measurableSet_Ioo) (hμs := measure_Ioo_lt_top.ne)
    (c := c)] with t ht
  exact fun h => ht (fun hm => (h.trans_le hqa).not_ge hm.1.le)

/-- Identify the kernel from the actual L² operator using interval pulses.
The first kernel variable is output time, the second input time. Only
the measured response after a pulse has ended is required. -/
theorem terminal_kernel_zero (T : Signals E →ₗ[ℝ] Signals E)
    [FiniteDimensional ℝ (LinearMap.range T)]
    (causal : ∀ q : ℝ, Submodule.map T (tail q) ≤ tail q) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧
    ∀ (c : E) (p : E →ₗ[ℝ] ℝ) (K : ℝ → ℝ → ℝ), Continuous K.uncurry →
      (∀ a b : ℝ, 0 < a → a < b → b < 1 →
        ∀ᵐ t ∂volume.restrict (Ioo b 1), p (T (pulse a b c) t) = ∫ s in a..b, K t s) →
      ∀ s t : ℝ, r < s → s < t → t < 1 → K t s = 0 := by
  obtain ⟨q,hq,hzero⟩ := terminal_annihilation T causal
  let r := max 0 (q : ℝ)
  have hr : 0 ≤ r := le_max_left _ _
  refine ⟨r, hr, max_lt (by norm_num) hq, ?_⟩
  intro c p K hc response s t hrs hst ht
  obtain ⟨a,hra,has⟩ := exists_between hrs
  have intZero (b : ℝ) (hab : a < b) (hbt : b < t) :
      (∫ x in a..b, K t x) = 0 := by
    have tz := hzero (pulse a b c) (pulse_in_tail ((le_max_right _ _).trans hra.le) c)
    have eq := response a b (hr.trans_lt hra) hab (hbt.trans ht)
    rw [tz] at eq
    have sub : Ioo b 1 ⊆ Ioo (0 : ℝ) 1 :=
      fun x hx => ⟨((hr.trans_lt hra).trans hab).trans hx.1,hx.2⟩
    have aeZero := ae_restrict_of_ae_restrict_of_subset sub (Lp.coeFn_zero E 2 timeMeasure)
    have eqInt : (fun y => ∫ x in a..b, K y x) =ᵐ[volume.restrict (Ioo b 1)]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [eq,aeZero] with y hy hy0
      change (0 : Signals E) y = 0 at hy0
      rw [hy0, map_zero] at hy
      exact hy.symm
    have cont := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) hc a b
    exact Measure.eqOn_Ioo_of_ae_eq volume eqInt cont.continuousOn continuousOn_const
      (show t ∈ Ioo b 1 from ⟨hbt,ht⟩)
  have loc : (fun b => ∫ x in a..b, K t x) =ᶠ[nhds s] (fun _ => (0 : ℝ)) :=
    Filter.eventually_of_mem (Ioo_mem_nhds has hst) (fun b hb => intZero b hb.1 hb.2)
  have contS : Continuous (K t) := hc.comp (continuous_const.prodMk continuous_id)
  have deriv := intervalIntegral.integral_hasDerivAt_right (contS.intervalIntegrable a s)
    (contS.stronglyMeasurableAtFilter volume (nhds s)) contS.continuousAt
  exact deriv.unique ((hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq loc)

#print axioms terminal_kernel_zero
end MinimizingSard.Causal
