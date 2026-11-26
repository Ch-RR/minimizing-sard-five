import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic.NormNum

/-! Two applications of one-dimensional density on transverse slices.
The coordinate scales may tend to zero at different rates. -/
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology
namespace MinimizingSard.Density

private def positiveSlice (S : Set ℝ) (x d r : ℝ) : Prop :=
  0 < volume (S ∩ closedBall (x+d) r)

private theorem interval_density (S : Set ℝ) (hs : MeasurableSet S)
    (d r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝[>] 0))
    (K : ℝ) (bound : ∀ j, |d j| ≤ K*r j) :
    ∀ᵐ x : ℝ, x ∈ S → ∀ᶠ j in atTop, positiveSlice S x (d j) (r j) := by
  apply (ae_restrict_iff' hs).mp
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div volume S K] with x good
  have near := good (fun j : ℕ => x+d j) r hr (.of_forall (fun j => by
    simpa [mem_closedBall,Real.dist_eq] using bound j))
  filter_upwards [near.eventually_const_lt (by norm_num : (0:ENNReal) < 1)] with j hj
  by_contra! z
  have eq : volume (S ∩ closedBall (x+d j) (r j)) = 0 := nonpos_iff_eq_zero.mp (le_of_not_gt z)
  simp [eq] at hj

private def vertical (S : Set (ℝ × ℝ)) (d r : ℝ) (p : ℝ × ℝ) :=
  positiveSlice (Prod.mk p.1 ⁻¹' S) p.2 d r

private theorem vertical_meas (S : Set (ℝ × ℝ)) (hs : MeasurableSet S) (d r : ℝ) :
    MeasurableSet {p | vertical S d r p} := by
  let U := {v : (ℝ × ℝ) × ℝ | (v.1.1,v.2) ∈ S ∧ dist v.2 (v.1.2+d) ≤ r}
  have mu : MeasurableSet U := ((measurable_fst.fst.prodMk measurable_snd) hs).inter
    (measurableSet_le (measurable_snd.dist (measurable_fst.snd.add_const d)) measurable_const)
  exact measurableSet_lt measurable_const (measurable_measure_prodMk_left (ν := volume) mu)

private theorem eventually_meas {P : ℕ → ℝ × ℝ → Prop} (hm : ∀ i, MeasurableSet {p | P i p}) :
    MeasurableSet {p | ∀ᶠ j in atTop, P j p} := by
  simp only [eventually_atTop,setOf_exists,setOf_forall]
  exact MeasurableSet.iUnion fun n => MeasurableSet.iInter fun j =>
    MeasurableSet.iInter fun _ => hm j

private theorem vertical_density (S : Set (ℝ × ℝ)) (hs : MeasurableSet S)
    (d r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝[>] 0)) (K : ℝ) (bound : ∀ j, |d j| ≤ K*r j) :
    ∀ᵐ p : ℝ × ℝ, p ∈ S → ∀ᶠ j in atTop, vertical S (d j) (r j) p := by
  have hm := eventually_meas (fun j => vertical_meas S hs (d j) (r j))
  have imp : MeasurableSet {p | p ∈ S → ∀ᶠ j in atTop, vertical S (d j) (r j) p} := by
    simpa only [imp_iff_not_or,setOf_or] using hs.compl.union hm
  apply (Measure.ae_prod_iff_ae_ae imp).mpr
  exact .of_forall fun x => interval_density _ (measurable_prodMk_left hs) d r hr K bound

/-- At almost every point of a measurable plane set, every sufficiently
late translated rectangle in the given sequence hits the set. Each
coordinate shift is bounded in units of its own radius. -/
theorem ae_rectangles_hit (S : Set (ℝ × ℝ)) (hs : MeasurableSet S)
    (d e r s : ℕ → ℝ) (hr : Tendsto r atTop (𝓝[>] 0)) (hs' : Tendsto s atTop (𝓝[>] 0))
    (K : ℝ) (dx : ∀ j, |d j| ≤ K*r j) (dy : ∀ j, |e j| ≤ K*s j) :
    ∀ᵐ p : ℝ × ℝ, p ∈ S → ∀ᶠ j in atTop, ∃ x y : ℝ, (x,y) ∈ S ∧
      dist x (p.1+d j) ≤ r j ∧ dist y (p.2+e j) ≤ s j := by
  let G (n : ℕ) := S ∩ {p | ∀ j ≥ n, vertical S (e j) (s j) p}
  have mg (n : ℕ) : MeasurableSet (G n) := by
    apply hs.inter
    simp only [setOf_forall]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => vertical_meas S hs _ _
  have hor (n : ℕ) : ∀ᵐ p : ℝ × ℝ, p ∈ G n → ∀ᶠ j in atTop,
      positiveSlice ((fun x : ℝ => (x,p.2)) ⁻¹' G n) p.1 (d j) (r j) := by
    let T := Prod.swap ⁻¹' G n
    have hh := vertical_density T (measurable_swap (mg n)) d r hr K dx
    exact (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).quasiMeasurePreserving.ae hh
  filter_upwards [vertical_density S hs e s hs' K dy,ae_all_iff.mpr hor] with p hv hh
  intro hp
  obtain ⟨n,hn⟩ := eventually_atTop.mp (hv hp)
  filter_upwards [hh n ⟨hp,hn⟩,eventually_ge_atTop n] with j pos jn
  obtain ⟨x,hx⟩ := nonempty_of_measure_ne_zero pos.ne'
  obtain ⟨y,hy⟩ := nonempty_of_measure_ne_zero ((hx.1.2 j jn).ne')
  exact ⟨x,y,hy.1,hx.2,hy.2⟩

#print axioms ae_rectangles_hit

/-- A single threshold works for all candidate vertices in the enlarged
rectangle, at every later scale. No eccentricity bound is required. -/
theorem ae_uniform_rectangles (S : Set (ℝ × ℝ)) (hS : MeasurableSet S)
    (r s : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0)) (hs : Tendsto s atTop (𝓝 0))
    (pr : ∀ j, 0 < r j) (ps : ∀ j, 0 < s j) (B η : ℝ) (hη : 0 < η) :
    ∀ᵐ p : ℝ × ℝ, p ∈ S → ∀ᶠ j in atTop,
      ∀ a b : ℝ, |a| ≤ B → |b| ≤ B → ∃ x y : ℝ, (x,y) ∈ S ∧
        dist x (p.1+a*r j) < η*r j ∧ dist y (p.2+b*s j) < η*s j := by
  let U := Icc (-B) B
  let e := η/2
  have ep : 0 < e := half_pos hη
  obtain ⟨D,sub,fin,cover⟩ := Metric.finite_approx_of_totallyBounded
    (s := U) isCompact_Icc.totallyBounded e ep
  haveI : Finite D := fin.to_subtype
  have pick (v : ℝ) (hv : |v| ≤ B) : ∃ u : D, dist v (u:ℝ) < e := by
    have m := cover (abs_le.mp hv)
    simp only [mem_iUnion,mem_ball] at m
    obtain ⟨u,hu,near⟩ := m
    exact ⟨⟨u,hu⟩,near⟩
  have scaled (f : ℕ → ℝ) (lim : Tendsto f atTop (𝓝 0)) (pos : ∀ j, 0 < f j) :
      Tendsto (fun j => e*f j) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨by simpa using (tendsto_const_nhds (x := e)).mul lim,.of_forall fun j => mul_pos ep (pos j)⟩
  have bd (a : D) (u : ℝ) (hu : 0 < u) : |(a:ℝ)*u| ≤ (B/e)*(e*u) := by
    have small := (abs_le.mpr (sub a.property) : |(a:ℝ)| ≤ B)
    rw [abs_mul,abs_of_pos hu,← mul_assoc,div_mul_cancel₀ _ ep.ne']
    exact mul_le_mul_of_nonneg_right small hu.le
  have one (a b : D) := ae_rectangles_hit S hS (fun j => (a:ℝ)*r j) (fun j => (b:ℝ)*s j)
    _ _ (scaled r hr pr) (scaled s hs ps) (B/e) (fun j => bd a _ (pr j)) (fun j => bd b _ (ps j))
  filter_upwards [Filter.eventually_all.mpr fun a => Filter.eventually_all.mpr (one a)] with p hp
  intro mem
  filter_upwards [Filter.eventually_all.mpr fun a => Filter.eventually_all.mpr fun b => hp a b mem] with j near
  intro a b ha hb
  obtain ⟨u,hu⟩ := pick a ha
  obtain ⟨v,hv⟩ := pick b hb
  obtain ⟨x,y,xy,hx,hy⟩ := near u v
  have enlarge {x p a u t : ℝ} (pt : 0 < t) (old : dist x (p+u*t) ≤ e*t)
      (approx : dist a u < e) : dist x (p+a*t) < η*t := by
    have second : dist (p+u*t) (p+a*t) = dist a u*t := by
      rw [dist_add_left,Real.dist_eq,← sub_mul,abs_mul,abs_of_pos pt,Real.dist_eq,abs_sub_comm]
    have more := add_lt_add_of_le_of_lt old (mul_lt_mul_of_pos_right approx pt)
    have tri := dist_triangle x (p+u*t) (p+a*t)
    rw [second] at tri
    dsimp [e] at more
    linarith
  exact ⟨x,y,xy,enlarge (pr j) hx hu,enlarge (ps j) hy hv⟩

#print axioms ae_uniform_rectangles
end MinimizingSard.Density
