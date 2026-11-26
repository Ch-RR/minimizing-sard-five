import ActualFrameFlow
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace MinimizingSard.Five

private theorem time_norm_sq {m : ℕ} (u : Control m) :
    ‖u‖^2 = ∫ s in (0:ℝ)..1, ‖u s‖^2 := by
  rw [Lp.norm_def,(Lp.memLp u).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  have id : (∫ s in Icc (0:ℝ) 1, ‖u s‖^2) = ∫ s in (0:ℝ)..1, ‖u s‖^2 := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    exact MeasureTheory.setIntegral_congr_set Ioc_ae_eq_Icc.symm
  have pos : 0 ≤ ∫ s in Icc (0:ℝ) 1, ‖u s‖^2 := integral_nonneg fun _ => sq_nonneg _
  simp only [ENNReal.toReal_ofNat,Real.rpow_two]
  rw [← one_div,← Real.sqrt_eq_rpow,ENNReal.toReal_ofReal (Real.sqrt_nonneg _),Real.sq_sqrt pos,id]

/-- A time-rescaled restriction of an original control exists in the
original L² space. Its squared norm is at most the time ratio times
the squared norm of the entire input, uniformly in the interval. -/
theorem rescaled_control {m : ℕ} (u : Control m) {a d : ℝ} (ha : 0 ≤ a) (hd : 0 < d) (end_le : a+d ≤ 1) :
    ∃ v : Control m, (∀ᵐ s ∂volume.restrict (Icc (0:ℝ) 1), v s = d • u (a+d*s)) ∧
      ‖v‖^2 = d * (∫ s in a..a+d, ‖u s‖^2) ∧ ‖v‖^2 ≤ d * ‖u‖^2 := by
  let g (s : ℝ) := d • u (a+d*s)
  let f (s : ℝ) := ‖u s‖^2
  have hi : IntervalIntegrable f volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr ((Lp.memLp u).integrable_norm_pow (p := 2) (by norm_num))
  have hab : a ≤ a+d := le_add_of_nonneg_right hd.le
  have sub := hi.mono_set (show uIcc a (a+d) ⊆ uIcc 0 1 by
    rw [uIcc_of_le hab,uIcc_of_le zero_le_one]; exact Icc_subset_Icc ha end_le)
  have shift : IntervalIntegrable (fun s => f (a+s)) volume 0 d := by simpa using sub.comp_add_left a
  have dil : IntervalIntegrable (fun s => f (a+d*s)) volume 0 1 := by
    simpa [hd.ne'] using shift.comp_mul_left (c := d)
  have val (s : ℝ) : ‖g s‖^2 = d^2 * f (a+d*s) := by simp [g,f,norm_smul,abs_of_pos hd,mul_pow]
  have sq : IntervalIntegrable (fun s => ‖g s‖^2) volume 0 1 :=
    (intervalIntegrable_congr (fun s _ => (val s).symm)).mp (dil.const_mul _)
  have meas : StronglyMeasurable g := (Lp.stronglyMeasurable u).comp_measurable
    (g := fun s : ℝ => a+d*s) (by fun_prop) |>.const_smul d
  have mem : MemLp g 2 (volume.restrict (Icc (0:ℝ) 1)) :=
    (memLp_two_iff_integrable_sq_norm meas.aestronglyMeasurable).mpr
      ((intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp sq)
  let v := mem.toLp g
  have repr := mem.coeFn_toLp
  have exact_sq : ‖v‖^2 = d * (∫ s in a..a+d, f s) := by
    rw [time_norm_sq]
    have ae : (fun s => ‖v s‖^2) =ᵐ[volume.restrict (Ioc (0:ℝ) 1)] (fun s => d^2 * f (a+d*s)) := by
      rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]
      filter_upwards [repr] with s hs
      exact (congrArg (fun y : Fiber m => ‖y‖^2) hs).trans (val s)
    have same := intervalIntegral.integral_congr_ae_restrict (a := (0:ℝ)) (b := 1) (μ := volume)
      (f := fun s => ‖v s‖^2) (g := fun s => d^2 * f (a+d*s))
      (by simpa only [uIoc_of_le zero_le_one] using ae)
    rw [same,intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_add_mul f hd.ne']
    simp only [mul_zero,mul_one,add_zero,smul_eq_mul]
    field_simp
  refine ⟨v,repr,exact_sq,?_⟩
  rw [exact_sq,time_norm_sq]
  exact mul_le_mul_of_nonneg_left (intervalIntegral.integral_mono_interval ha hab end_le
    (ae_of_all _ fun s => sq_nonneg ‖u s‖) hi) hd.le

#print axioms rescaled_control

/-- Rescaling is a single bounded linear operation on the original
space of equivalence classes, valid simultaneously for all variations. -/
theorem restriction_operator (m : ℕ) {a d : ℝ} (ha : 0 ≤ a) (hd : 0 < d) (he : a+d ≤ 1) :
    ∃ R : Control m →L[ℝ] Control m, ∀ u,
      (∀ᵐ s ∂volume.restrict (Icc (0:ℝ) 1), (R u) s = d • u (a+d*s)) ∧
      ‖R u‖^2 ≤ d * ‖u‖^2 := by
  choose r repr _ bound using fun u : Control m => rescaled_control u ha hd he
  let τ (s : ℝ) := a+d*s
  let μ := volume.restrict (Icc (0:ℝ) 1)
  have affine : Measure.QuasiMeasurePreserving τ (volume : Measure ℝ) volume :=
    (measurePreserving_add_left volume a).quasiMeasurePreserving.comp (Measure.quasiMeasurePreserving_smul volume hd.ne')
  have preserve : Measure.QuasiMeasurePreserving τ μ μ := affine.restrict (by
    intro s hs
    exact ⟨add_nonneg ha (mul_nonneg hd.le hs.1),(add_le_add_left (mul_le_of_le_one_right hd.le hs.2) a).trans he⟩)
  let R : Control m →ₗ[ℝ] Control m := {
    toFun := r
    map_add' := by
      intro u v
      apply Lp.ext
      filter_upwards [repr (u+v),repr u,repr v,preserve.ae (Lp.coeFn_add u v),Lp.coeFn_add (r u) (r v)]
        with s hw hu hv hs ht
      change (u+v) (a+d*s) = u (a+d*s)+v (a+d*s) at hs
      change (r u+r v) s = r u s+r v s at ht
      rw [hw,ht,hu,hv,hs,smul_add]
    map_smul' := by
      intro c u
      apply Lp.ext
      filter_upwards [repr (c • u),repr u,preserve.ae (Lp.coeFn_smul c u),Lp.coeFn_smul c (r u)]
        with s hw hu hs ht
      change (c • u) (a+d*s) = c • u (a+d*s) at hs
      change (r (c • u)) s = (c • r u) s
      rw [hw,ht]
      change d • ((c • u) (a+d*s)) = c • (r u s)
      rw [hu,hs,smul_comm]
  }
  have bnd (u : Control m) : ‖R u‖ ≤ 1 * ‖u‖ := by
    have step : d * ‖u‖^2 ≤ 1 * ‖u‖^2 := mul_le_mul_of_nonneg_right (by linarith : d ≤ 1) (sq_nonneg _)
    change ‖r u‖ ≤ _
    nlinarith [bound u,norm_nonneg u]
  exact ⟨R.mkContinuous 1 bnd,fun u => ⟨repr u,bound u⟩⟩

#print axioms restriction_operator

/-- A positive-duration restriction of an original chart trajectory is
itself an original Segment, with a quantitatively small control. -/
theorem subsegment {M : Type*} [TopologicalSpace M] [ChartedSpace State M] {m : ℕ}
    (e : Frame M m) (u : Control m) (z : ℝ → State)
    (cz : ContinuousOn z (Icc 0 1)) (mz : MapsTo z (Icc 0 1) e.chart.target)
    (integ : IntervalIntegrable (fun s => e.velocity (z s) (u s)) volume 0 1)
    (ode : ∀ t ∈ Icc (0:ℝ) 1, z t = z 0 + ∫ s in (0:ℝ)..t, e.velocity (z s) (u s))
    {a d : ℝ} (ha : 0 ≤ a) (hd : 0 < d) (end_le : a+d ≤ 1) :
    ∃ v : Control m, (∀ᵐ s ∂volume.restrict (Icc (0:ℝ) 1), v s = d • u (a+d*s)) ∧
      ‖v‖^2 ≤ d * ‖u‖^2 ∧ Segment e v (e.chart.symm (z a)) (e.chart.symm (z (a+d))) := by
  obtain ⟨v,rep,_,bound⟩ := rescaled_control u ha hd end_le
  let τ (s : ℝ) := a+d*s
  let f (s : ℝ) := e.velocity (z s) (u s)
  have maps (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : τ t ∈ Icc (0:ℝ) 1 :=
    ⟨add_nonneg ha (mul_nonneg hd.le ht.1), (add_le_add_left (mul_le_of_le_one_right hd.le ht.2) a).trans end_le⟩
  have a1 : a ≤ 1 := (le_add_of_nonneg_right hd.le).trans end_le
  have sub (b c : ℝ) (hb : 0 ≤ b) (hbc : b ≤ c) (hc : c ≤ 1) : IntervalIntegrable f volume b c :=
    integ.mono_set (by rw [uIcc_of_le hbc,uIcc_of_le zero_le_one]; exact Icc_subset_Icc hb hc)
  have shift : IntervalIntegrable (fun s => f (a+s)) volume 0 d := by
    simpa using (sub a (a+d) ha (le_add_of_nonneg_right hd.le) end_le).comp_add_left a
  have dil : IntervalIntegrable (fun s => f (τ s)) volume 0 1 := by
    simpa [τ,hd.ne'] using shift.comp_mul_left (c := d)
  have vr : (fun s => e.velocity (z (τ s)) (v s)) =ᵐ[volume.restrict (Icc (0:ℝ) 1)]
      (fun s => d • f (τ s)) := by
    filter_upwards [rep] with s hs
    simp [hs,τ,f,Frame.velocity,Finset.smul_sum,smul_smul]
  have ri (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      (fun s => e.velocity (z (τ s)) (v s)) =ᵐ[volume.restrict (uIoc (0:ℝ) t)] (fun s => d • f (τ s)) := by
    rw [uIoc_of_le ht.1]
    exact ae_mono (Measure.restrict_mono (fun s hs => ⟨hs.1.le,hs.2.trans ht.2⟩ : Ioc (0:ℝ) t ⊆ Icc 0 1)
      le_rfl) vr
  have za := mz (show a ∈ Icc (0:ℝ) 1 from ⟨ha,a1⟩)
  have ze := mz (show a+d ∈ Icc (0:ℝ) 1 from ⟨add_nonneg ha hd.le,end_le⟩)
  refine ⟨v,rep,bound,e.chart.map_target za,e.chart.map_target ze,z ∘ τ,cz.comp (by fun_prop) (fun t ht => maps t ht),
    fun t ht => mz (maps t ht),?_,?_,(intervalIntegrable_congr_ae (ri 1 (by norm_num))).mpr (dil.smul d),?_⟩
  · simp [τ,e.chart.right_inv za]
  · simp [τ,e.chart.right_inv ze]
  · intro t ht
    have diff := intervalIntegral.integral_add_adjacent_intervals (sub 0 a le_rfl ha a1)
      (sub a (τ t) ha (le_add_of_nonneg_right (mul_nonneg hd.le ht.1)) (maps t ht).2)
    change z (τ t) = z (τ 0) + ∫ s in (0:ℝ)..t, e.velocity (z (τ s)) (v s)
    rw [show τ 0 = a by simp [τ],intervalIntegral.integral_congr_ae_restrict (ri t ht),
      intervalIntegral.integral_smul,intervalIntegral.smul_integral_comp_add_mul f d a]
    rw [show a+d*0 = a by ring,ode _ (maps t ht),ode a ⟨ha,a1⟩]
    change z 0 + (∫ s in (0:ℝ)..(τ t), f s) = (z 0 + ∫ s in (0:ℝ)..a, f s) + ∫ s in a..τ t, f s
    rw [add_assoc,diff]

#print axioms subsegment

variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M]

def HasSmoothSegmentGraph {m : ℕ} (e : Frame M m) (n : ℕ) (p : State × Control m) : Prop :=
  ∃ F : State × Control m → State, ContDiffAt ℝ n F p ∧ ∀ᶠ b in 𝓝 p,
    b.1 ∈ e.chart.target ∧ F b ∈ e.chart.target ∧
    ∀ y, Segment e b.2 (e.chart.symm b.1) y ↔ y = e.chart.symm (F b)

/-- A single smallness threshold works at every base point of a compact
part of the chart. The endpoint graph varies smoothly in all inputs. -/
theorem compact_segment_graphs (e : Frame M 2) (n : ℕ) (hn : 1 ≤ (n : WithTop ℕ∞))
    (K : Set State) (hk : IsCompact K) (inside : K ⊆ e.chart.target) :
    ∃ ε > 0, ∀ x ∈ K, ∀ u : Control 2, ‖u‖ < ε → HasSmoothSegmentGraph e n (x,u) := by
  let V := {p | HasSmoothSegmentGraph e n p}
  have tube : K ×ˢ {(0 : Control 2)} ⊆ interior V := by
    rintro ⟨q,u⟩ ⟨hq,hu⟩
    change u = 0 at hu
    subst u
    obtain ⟨F,_,cs,graph⟩ := small_segment_endpoint e (inside hq) n hn
    let J (b : State × Control 2) := (b.1-q,b.2)
    have cJ : ContDiff ℝ n J := (contDiff_fst.sub contDiff_const).prodMk contDiff_snd
    have jq : J (q,0) = 0 := by apply Prod.ext <;> simp [J]
    have push : Tendsto J (𝓝 (q,0)) (𝓝 0) := jq ▸ cJ.continuous.tendsto (q,0)
    have df : ∀ᶠ b in 𝓝 (q,(0:Control 2)), ContDiffAt ℝ n (F ∘ J) b :=
      by
        filter_upwards [push (cs.eventually (by simp))] with b hb
        exact (show ContDiffAt ℝ n F (J b) from hb).comp b cJ.contDiffAt
    have gr : ∀ᶠ b : State × Control 2 in 𝓝 (q,0), b.1 ∈ e.chart.target ∧
        F (J b) ∈ e.chart.target ∧ ∀ y, Segment e b.2 (e.chart.symm b.1) y ↔ y = e.chart.symm (F (J b)) := by
      filter_upwards [push graph] with b hb
      have id : q+(J b).1 = b.1 := by change q+(b.1-q) = b.1; abel
      change q+(J b).1 ∈ e.chart.target ∧ F (J b) ∈ e.chart.target ∧
        ∀ y, Segment e b.2 (e.chart.symm (q+(J b).1)) y ↔ y = e.chart.symm (F (J b)) at hb
      rwa [id] at hb
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [df,eventually_eventually_nhds.mpr gr] with p hp localGraph
    exact ⟨F ∘ J,hp,localGraph⟩
  obtain ⟨s,w,_,hw,cover,hw0,prod⟩ := generalized_tube_lemma hk isCompact_singleton isOpen_interior tube
  obtain ⟨ε,hε,ball⟩ := Metric.mem_nhds_iff.mp (hw.mem_nhds (hw0 (mem_singleton _)))
  refine ⟨ε,hε,?_⟩
  intro x hx u hu
  have ub : u ∈ Metric.ball (0 : Control 2) ε := by rwa [Metric.mem_ball,dist_zero_right]
  have pin : (x,u) ∈ interior V := prod ⟨cover hx,ball ub⟩
  exact (interior_subset : interior V ⊆ V) pin

#print axioms compact_segment_graphs

/-- Every sufficiently short piece of an arbitrary original rank-two
reference has a smooth endpoint graph at its own rescaled control. -/
theorem arbitrary_reference_pieces (e : Frame M 2) (n : ℕ) (hn : 1 ≤ (n : WithTop ℕ∞))
    (u : Control 2) (z : ℝ → State) (cz : ContinuousOn z (Icc 0 1))
    (mz : MapsTo z (Icc 0 1) e.chart.target)
    (integ : IntervalIntegrable (fun s => e.velocity (z s) (u s)) volume 0 1)
    (ode : ∀ t ∈ Icc (0:ℝ) 1, z t = z 0 + ∫ s in (0:ℝ)..t, e.velocity (z s) (u s)) :
    ∃ δ > 0, ∀ a d : ℝ, 0 ≤ a → 0 < d → d < δ → a+d ≤ 1 →
      ∃ v : Control 2, (∀ᵐ s ∂volume.restrict (Icc (0:ℝ) 1), v s = d • u (a+d*s)) ∧
        HasSmoothSegmentGraph e n (z a,v) ∧
        Segment e v (e.chart.symm (z a)) (e.chart.symm (z (a+d))) := by
  obtain ⟨ε,hε,uniform⟩ := compact_segment_graphs e n hn (z '' Icc 0 1)
    (isCompact_Icc.image_of_continuousOn cz) (image_subset_iff.mpr mz)
  have pos : 0 < ‖u‖^2 + 1 := by positivity
  refine ⟨ε^2 / (‖u‖^2+1),div_pos (sq_pos_of_pos hε) pos,?_⟩
  intro a d ha hd hs he
  obtain ⟨v,repr,bound,seg⟩ := subsegment e u z cz mz integ ode ha hd he
  have lt := (lt_div_iff₀ pos).mp hs
  have small : ‖v‖ < ε := by nlinarith [sq_nonneg (‖v‖-ε),norm_nonneg v]
  exact ⟨v,repr,uniform _ ⟨a,⟨ha,(le_add_of_nonneg_right hd.le).trans he⟩,rfl⟩ v small,seg⟩

#print axioms arbitrary_reference_pieces
end MinimizingSard.Five
