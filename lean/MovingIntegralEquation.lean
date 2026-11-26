import ChartTangentFlow
import EndpointComposition
import Mathlib.MeasureTheory.Function.JacobianOneDim

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace MinimizingSard.Five
open Volterra

private theorem monotone_increment {a b : ℝ} (ab : a ≤ b) (G d : ℝ → ℝ)
    (mono : MonotoneOn G (Icc a b))
    (der : ∀ᵐ t ∂volume, t ∈ Ioo a b → HasDerivAt G (d t) t) :
    (∫ s in a..b, d s) ≤ G b - G a := by
  obtain ⟨N,bad,mN,null⟩ := exists_measurable_superset_of_null (ae_iff.mp der)
  let A := Ioo a b \ N
  have inside : A ⊆ Icc a b := fun _ h => ⟨h.1.1.le,h.1.2.le⟩
  have good (t) (ht : t ∈ A) : HasDerivWithinAt G (d t) A t := by
    apply HasDerivAt.hasDerivWithinAt
    by_contra hn
    exact ht.2 (bad (fun hg => hn (hg ht.1)))
  have image := integral_image_eq_integral_deriv_smul_of_monotoneOn
    (measurableSet_Ioo.diff mN) good (mono.mono inside) (fun _ => (1:ℝ))
  have eq : A =ᵐ[volume] Ioc a b := by
    filter_upwards [compl_mem_ae_iff.mpr null,(Ioo_ae_eq_Ioc (μ := volume) (a := a) (b := b))] with t hN h
    change (t ∈ Ioo a b ∧ t ∉ N) = (t ∈ Ioc a b)
    exact propext ⟨fun h' => (eq_iff_iff.mp h).mp h'.1,fun h' => ⟨(eq_iff_iff.mp h).mpr h',hN⟩⟩
  have sub : G '' A ⊆ Icc (G a) (G b) := by
    rintro _ ⟨t,ht,rfl⟩
    exact ⟨mono ⟨le_rfl,ab⟩ (inside ht) (inside ht).1,mono (inside ht) ⟨ab,le_rfl⟩ (inside ht).2⟩
  have bound := measureReal_mono (μ := volume) sub (isCompact_Icc.measure_lt_top.ne)
  rw [Real.volume_real_Icc_of_le (mono ⟨le_rfl,ab⟩ ⟨ab,le_rfl⟩ ab)] at bound
  rw [intervalIntegral.integral_of_le ab,← setIntegral_congr_set eq]
  have area : (∫ t in A, d t) = volume.real (G '' A) := by simpa [A] using image.symm
  exact area.le.trans bound

/-- An integrable bound on *every* interval increment rules out a
singular part that the a.e. derivative alone cannot see. -/
theorem integral_eq_of_dominated_increments (z v g : ℝ → ℝ) {b : ℝ} (hb : 0 ≤ b)
    (iv : IntervalIntegrable v volume 0 b) (ig : IntervalIntegrable g volume 0 b)
    (dom : ∀ s ∈ Icc 0 b, ∀ t ∈ Icc 0 b, s ≤ t → |z t-z s| ≤ ∫ r in s..t, g r)
    (der : ∀ᵐ t ∂volume, t ∈ Ioo 0 b → HasDerivAt z (v t) t) :
    z b = z 0 + ∫ t in (0:ℝ)..b, v t := by
  let P := fun t => ∫ s in (0:ℝ)..t, g s
  have sub (s t : ℝ) (hs : s ∈ Icc 0 b) (ht : t ∈ Icc 0 b) (h : s ≤ t) :
      IntervalIntegrable g volume s t := ig.mono_set (by
    rw [uIcc_of_le h,uIcc_of_le hb]; exact Icc_subset_Icc hs.1 ht.2)
  have diff (s t : ℝ) (hs : s ∈ Icc 0 b) (ht : t ∈ Icc 0 b) (h : s ≤ t) :
      P s + (∫ r in s..t, g r) = P t :=
    intervalIntegral.integral_add_adjacent_intervals (sub 0 s ⟨le_rfl,hb⟩ hs hs.1) (sub s t hs ht h)
  have pd : ∀ᵐ t ∂volume, t ∈ Ioo 0 b → HasDerivAt P (g t) t := by
    filter_upwards [ig.ae_hasDerivAt_integral] with t h ht
    exact h (by rw [uIcc_of_le hb]; exact ⟨ht.1.le,ht.2.le⟩) 0 (by rw [uIcc_of_le hb]; exact ⟨le_rfl,hb⟩)
  have plus := monotone_increment hb (fun t => P t + z t) (fun t => g t + v t)
    (fun s hs t ht h => by linarith [(abs_le.mp (dom s hs t ht h)).1,diff s t hs ht h])
    (by filter_upwards [pd,der] with t a d ht using (a ht).add (d ht))
  have minus := monotone_increment hb (fun t => P t - z t) (fun t => g t - v t)
    (fun s hs t ht h => by linarith [(abs_le.mp (dom s hs t ht h)).2,diff s t hs ht h])
    (by filter_upwards [pd,der] with t a d ht using (a ht).sub (d ht))
  simp only [P,intervalIntegral.integral_same,zero_add,zero_sub,
    intervalIntegral.integral_add ig iv,intervalIntegral.integral_sub ig iv] at plus minus
  linarith

#print axioms integral_eq_of_dominated_increments
private theorem subintegrable {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (hf : IntervalIntegrable f volume 0 1) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    IntervalIntegrable f volume s t := hf.mono_set (by
  rw [uIcc_of_le hst,uIcc_of_le zero_le_one]; exact Icc_subset_Icc hs ht)

private theorem path_increment {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : ℝ → E) (ib : IntervalIntegrable b volume 0 1)
    (eq : ∀ t ∈ Icc (0:ℝ) 1, a t = a 0 + ∫ r in (0:ℝ)..t, b r)
    {s t : ℝ} (hs : s ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) (st : s ≤ t) :
    dist (a t) (a s) ≤ ∫ r in s..t, ‖b r‖ := by
  rw [dist_eq_norm,eq t ht,eq s hs,add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left (subintegrable ib le_rfl ht.1 ht.2)
      (subintegrable ib le_rfl hs.1 hs.2)]
  exact intervalIntegral.norm_integral_le_integral_norm st

private theorem primitive_derivative (a b : ℝ → State) (ib : IntervalIntegrable b volume 0 1)
    (eq : ∀ t ∈ Icc (0:ℝ) 1, a t = a 0 + ∫ r in (0:ℝ)..t, b r) :
    ∀ᵐ t ∂volume.restrict (Ioo (0:ℝ) 1), HasDerivAt a (b t) t := by
  let L (i : Fin 5) := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 5 => ℝ) i
  have integ (i) : IntervalIntegrable (fun r => L i (b r)) volume 0 1 :=
    ⟨(L i).integrable_comp ib.1,(L i).integrable_comp ib.2⟩
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [ae_all_iff.mpr (fun i => (integ i).ae_hasDerivAt_integral)] with t d ht
  apply hasDerivAt_pi.mpr
  intro i
  apply ((d i (by rw [uIcc_of_le zero_le_one]; exact ⟨ht.1.le,ht.2.le⟩) 0
    (by rw [uIcc_of_le zero_le_one]; exact ⟨le_rfl,zero_le_one⟩)).const_add (a 0 i)).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  change a s i = a 0 i + ∫ r in (0:ℝ)..s, L i (b r)
  rw [(L i).intervalIntegral_comp_comm (subintegrable ib le_rfl hs.1.le hs.2.le)]
  exact congrArg (fun z : State => z i) (eq s ⟨hs.1.le,hs.2.le⟩)

/-- The moving change of coordinates recovers an integral equation at
every time, including the terminal time. No time derivative of the input
or absolute continuity of the composed path is assumed. -/
theorem moving_integral_equation (K : Set State) [CompactSpace K]
    (S : State → C(Time,State)) (f : ℝ → C(K,State)) (hf : Integrable f volume)
    (frozen : ∀ x : K, ∀ s ∈ Icc (0:ℝ) 1,
      S x (clamp s) = S x (clamp 0) + ∫ r in (0:ℝ)..s, f r x)
    (L : ℝ≥0) (lip : LipschitzOnWith L S K) (ds : ∀ x ∈ K, DifferentiableAt ℝ S x)
    (a b : ℝ → State) (inside : MapsTo a (Icc 0 1) K) (ib : IntervalIntegrable b volume 0 1)
    (moving : ∀ t ∈ Icc (0:ℝ) 1, a t = a 0 + ∫ r in (0:ℝ)..t, b r)
    (v : ℝ → State) (iv : IntervalIntegrable v volume 0 1)
    (velocity : ∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo (0:ℝ) 1,
      fderiv ℝ S (a t) (b t) (clamp t) + f t ⟨a t,inside ⟨ht.1.le,ht.2.le⟩⟩ = v t) :
    ∀ t ∈ Icc (0:ℝ) 1, S (a t) (clamp t) = S (a 0) (clamp 0) + ∫ r in (0:ℝ)..t, v r := by
  let z (s : ℝ) := S (a s) (clamp s)
  let g (s : ℝ) := (L:ℝ) * ‖b s‖ + ‖f s‖
  have ig : IntervalIntegrable g volume 0 1 := (ib.norm.const_mul _).add hf.norm.intervalIntegrable
  have bound {s t : ℝ} (hs : s ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) (st : s ≤ t) :
      dist (z t) (z s) ≤ ∫ r in s..t, g r := by
    let x : K := ⟨a s,inside hs⟩
    let ev : C(K,State) →L[ℝ] State := ContinuousMap.evalCLM ℝ x
    have ie : Integrable (fun r => f r x) volume := ev.integrable_comp hf
    have one := path_increment (fun r => S x (clamp r)) (fun r => f r x) ie.intervalIntegrable (frozen x) hs ht st
    have two := (ContinuousMap.dist_apply_le_dist (f := S (a t)) (g := S (a s)) (clamp t)).trans
      (lip.dist_le_mul _ (inside ht) _ (inside hs))
    have vi := path_increment a b ib moving hs ht st
    have calcBound := dist_triangle (z t) (S (a s) (clamp t)) (z s)
    change dist (S (a s) (clamp t)) (z s) ≤ _ at one
    have mono := intervalIntegral.integral_mono_on st (subintegrable ie.intervalIntegrable.norm hs.1 st ht.2)
      (subintegrable hf.norm.intervalIntegrable hs.1 st ht.2) (fun r _ => (f r).norm_coe_le_norm x)
    rw [show (∫ r in s..t, g r) = (L:ℝ)*(∫ r in s..t, ‖b r‖) + ∫ r in s..t, ‖f r‖ by
      dsimp only [g]
      rw [intervalIntegral.integral_add ((subintegrable ib.norm hs.1 st ht.2).const_mul _) hf.norm.intervalIntegrable,
        intervalIntegral.integral_const_mul]]
    exact calcBound.trans (add_le_add (two.trans (mul_le_mul_of_nonneg_left vi L.coe_nonneg)) (one.trans mono))
  have d := moving_integral_family K S f hf frozen
  have da := primitive_derivative a b ib moving
  rw [ae_restrict_iff' measurableSet_Ioo] at d da
  intro t ht
  ext i
  let ev := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 5 => ℝ) i
  have vi := subintegrable iv le_rfl ht.1 ht.2
  have ci : IntervalIntegrable (fun s => ev (v s)) volume 0 t := ⟨ev.integrable_comp vi.1,ev.integrable_comp vi.2⟩
  have val := integral_eq_of_dominated_increments (fun s => z s i) (fun s => ev (v s)) g ht.1 ci
    (subintegrable ig le_rfl ht.1 ht.2) (fun s hs r hr sr => (dist_le_pi_dist (z r) (z s) i).trans
      (bound ⟨hs.1,hs.2.trans ht.2⟩ ⟨hr.1,hr.2.trans ht.2⟩ sr)) (by
    filter_upwards [d,da,velocity] with r chain path vel hr
    have h : r ∈ Ioo (0:ℝ) 1 := ⟨hr.1,hr.2.trans_le ht.2⟩
    have dz := chain h a (b r) (inside ⟨h.1.le,h.2.le⟩) (ds _ (inside ⟨h.1.le,h.2.le⟩)) (path h)
    rw [vel h] at dz
    exact ev.hasFDerivAt.comp_hasDerivAt r dz)
  rwa [ev.intervalIntegral_comp_comm vi] at val

#print axioms moving_integral_equation
private theorem two_channels {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Y : Fin 2 → C(Time,V)) (u : Control 2) :
    IntervalIntegrable (fun t => u t 0 • Y 0 (clamp t) + u t 1 • Y 1 (clamp t)) volume 0 1 := by
  obtain ⟨R,rep⟩ := control_signal_equiv
  let L (i : Fin 2) := ContinuousLinearMap.smulRightL ℝ (Fiber 2) V (ContinuousLinearMap.proj i)
  let A : C(Time,Fiber 2 →L[ℝ] V) := ⟨fun t => L 0 (Y 0 t) + L 1 (Y 1 t),
    ((L 0).continuous.comp (Y 0).continuous).add ((L 1).continuous.comp (Y 1).continuous)⟩
  have hi := Volterra.intervalIntegrable A (R u)
  simpa only [rep] using hi

variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M]

/-- On a common chart neighborhood of the reference flow, every genuine
solution of the pulled-back equation gives an original Segment for the
sum of the two L² controls. No a.e. chain rule or endpoint identity
is required from the caller. -/
theorem pulled_path_gives_segment (e : Frame M 2) (u v : Control 2)
    (K : Set State) [CompactSpace K] (S : State → C(Time,State))
    (L : ℝ≥0) (lip : LipschitzOnWith L S K) (ds : ∀ x ∈ K, DifferentiableAt ℝ S x)
    (chart : ∀ x ∈ K, ∀ t : Time, S x t ∈ e.chart.target)
    (init : ∀ x ∈ K, S x (clamp 0) = x)
    (flow : ∀ x ∈ K, ∀ t ∈ Icc (0:ℝ) 1,
      S x (clamp t) = x + ∫ r in (0:ℝ)..t, e.velocity (S x (clamp r)) (u r))
    (a : ℝ → State) (ca : ContinuousOn a (Icc 0 1)) (inside : MapsTo a (Icc 0 1) K)
    (inv : ∀ t ∈ Icc (0:ℝ) 1, ((ContinuousMap.evalCLM ℝ (clamp t)).comp (fderiv ℝ S (a t))).IsInvertible)
    (b : ℝ → State)
    (ib : IntervalIntegrable b volume 0 1)
    (ode : ∀ t ∈ Icc (0:ℝ) 1, a t = a 0 + ∫ r in (0:ℝ)..t, b r)
    (hb : ∀ t ∈ Icc (0:ℝ) 1, b t = ((ContinuousMap.evalCLM ℝ (clamp t)).comp (fderiv ℝ S (a t))).inverse
      (e.velocity (S (a t) (clamp t)) (v t))) :
    Segment e (u+v) (e.chart.symm (a 0)) (e.chart.symm (S (a 1) (clamp 1))) := by
  have sc : Continuous (fun x : K => S x) := continuousOn_iff_continuous_restrict.mp lip.continuousOn
  have joint : Continuous (fun p : Time × K => S p.2 p.1) :=
    continuous_eval.comp ((sc.comp continuous_snd).prodMk continuous_fst)
  have cj (i : Fin 2) : Continuous (fun p : Time × K => e.X i (S p.2 p.1)) :=
    (e.smooth i).continuousOn.comp_continuous joint (fun p => chart _ p.2.2 _)
  let Y (i : Fin 2) (t : Time) : C(K,State) := ⟨fun x => e.X i (S x t),
    (cj i).comp (continuous_const.prodMk continuous_id)⟩
  let fields (i : Fin 2) : C(Time,C(K,State)) := ⟨Y i,ContinuousMap.continuous_of_continuous_uncurry _ (cj i)⟩
  let raw (r : ℝ) := u r 0 • fields 0 (clamp r) + u r 1 • fields 1 (clamp r)
  let f := (Icc (0:ℝ) 1).indicator raw
  have hf : Integrable f volume := (integrable_indicator_iff measurableSet_Icc).mpr
    ((intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp (two_channels fields u))
  have fval (x : K) (r : ℝ) (hr : r ∈ Icc (0:ℝ) 1) : f r x = e.velocity (S x (clamp r)) (u r) := by
    rw [show f r = raw r from indicator_of_mem hr _]
    simp only [Frame.velocity,Fin.sum_univ_two]; rfl
  have ref (x : K) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      S x (clamp t) = S x (clamp 0) + ∫ r in (0:ℝ)..t, f r x := by
    rw [init _ x.2,flow _ x.2 t ht]
    congr 1
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le ht.1] at hr
    exact (fval x r ⟨hr.1,hr.2.trans ht.2⟩).symm
  let z (r : ℝ) := S (a r) (clamp r)
  have cz : ContinuousOn z (Icc 0 1) :=
    continuous_eval.comp_continuousOn ((lip.continuousOn.comp ca inside).prodMk
      (show Continuous clamp from continuous_projIcc).continuousOn)
  let w (t : ℝ) := e.velocity (z t) ((u+v) t)
  let F (i : Fin 2) : C(Time,State) := ⟨fun t => e.X i (z t),
    continuousOn_iff_continuous_restrict.mp ((e.smooth i).continuousOn.comp cz (fun r hr => chart _ (inside hr) _))⟩
  have iw : IntervalIntegrable w volume 0 1 := by
    apply (intervalIntegrable_congr (f := fun t => (u+v) t 0 • F 0 (clamp t) + (u+v) t 1 • F 1 (clamp t)) ?_).mp (two_channels F (u+v))
    intro r hr
    rw [uIoc_of_le zero_le_one] at hr
    change (u+v) r 0 • F 0 (clamp r) + (u+v) r 1 • F 1 (clamp r) = w r
    rw [show clamp r = ⟨r,hr.1.le,hr.2⟩ from projIcc_of_mem _ _]
    simp only [w,Frame.velocity,Fin.sum_univ_two]; rfl
  have velocity : ∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo (0:ℝ) 1,
      fderiv ℝ S (a t) (b t) (clamp t) + f t ⟨a t,inside ⟨ht.1.le,ht.2.le⟩⟩ = w t := by
    have add : ∀ᵐ t ∂volume.restrict (Icc (0:ℝ) 1), (u+v) t = u t + v t := Lp.coeFn_add u v
    rw [ae_restrict_iff' measurableSet_Icc] at add
    filter_upwards [add] with t sum ht
    have h : t ∈ Icc (0:ℝ) 1 := ⟨ht.1.le,ht.2.le⟩
    rw [fval _ t h,hb t h]
    let J := (ContinuousMap.evalCLM ℝ (clamp t)).comp (fderiv ℝ S (a t))
    change J (J.inverse (e.velocity (z t) (v t))) + e.velocity (z t) (u t) = e.velocity (z t) ((u+v) t)
    obtain ⟨A,hA⟩ := inv t h
    change A.toContinuousLinearMap = J at hA
    rw [← hA,ContinuousLinearMap.inverse_equiv]
    change A (A.symm _) + _ = _
    rw [A.apply_symm_apply,sum h]
    simp only [Frame.velocity,Fin.sum_univ_two,Pi.add_apply,add_smul]; abel
  have h0 : (0:ℝ) ∈ Icc 0 1 := ⟨le_rfl,zero_le_one⟩
  have h1 : (1:ℝ) ∈ Icc 0 1 := ⟨zero_le_one,le_rfl⟩
  have start := init _ (inside h0)
  have x0 : a 0 ∈ e.chart.target := start ▸ chart _ (inside h0) (clamp 0)
  have x1 : z 1 ∈ e.chart.target := chart _ (inside h1) _
  exact ⟨e.chart.map_target x0,e.chart.map_target x1,z,cz,fun t ht => chart _ (inside ht) _,
    start.trans (e.chart.right_inv x0).symm,(e.chart.right_inv x1).symm,iw,
    moving_integral_equation K S f hf ref L lip ds a b inside ib ode w iw velocity⟩

#print axioms pulled_path_gives_segment
/-- The compact neighborhood data used for the moving-frame calculation. -/
structure ReferenceTube (e : Frame M 2) (q : State) (r : ℝ) (u : Control 2) (P : State → C(Time,State)) : Prop where
  regular : ∀ x ∈ Metric.closedBall q r, ContDiffAt ℝ 3 P x
  lipschitz : ∃ L, LipschitzOnWith L P (Metric.closedBall q r)
  chart : ∀ x ∈ Metric.closedBall q r, ∀ t : Time, P x t ∈ e.chart.target
  initial : ∀ x ∈ Metric.closedBall q r, P x (clamp 0) = x
  flow : ∀ x ∈ Metric.closedBall q r, ∀ t ∈ Icc (0:ℝ) 1, P x (clamp t) = x +
    ∫ s in (0:ℝ)..t, e.velocity (P x (clamp s)) (u s)
  invertible : ∀ x ∈ Metric.closedBall q r, ∀ t : Time,
    ((ContinuousMap.evalCLM ℝ t).comp (fderiv ℝ P x)).IsInvertible

/-- A common compact ball and a single positive input threshold are
derived from the given smooth frame at any chart point. -/
theorem exists_reference_tube (e : Frame M 2) {q : State} (hq : q ∈ e.chart.target) :
    ∃ r > 0, ∀ u : Control 2, ‖u‖ < r → ∃ P, ReferenceTube e q r u P := by
  obtain ⟨S,cs,slice,run⟩ := small_chart_path_family e hq 3 (by decide)
  have c1 : ContDiffAt ℝ 1 S 0 := cs.of_le (by decide)
  have inv := nearby_state_jacobian_invertible S q c1 slice
  obtain ⟨L,N,near,lip⟩ := c1.exists_lipschitzOnWith
  obtain ⟨d,hd,ball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem near (inter_mem run (inter_mem inv (cs.eventually (by decide)))))
  refine ⟨d/2,half_pos hd,?_⟩
  intro u hu
  let I := fun x : State => (x-q,u)
  let P := S ∘ I
  have atX (x : State) (hx : x ∈ Metric.closedBall q (d/2)) : I x ∈ Metric.ball 0 d := by
    change max (dist (x-q) 0) (dist u 0) < d
    rw [dist_zero_right,dist_zero_right]
    exact max_lt ((show dist x q ≤ d/2 from hx).trans_lt (half_lt_self hd))
      (hu.trans (half_lt_self hd))
  have ci : ContDiff ℝ 3 I := (contDiff_id.sub contDiff_const).prodMk contDiff_const
  have di (x : State) : HasFDerivAt I (ContinuousLinearMap.inl ℝ State (Control 2)) x := by
    exact ((hasFDerivAt_id x).sub_const q).prodMk (hasFDerivAt_const u x)
  have lipI (x y : State) : dist (I x) (I y) = dist x y := by
    change max (dist (x-q) (y-q)) (dist u u) = _
    simp
  have regular (x : State) (hx : x ∈ Metric.closedBall q (d/2)) : ContDiffAt ℝ 3 S (I x) :=
    (ball (atX x hx)).2.2.2
  refine ⟨P,⟨fun x hx => (regular x hx).comp x ci.contDiffAt,⟨L,?_⟩,
    fun x hx => (ball (atX x hx)).2.1.1,?_,?_,?_⟩⟩
  · apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [P,Function.comp_apply,← lipI x y] using lip.dist_le_mul _ (ball (atX x hx)).1 _ (ball (atX y hy)).1
  · intro x hx
    have eq := (ball (atX x hx)).2.1.2 0 (by norm_num)
    simpa [P,I,add_sub_cancel] using eq
  · intro x hx t ht
    have eq := (ball (atX x hx)).2.1.2 t ht
    simpa [P,I,add_sub_cancel] using eq
  · intro x hx t
    have mem := ball (atX x hx)
    have dP := ((regular x hx).differentiableAt (by decide)).hasFDerivAt.comp x (di x)
    rw [show fderiv ℝ P x = _ from dP.fderiv]
    exact mem.2.2.1 t

#print axioms exists_reference_tube

/-- An arbitrary chart segment admits an exact positive-duration terminal
restriction whose reference flow starts in the inner ball and ends at the
original endpoint. The length of the full control is unrestricted. -/
theorem terminal_reference_tube (e : Frame M 2) (u : Control 2) {x y : M}
    (seg : Segment e u x y) :
    ∃ (d r : ℝ) (v : Control 2) (k : State) (P : State → C(Time, State)),
      0 < d ∧ d ≤ 1 ∧ 0 < r ∧ k ∈ Metric.ball (e.chart y) (r/2) ∧
      (∀ᵐ t ∂volume.restrict (Icc (0:ℝ) 1), v t = d • u ((1-d)+d*t)) ∧
      Segment e v (e.chart.symm k) y ∧ ReferenceTube e (e.chart y) r v P ∧
      P k (clamp 1) = e.chart y ∧ d < 1 ∧ ∃ pre : Control 2,
        (∀ᵐ t ∂volume.restrict (Icc (0:ℝ) 1), pre t = (1-d) • u ((1-d)*t)) ∧
        Segment e pre x (e.chart.symm k) := by
  obtain ⟨hx,hy,z,cz,mz,z0,z1,hi,ode⟩ := seg
  obtain ⟨r,hr,small⟩ := exists_reference_tube e (e.chart.map_source hy)
  have one : (1:ℝ) ∈ Icc 0 1 := ⟨zero_le_one,le_rfl⟩
  obtain ⟨η,hη,close⟩ := Metric.continuousWithinAt_iff.mp (cz 1 one) (r/2) (half_pos hr)
  let B := ‖u‖^2 + 1
  have posB : 0 < B := by dsimp [B]; positivity
  let m := min 1 (min η (r^2/B))
  have pm : 0 < m := lt_min zero_lt_one (lt_min hη (div_pos (sq_pos_of_pos hr) posB))
  let d := m/2
  have hd : 0 < d := half_pos pm
  have dm : d < m := half_lt_self pm
  have d1 : d ≤ 1 := dm.le.trans (min_le_left _ _)
  have dη : d < η := dm.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have dB : d*B < r^2 := (lt_div_iff₀ posB).mp
    (dm.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  have ha : 0 ≤ 1-d := sub_nonneg.mpr d1
  let k := z (1-d)
  have hk : k ∈ Metric.ball (e.chart y) (r/2) := by
    rw [Metric.mem_ball,← z1]
    apply close ⟨ha,by linarith⟩
    simpa [Real.dist_eq,abs_of_nonneg hd.le] using dη
  obtain ⟨v,rep,bound,sv⟩ := subsegment e u z cz mz hi ode ha hd (by linarith)
  have hv : ‖v‖ < r := by dsimp [B] at dB; nlinarith
  obtain ⟨P,tube⟩ := small v hv
  have sv' : Segment e v (e.chart.symm k) y := by
    simpa only [sub_add_cancel,z1,e.chart.left_inv hy,k] using sv
  have kc : k ∈ Metric.closedBall (e.chart y) r :=
    hk.le.trans (half_le_self hr.le)
  have start := tube.initial k kc
  have kt : k ∈ e.chart.target := start ▸ tube.chart k kc (clamp 0)
  have endt := tube.chart k kc (clamp 1)
  let W (i : Fin 2) : C(Time, State) := ⟨fun t => e.X i (P k t),
    (e.smooth i).continuousOn.comp_continuous (P k).continuous (tube.chart k kc)⟩
  have iw := two_channels W v
  have other : Segment e v (e.chart.symm k) (e.chart.symm (P k (clamp 1))) := by
    refine ⟨e.chart.map_target kt,e.chart.map_target endt,fun t => P k (clamp t),
      ((P k).continuous.comp (show Continuous clamp from continuous_projIcc)).continuousOn,
      fun t _ => tube.chart k kc _,start.trans (e.chart.right_inv kt).symm,
      (e.chart.right_inv endt).symm,?_,?_⟩
    · simpa only [Frame.velocity,Fin.sum_univ_two] using iw
    · intro t ht
      simpa only [start] using (tube.flow k kc t ht)
  obtain ⟨F,_,graph⟩ := arbitrary_segment_graph e v _ y sv' 1 (by decide)
  rw [e.chart.right_inv kt] at graph
  have same := ((graph.self_of_nhds.2.2 _).mp other).trans
    ((graph.self_of_nhds.2.2 _).mp sv').symm
  have strict : d < 1 := dm.trans_le (min_le_left _ _)
  obtain ⟨pre,pRep,_,pSeg⟩ := subsegment e u z cz mz hi ode (a := 0) le_rfl
    (sub_pos.mpr strict) (by linarith)
  exact ⟨d,r,v,k,P,hd,d1,hr,hk,rep,sv',tube,
    (e.chart.right_inv endt).symm.trans (congrArg e.chart same),strict,pre,
    by simpa only [zero_add] using pRep,by simpa only [zero_add,z0,e.chart.left_inv hx,k] using pSeg⟩

#print axioms terminal_reference_tube
end MinimizingSard.Five
