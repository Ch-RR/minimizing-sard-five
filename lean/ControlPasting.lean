import ControlSubdivision

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace MinimizingSard.Five

private abbrev unitMeasure := volume.restrict (Icc (0:ℝ) 1)

private theorem restriction_iff {m : ℕ} {a d : ℝ} (hd : 0 < d)
    (R : Control m →L[ℝ] Control m)
    (rep : ∀ u : Control m, ∀ᵐ s ∂unitMeasure, R u s = d • u (a+d*s))
    (u v : Control m) : R u = v ↔
    ∀ᵐ t ∂volume.restrict (Ioc a (a+d)), u t = d⁻¹ • v ((t-a)/d) := by
  let f (s : ℝ) := a+d*s
  let g (t : ℝ) := (t-a)/d
  have back : Measure.QuasiMeasurePreserving g (volume : Measure ℝ) volume := by
    simpa only [g,div_eq_inv_mul,sub_eq_add_neg,add_comm,Function.comp_def,smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) (inv_ne_zero hd.ne')).comp
        (measurePreserving_add_left volume (-a)).quasiMeasurePreserving
  have inverseMap := back.restrict (s := Ioc a (a+d)) (t := Icc 0 1) (by
    intro t ht
    exact ⟨div_nonneg (sub_nonneg.mpr ht.1.le) hd.le,(div_le_one hd).mpr (by linarith [ht.2])⟩)
  have forth : Measure.QuasiMeasurePreserving f (volume : Measure ℝ) volume :=
    (measurePreserving_add_left volume a).quasiMeasurePreserving.comp (Measure.quasiMeasurePreserving_smul volume hd.ne')
  have forwardMap := forth.restrict (s := Ioc 0 1) (t := Ioc a (a+d)) (by
    intro s hs; exact ⟨lt_add_of_pos_right a (mul_pos hd hs.1),
      add_le_add_left (mul_le_of_le_one_right hd.le hs.2) _⟩)
  constructor
  · rintro rfl
    filter_upwards [inverseMap.ae (rep u)] with t ht
    change (R u) ((t-a)/d) = d • u (a+d*((t-a)/d)) at ht
    rw [ht,show a+d*((t-a)/d) = t by field_simp; ring,inv_smul_smul₀ hd.ne']
  · intro h
    apply Lp.ext
    have hf := forwardMap.ae h
    rw [Measure.restrict_congr_set Ioc_ae_eq_Icc] at hf
    filter_upwards [rep u,hf] with s hs ht
    change u (a+d*s) = d⁻¹ • v (((a+d*s)-a)/d) at ht
    rw [hs,ht,show ((a+d*s)-a)/d = s by field_simp; ring,smul_inv_smul₀ hd.ne']

private theorem inverse_piece_memLp {m : ℕ} (v : Control m) (a d : ℝ) :
    MemLp ((Ioc a (a+d)).indicator (fun t : ℝ => d⁻¹ • v ((t-a)/d))) 2 (volume : Measure ℝ) := by
  rw [memLp_indicator_iff_restrict measurableSet_Ioc]
  have hi : IntervalIntegrable (fun s : ℝ => ‖v s‖^2) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr ((Lp.memLp v).integrable_norm_pow (p := 2) (by norm_num))
  have dil : IntervalIntegrable (fun s : ℝ => ‖v (s/d)‖^2) volume 0 d := by
    simpa [div_eq_mul_inv,mul_comm] using hi.comp_mul_left (c := d⁻¹)
  have shift : IntervalIntegrable (fun t : ℝ => ‖v ((t-a)/d)‖^2) volume a (a+d) := by
    simpa [add_comm] using dil.comp_sub_right a
  have meas : StronglyMeasurable (fun t : ℝ => d⁻¹ • v ((t-a)/d)) :=
    ((Lp.stronglyMeasurable v).comp_measurable (g := fun t : ℝ => (t-a)/d) (by fun_prop)).const_smul (d⁻¹)
  apply (memLp_two_iff_integrable_sq_norm meas.aestronglyMeasurable).mpr
  simpa only [norm_smul,mul_pow] using (shift.const_mul (‖d⁻¹‖^2)).1

/-- Any finite partition of the unit interval into positive time blocks gives
a bounded linear equivalence on all L² controls, with the prescribed rescaling. -/
theorem partition_control_equiv (m n : ℕ) (a d : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hd : ∀ i, 0 < d i) (he : ∀ i, a i+d i ≤ 1)
    (disj : Pairwise (fun i j => Disjoint (Ioc (a i) (a i+d i)) (Ioc (a j) (a j+d j))))
    (cover : Ioc (0:ℝ) 1 ⊆ ⋃ i, Ioc (a i) (a i+d i)) :
    ∃ R : Control m ≃L[ℝ] (Fin n → Control m), ∀ u i,
      ∀ᵐ s ∂unitMeasure, R u i s = d i • u (a i+d i*s) := by
  classical
  choose r hr using fun i => restriction_operator m (ha i) (hd i) (he i)
  let R := ContinuousLinearMap.pi r
  let B (i : Fin n) := Ioc (a i) (a i+d i)
  have block (i : Fin n) (u v : Control m) := restriction_iff (a := a i) (hd i) (r i)
    (fun z => (hr i z).1) u v
  have inj : Function.Injective R := by
    intro u v eq
    apply Lp.ext
    have each (i : Fin n) : ∀ᵐ t ∂volume, t ∈ B i → u t = v t := by
      apply (ae_restrict_iff' measurableSet_Ioc).mp
      have same : r i u = r i v := congrFun eq i
      filter_upwards [(block i u (r i v)).mp same,(block i v (r i v)).mp rfl] with t hu hv
      exact hu.trans hv.symm
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    filter_upwards [ae_all_iff.mpr each,(Ioc_ae_eq_Icc (μ := (volume : Measure ℝ)) (a := 0) (b := 1))] with t ht edge
    intro hc
    have h : t ∈ Ioc (0:ℝ) 1 := (show (t ∈ Ioc (0:ℝ) 1) = (t ∈ Icc 0 1) from edge).mpr hc
    obtain ⟨i,hi⟩ := mem_iUnion.mp (cover h)
    exact ht i hi
  have sur : Function.Surjective R := by
    intro v
    let g (i : Fin n) := (B i).indicator (fun t : ℝ => (d i)⁻¹ • v i ((t-a i)/d i))
    let f (t : ℝ) := ∑ i, g i t
    have allMem : MemLp f 2 volume :=
      memLp_finset_sum Finset.univ (fun i _ => inverse_piece_memLp (v i) (a i) (d i))
    have mem := allMem.mono_measure (Measure.restrict_le_self (s := Icc (0:ℝ) 1))
    let u := mem.toLp f
    refine ⟨u,funext (fun i => (block i u (v i)).mpr ?_)⟩
    have subset : B i ⊆ Icc 0 1 := fun t ht => ⟨(ha i).trans ht.1.le,ht.2.trans (he i)⟩
    filter_upwards [ae_mono (Measure.restrict_mono subset le_rfl) mem.coeFn_toLp,
      ae_restrict_mem (measurableSet_Ioc (a := a i) (b := a i+d i))] with t hu ht
    change u t = f t at hu
    rw [hu]
    change (∑ j, g j t) = _
    rw [Finset.sum_eq_single i]
    · exact indicator_of_mem ht _
    · intro j _ hji
      exact indicator_of_notMem (fun hj => Set.disjoint_left.mp (disj hji) hj ht) _
    · simp
  exact ⟨ContinuousLinearEquiv.ofBijective R (LinearMap.ker_eq_bot.mpr inj) (LinearMap.range_eq_top.mpr sur),
    fun u i => (hr i u).1⟩

#print axioms partition_control_equiv

structure TimePartition (n : ℕ) where
  cut : Fin (n+1) → ℝ
  first : cut 0 = 0
  last : cut (Fin.last n) = 1
  increasing : StrictMono cut

namespace TimePartition
variable {n : ℕ} (P : TimePartition n)

def left (i : Fin n) := P.cut i.castSucc
def duration (i : Fin n) := P.cut i.succ - P.left i
def block (i : Fin n) := Ioc (P.left i) (P.cut i.succ)

theorem cut_mem (j : Fin (n+1)) : P.cut j ∈ Icc (0:ℝ) 1 := by
  constructor
  · rw [← P.first]; exact P.increasing.monotone (Fin.zero_le _)
  · rw [← P.last]; exact P.increasing.monotone (Fin.le_last _)

theorem duration_pos (i : Fin n) : 0 < P.duration i :=
  sub_pos.mpr (P.increasing (Fin.castSucc_lt_succ i))

@[simp] theorem end_eq (i : Fin n) : P.left i + P.duration i = P.cut i.succ := by
  dsimp [duration]; abel

theorem blocks_disjoint : Pairwise (fun i j => Disjoint (P.block i) (P.block j)) := by
  intro i j h
  have ordered {i j : Fin n} (lt : i < j) : Disjoint (P.block i) (P.block j) := by
    apply Set.disjoint_left.mpr
    intro t hi hj
    have le : i.succ ≤ j.castSucc := by change i.val+1 ≤ j.val; exact lt
    exact (not_lt_of_ge (hi.2.trans (P.increasing.monotone le))) hj.1
  rcases lt_or_gt_of_ne h with h | h
  · exact ordered h
  · exact (ordered h).symm

theorem covers : Ioc (0:ℝ) 1 ⊆ ⋃ i, P.block i := by
  intro t ht
  have aux (j : Fin (n+1)) : t ≤ P.cut j → ∃ i, t ∈ P.block i := by
    induction j using Fin.induction with
    | zero => intro h; rw [P.first] at h; exact False.elim (not_lt_of_ge h ht.1)
    | succ i ih =>
      intro h
      by_cases le : t ≤ P.cut i.castSucc
      · exact ih le
      · exact ⟨i,lt_of_not_ge le,h⟩
  exact mem_iUnion.mpr (aux _ (P.last ▸ ht.2))

theorem coordinates (m : ℕ) : ∃ R : Control m ≃L[ℝ] (Fin n → Control m),
    (∀ u i, ∀ᵐ s ∂unitMeasure, R u i s = P.duration i • u (P.left i+P.duration i*s)) ∧
    ∀ u i, ∀ᵐ t ∂volume.restrict (P.block i),
      u t = (P.duration i)⁻¹ • R u i ((t-P.left i)/P.duration i) := by
  obtain ⟨R,rep⟩ := partition_control_equiv m n P.left P.duration
    (fun i => (P.cut_mem i.castSucc).1) P.duration_pos (fun i => P.end_eq i ▸ (P.cut_mem i.succ).2)
    (by simpa only [end_eq,block] using P.blocks_disjoint)
    (by simpa only [end_eq,block] using P.covers)
  refine ⟨R,rep,?_⟩
  intro u i
  let L := (ContinuousLinearMap.proj i).comp R.toContinuousLinearMap
  have eq := (restriction_iff (a := P.left i) (P.duration_pos i) L (fun z => rep z i) u (R u i)).mp rfl
  simpa only [end_eq,block] using eq

#print axioms coordinates
end TimePartition
end MinimizingSard.Five
