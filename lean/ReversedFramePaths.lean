import PointedLengthValue
import Mathlib.Data.Fin.Rev
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

noncomputable section
open Set Filter MeasureTheory
namespace MinimizingSard.Five

private abbrev flipTime (s : ℝ) := 1 - s

private theorem flip_preserves : MeasurePreserving flipTime
    (volume.restrict (Icc (0:ℝ) 1)) (volume.restrict (Icc (0:ℝ) 1)) := by
  have same : flipTime ⁻¹' Icc 0 1 = Icc 0 1 := by
    ext s
    change (0 ≤ 1-s ∧ 1-s ≤ 1) ↔ (0 ≤ s ∧ s ≤ 1)
    constructor <;> rintro ⟨h,k⟩ <;> constructor <;> linarith
  have h := (volume.measurePreserving_sub_left (1:ℝ)).restrict_preimage (measurableSet_Icc (a := (0:ℝ)) (b := 1))
  change MeasurePreserving flipTime (volume.restrict (flipTime ⁻¹' Icc 0 1)) _ at h
  rwa [same] at h

def reverseControl {m : ℕ} (u : Control m) : Control m :=
  -(Lp.compMeasurePreserving flipTime flip_preserves u)

private theorem reverse_repr {m : ℕ} (u : Control m) :
    ∀ᵐ s ∂volume.restrict (Icc (0:ℝ) 1), reverseControl u s = -u (1-s) := by
  filter_upwards [Lp.coeFn_neg (Lp.compMeasurePreserving flipTime flip_preserves u),
    Lp.coeFn_compMeasurePreserving u flip_preserves] with s hn hf
  exact hn.trans (congrArg Neg.neg hf)

theorem reverseControl_const {m : ℕ} (v : Fiber m) :
    reverseControl (Lp.const 2 (volume.restrict (Icc (0:ℝ) 1)) v) =
      Lp.const 2 (volume.restrict (Icc (0:ℝ) 1)) (-v) := by
  let μ := volume.restrict (Icc (0:ℝ) 1)
  apply Lp.ext
  filter_upwards [reverse_repr (Lp.const 2 μ v),flip_preserves.quasiMeasurePreserving.ae (Lp.coeFn_const 2 μ v),
    Lp.coeFn_const 2 μ (-v)] with s h hr hc
  exact h.trans ((congrArg Neg.neg hr).trans hc.symm)

private theorem on_subinterval {P : ℝ → Prop} (h : ∀ᵐ s ∂volume.restrict (Icc (0:ℝ) 1), P s)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : ∀ᵐ s ∂volume.restrict (uIoc (0:ℝ) t), P s := by
  rw [uIoc_of_le ht.1]
  exact ae_mono (Measure.restrict_mono (fun s hs => ⟨hs.1.le,hs.2.trans ht.2⟩ : Ioc (0:ℝ) t ⊆ Icc 0 1) le_rfl) h

theorem segment_reverse {M : Type*} [TopologicalSpace M] [ChartedSpace State M] {m : ℕ}
    {e : Frame M m} {u : Control m} {x y : M} (h : Segment e u x y) : Segment e (reverseControl u) y x := by
  obtain ⟨hx,hy,z,cz,mz,z0,z1,integ,ode⟩ := h
  let f (s : ℝ) := e.velocity (z s) (u s)
  have maps : MapsTo flipTime (Icc (0:ℝ) 1) (Icc 0 1) := by
    intro s hs
    obtain ⟨hs,h1⟩ := hs
    exact ⟨sub_nonneg.mpr h1,sub_le_self _ hs⟩
  have repr : ∀ᵐ s ∂volume.restrict (Icc (0:ℝ) 1),
      e.velocity (z (1-s)) (reverseControl u s) = -f (1-s) := by
    filter_upwards [reverse_repr u] with s hs
    simp [hs,f,Frame.velocity,Finset.sum_neg_distrib]
  have ri : IntervalIntegrable (fun s => -f (1-s)) volume 0 1 := by
    exact (show IntervalIntegrable (fun s => f (1-s)) volume 0 1 by simpa [f] using (integ.comp_sub_left 1).symm).neg
  refine ⟨hy,hx,z ∘ flipTime,cz.comp (by unfold flipTime; fun_prop) maps,mz.comp maps,
    by simpa [flipTime] using z1, by simpa [flipTime] using z0,
    (intervalIntegrable_congr_ae (on_subinterval repr (t := 1) (by norm_num))).mpr ri,?_⟩
  intro t ht
  change z (1-t) = z (1-0) + ∫ s in (0:ℝ)..t, e.velocity (z (1-s)) (reverseControl u s)
  rw [intervalIntegral.integral_congr_ae_restrict (on_subinterval repr ht),
    intervalIntegral.integral_neg,intervalIntegral.integral_comp_sub_left,sub_zero]
  have ht' := maps ht
  have i0 : IntervalIntegrable f volume 0 (1-t) :=
    integ.mono_set (by rw [uIcc_of_le ht'.1,uIcc_of_le zero_le_one]; exact Icc_subset_Icc le_rfl ht'.2)
  have i1 : IntervalIntegrable f volume (1-t) 1 :=
    integ.mono_set (by rw [uIcc_of_le ht'.2,uIcc_of_le zero_le_one]; exact Icc_subset_Icc ht'.1 le_rfl)
  rw [ode _ ht',ode 1 (by norm_num)]
  change _ = (z 0 + ∫ s in (0:ℝ)..1, f s) + _
  rw [← intervalIntegral.integral_add_adjacent_intervals i0 i1]
  abel

private theorem reverse_integral {m : ℕ} (u : Control m) :
    (∫ s in (0:ℝ)..1, Real.sqrt (speedSq (reverseControl u s))) = ∫ s in (0:ℝ)..1, Real.sqrt (speedSq (u s)) := by
  have same : ∀ᵐ s ∂volume.restrict (Icc (0:ℝ) 1), Real.sqrt (speedSq (reverseControl u s)) =
      (fun t => Real.sqrt (speedSq (u t))) (1-s) := by
    filter_upwards [reverse_repr u] with s hs
    simp [hs,speedSq]
  rw [intervalIntegral.integral_congr_ae_restrict (on_subinterval same (t := 1) (by norm_num)),
    intervalIntegral.integral_comp_sub_left (fun t => Real.sqrt (speedSq (u t))) 1]
  simp

/-- Reversal preserves the full set of lengths attained by arbitrary original finite-frame paths. -/
theorem attainableLengths_reverse {M : Type*} [TopologicalSpace M] [ChartedSpace State M] {m : ℕ}
    (Γ : Geometry M m) (x y : M) : attainableLengths Γ x y = attainableLengths Γ y x := by
  suffices inc : ∀ a b, attainableLengths Γ a b ⊆ attainableLengths Γ b a from Set.Subset.antisymm (inc x y) (inc y x)
  intro a b l hl
  obtain ⟨k,e,u,he,⟨nodes,src,dst,segs⟩,rfl⟩ := hl
  refine ⟨k,fun i => e i.rev,fun i => reverseControl (u i.rev),fun i => he i.rev,
    ⟨fun i => nodes i.rev,by simpa using dst,by simpa using src,?_⟩,?_⟩
  · intro i
    simpa only [Fin.rev_castSucc,Fin.rev_succ] using segment_reverse (segs i.rev)
  · unfold length
    simp only [reverse_integral]
    exact Equiv.sum_comp Fin.revPerm (fun i => ∫ s in (0:ℝ)..1, Real.sqrt (speedSq (u i s)))

#print axioms segment_reverse
#print axioms reverseControl_const
#print axioms attainableLengths_reverse
end MinimizingSard.Five
