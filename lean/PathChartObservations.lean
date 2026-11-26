import SobolevTimeCoordinates
import GlobalCurveSard

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
open Volterra
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] {m n : ℕ}

theorem TimePartition.atTime_continuous (P : TimePartition n) (i : Fin n) : Continuous (P.atTime i) :=
  (continuous_const.add (continuous_const.mul continuous_subtype_val)).subtype_mk _

theorem TimePartition.interval_cover (P : TimePartition (n+1)) (t : Time) :
    ∃ i, (t:ℝ) ∈ Icc (P.left i) (P.cut i.succ) := by
  by_cases z : (t:ℝ) = 0
  · exact ⟨0,by rw [z]; exact ⟨P.first.le,(P.cut_mem (0:Fin (n+1)).succ).1⟩⟩
  · obtain ⟨i,h⟩ := mem_iUnion.mp (P.covers ⟨lt_of_le_of_ne t.2.1 (Ne.symm z),t.2.2⟩)
    exact ⟨i,h.1.le,h.2⟩

theorem HorizontalVariation.maps_into {Γ : Geometry M m} {x : M} {F : ℝ → C(Time,M)} (family : HorizontalVariation Γ x F)
    (K : Set Time) (hk : IsCompact K) (U : Set M) (ho : IsOpen U) (h0 : MapsTo (F 0) K U) :
    ∀ᶠ r in 𝓝 0, MapsTo (F r) K U := by
  obtain ⟨n,P,e,Z,he,dz,near⟩ := family
  let B (i : Fin (n+1)) := P.atTime i ⁻¹' K
  let O (i : Fin (n+1)) := (e i).chart.target ∩ (e i).chart.symm ⁻¹' U
  have base (i) : MapsTo (ambientPath (Z 0 i)) (B i) (O i) := by
    obtain ⟨_,_,_,edge⟩ := near.self_of_nhds.2.1
    intro s hs
    have ref := near.self_of_nhds.2.2 i _ (P.atTime_mem i s)
    rw [P.clock_atTime] at ref
    exact ⟨(edge i).2.2.2.2.1 _,by change (e i).chart.symm _ ∈ U; rw [← ref]; exact h0 hs⟩
  have each (i) : ∀ᶠ r in 𝓝 0, MapsTo (ambientPath (Z r i)) (B i) (O i) := by
    let pr := (ContinuousLinearMap.proj i : (Fin (n+1) → SobolevData) →L[ℝ] SobolevData)
    have c := (ambientPath.continuous.comp pr.continuous).continuousAt.comp dz.continuousAt
    exact c.tendsto ((ContinuousMap.isOpen_setOf_mapsTo
      ((hk.isClosed.preimage (P.atTime_continuous i)).isCompact)
      ((e i).chart.continuousOn_symm.isOpen_inter_preimage (e i).chart.open_target ho)).mem_nhds (base i))
  filter_upwards [near,Filter.eventually_all.mpr each] with r hr ok
  intro t ht
  obtain ⟨i,hi⟩ := P.interval_cover t
  rw [hr.2.2 i t hi]
  exact (ok i (show P.localClock i t ∈ B i by change P.atTime i (P.localClock i t) ∈ K; rwa [P.atTime_clock i t hi])).2

variable [T2Space M]

/-- On a compact nonempty portion of a chart, the coordinates extend to
a globally defined observation which is smooth in every compatible chart. -/
theorem extend_chart_observation (c : OpenPartialHomeomorph M State) (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M)
    (K : Set M) (hk : IsCompact K) (ne : K.Nonempty) (sub : K ⊆ c.source) :
    ∃ (H : M → State) (V : Set M),
      (∀ b : OpenPartialHomeomorph M State, b ∈ maximalAtlas 𝓘(ℝ,State) ∞ M →
        ContDiffOn ℝ ∞ (H ∘ b.symm) b.target) ∧
      IsOpen V ∧ K ⊆ V ∧ V ⊆ c.source ∧ EqOn H c V := by
  classical
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace State M
  obtain ⟨W,ow,kw,ws⟩ := hk.exists_isOpen_closure_subset (c.open_source.mem_nhdsSet.mpr sub)
  have wc := subset_closure.trans ws
  have op : IsOpen (c '' W) := c.isOpen_image_of_subset_source ow wc
  obtain ⟨b,sup,sm,vals⟩ := op.exists_smooth_support_eq
  have compact := hk.image_of_continuousOn (c.continuousOn.mono sub)
  obtain ⟨z,hz,small⟩ := compact.exists_isMinOn (ne.image c) sm.continuous.continuousOn
  have pos : 0 < b z := lt_of_le_of_ne (vals (mem_range_self z)).1 (Ne.symm (by
    apply (show z ∈ Function.support b from sup.symm ▸ image_mono kw hz)))
  let a := (3:ℝ)/b z
  have pa : 0 < a := div_pos (by norm_num) pos
  have val : a*b z = 3 := by dsimp [a]; field_simp
  let Y (v : State) := Real.smoothTransition (a*b v-1) • v
  have sy : ContDiff ℝ ∞ Y := (Real.smoothTransition.contDiff.comp ((contDiff_const.mul sm).sub contDiff_const)).smul contDiff_id
  let H (y : M) := if y ∈ c.source then Y (c y) else 0
  have zero (y : M) (hy : y ∉ W) : H y = 0 := by
    by_cases inC : y ∈ c.source
    · have bz : b (c y) = 0 := Function.notMem_support.mp (fun h => by
        obtain ⟨q,hq,eq⟩ := sup ▸ h
        exact hy ((c.injOn (wc hq) inC eq) ▸ hq))
      simp [H,inC,Y,bz,Real.smoothTransition.zero_of_nonpos]
    · simp [H,inC]
  let V := c.source ∩ c ⁻¹' {v | 2 < a*b v}
  have ov : IsOpen V := c.continuousOn.isOpen_inter_preimage c.open_source (isOpen_lt continuous_const (continuous_const.mul sm.continuous))
  refine ⟨H,V,?_,ov,fun y hy => ⟨sub hy,?_⟩,inter_subset_left,?_⟩
  · intro d hd v hv
    let y := d.symm v
    have ds : y ∈ d.source := d.map_target hv
    by_cases hit : y ∈ c.source
    · have reg := (compatible_of_mem_maximalAtlas hd hc).1
      change ContDiffOn ℝ ∞ (c ∘ d.symm) ((d.symm.trans c).source ∩ range (𝓘(ℝ,State))) at reg
      have reg' : ContDiffOn ℝ ∞ (c ∘ d.symm) (d.symm.trans c).source := by simpa using reg
      have localT := (reg' v ⟨hv,hit⟩).contDiffAt ((d.symm.trans c).open_source.mem_nhds ⟨hv,hit⟩)
      apply ((sy.contDiffAt.comp v localT).congr_of_eventuallyEq ?_).contDiffWithinAt
      filter_upwards [(d.continuousAt_symm hv) (c.open_source.mem_nhds hit)] with q hq
      change d.symm q ∈ c.source at hq
      simp [H,Function.comp_apply,hq]
    · have out : y ∈ (closure W)ᶜ := fun h => hit (ws h)
      apply ((contDiffAt_const (c := (0:State))).congr_of_eventuallyEq ?_).contDiffWithinAt
      filter_upwards [(d.continuousAt_symm hv) (isClosed_closure.isOpen_compl.mem_nhds out)] with q hq
      exact zero _ (fun h => hq (subset_closure h))
  · change 2 < a*b (c y)
    linarith only [val,mul_le_mul_of_nonneg_left (small (mem_image_of_mem c hy)) pa.le]
  · intro y hy
    have large : 1 ≤ a*b (c y)-1 := by linarith [show 2 < a*b (c y) from hy.2]
    simp [H,hy.1,Y,Real.smoothTransition.one_of_one_le large]

#print axioms HorizontalVariation.maps_into
#print axioms extend_chart_observation
end MinimizingSard.Five
