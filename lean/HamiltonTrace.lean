import CotangentCharts
import Mathlib.Analysis.ODE.Gronwall

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five

variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] {m : ℕ}

/-- A fixed-time Hamiltonian trajectory written in all local frame coordinates.
Only right derivatives are needed, so finite concatenations include their joints. -/
structure HamiltonTrace (Γ : Geometry M m) (L : ℝ) (f : ℝ → CotPoint M) : Prop where
  base : ContinuousOn (fun t => (f t).1) (Icc 0 L)
  coord : ∀ e ∈ Γ.frames, ∀ t ∈ Icc 0 L, (f t).1 ∈ e.chart.source →
    ContinuousWithinAt (phaseView e.chart ∘ f) (Icc 0 L) t
  ode : ∀ e ∈ Γ.frames, ∀ t ∈ Ico 0 L, (f t).1 ∈ e.chart.source →
    HasDerivWithinAt (phaseView e.chart ∘ f) (hamiltonianField e.X (phaseView e.chart (f t))) (Ici t) t

variable [IsManifold 𝓘(ℝ,State) ∞ M]

theorem HamiltonTrace.equal_right (Γ : Geometry M m) {L : ℝ} {f g : ℝ → CotPoint M}
    (hf : HamiltonTrace Γ L f) (hg : HamiltonTrace Γ L g) (t : ℝ) (ht : t ∈ Ico 0 L)
    (equal : f t = g t) : f =ᶠ[𝓝[≥] t] g := by
  have ti : t ∈ Icc 0 L := Ico_subset_Icc_self ht
  obtain ⟨e,he,ex⟩ := Γ.cover (f t).1
  have ey : (g t).1 ∈ e.chart.source := equal ▸ ex
  let F := phaseView e.chart ∘ f
  let G := phaseView e.chart ∘ g
  have fg : F t = G t := congrArg (phaseView e.chart) equal
  have c1 : ContDiffAt ℝ 1 (hamiltonianField e.X) (F t) :=
    (hamiltonianField_smoothAt e _ (e.chart.map_source ex)).of_le (by decide)
  obtain ⟨K,N,near,lip⟩ := c1.exists_lipschitzOnWith
  have filt := nhdsWithin_le_of_mem (Icc_mem_nhdsGE_of_mem ht)
  have fN : ∀ᶠ s in 𝓝[≥] t, F s ∈ N := ((hf.coord e he t ti ex).tendsto.mono_left filt) near
  have gN : ∀ᶠ s in 𝓝[≥] t, G s ∈ N := ((hg.coord e he t ti ey).tendsto.mono_left filt) (show N ∈ 𝓝 (G t) by rwa [← fg])
  have fE : ∀ᶠ s in 𝓝[≥] t, (f s).1 ∈ e.chart.source := ((hf.base t ti).tendsto.mono_left filt) (e.chart.open_source.mem_nhds ex)
  have gE : ∀ᶠ s in 𝓝[≥] t, (g s).1 ∈ e.chart.source := ((hg.base t ti).tendsto.mono_left filt) (e.chart.open_source.mem_nhds ey)
  let A := {s : ℝ | F s ∈ N ∧ G s ∈ N ∧ (f s).1 ∈ e.chart.source ∧ (g s).1 ∈ e.chart.source}
  have nb : A ∈ 𝓝[≥] t := fN.and (gN.and (fE.and gE))
  obtain ⟨r,hr,mem⟩ := (mem_nhdsGE_iff_exists_mem_Ioc_Ico_subset ht.2).mp nb
  filter_upwards [Ico_mem_nhdsGE hr.1] with b hb
  have subset : Icc t b ⊆ Ico t r := Icc_subset_Ico_right hb.2
  have all (s) (hs : s ∈ Icc t b) : s ∈ Ico 0 L := ⟨ht.1.trans hs.1,(hs.2.trans_lt hb.2).trans_le hr.2⟩
  have interval : Icc t b ⊆ Icc 0 L := fun s h => Ico_subset_Icc_self (all s h)
  have solve := ODE_solution_unique_of_mem_Icc_right (v := fun _ => hamiltonianField e.X) (s := fun _ => N)
    (a := t) (b := b) (f := F) (g := G) (fun _ _ => lip)
    (fun s h => (hf.coord e he s (interval h) (mem (subset h)).2.2.1).mono interval)
    (fun s h => hf.ode e he s (all s (Ico_subset_Icc_self h)) (mem (subset (Ico_subset_Icc_self h))).2.2.1)
    (fun _ h => (mem (subset (Ico_subset_Icc_self h))).1)
    (fun s h => (hg.coord e he s (interval h) (mem (subset h)).2.2.2).mono interval)
    (fun s h => hg.ode e he s (all s (Ico_subset_Icc_self h)) (mem (subset (Ico_subset_Icc_self h))).2.2.2)
    (fun _ h => (mem (subset (Ico_subset_Icc_self h))).2.1) fg
  exact phaseView_injective e.chart e.compatible _ _ (mem hb).2.2.1 (mem hb).2.2.2
    (solve (right_mem_Icc.mpr hb.1))

/-- Uniqueness on the entire common time interval for paths written in
arbitrary local frames, including different chart sequences. -/
theorem HamiltonTrace.unique [T2Space M] (Γ : Geometry M m) {L : ℝ} {f g : ℝ → CotPoint M}
    (hf : HamiltonTrace Γ L f) (hg : HamiltonTrace Γ L g) (equal : f 0 = g 0) : EqOn f g (Icc 0 L) := by
  let A := {t : ℝ | f t = g t}
  let B := {s : Icc 0 L | f s = g s}
  have cls : IsClosed B := by
    rw [← isOpen_compl_iff,isOpen_iff_mem_nhds]
    intro t ht
    change f t ≠ g t at ht
    by_cases bases : (f t).1 = (g t).1
    · obtain ⟨e,he,ex⟩ := Γ.cover (f t).1
      have ey : (g t).1 ∈ e.chart.source := bases ▸ ex
      have df := (continuousWithinAt_iff_continuousAt_restrict _ t.property).mp (hf.coord e he t t.property ex)
      have dg := (continuousWithinAt_iff_continuousAt_restrict _ t.property).mp (hg.coord e he t t.property ey)
      have ne : phaseView e.chart (f t) ≠ phaseView e.chart (g t) :=
        fun h => ht (phaseView_injective e.chart e.compatible _ _ ex ey h)
      filter_upwards [(df.ne_iff_eventually_ne dg).mp ne] with s hs
      exact fun h => hs (congrArg (phaseView e.chart) h)
    · have df := (continuousWithinAt_iff_continuousAt_restrict _ t.property).mp (hf.base _ t.property)
      have dg := (continuousWithinAt_iff_continuousAt_restrict _ t.property).mp (hg.base _ t.property)
      filter_upwards [(df.ne_iff_eventually_ne dg).mp bases] with s hs
      exact fun h => hs (congrArg Prod.fst h)
  have image : Subtype.val '' B = A ∩ Icc 0 L := by
    ext t
    constructor
    · rintro ⟨s,h,rfl⟩
      exact ⟨h,s.property⟩
    · rintro ⟨h,ht⟩
      exact ⟨⟨t,ht⟩,h,rfl⟩
  have closed := isClosed_Icc.isClosedMap_subtype_val _ cls
  rw [image] at closed
  apply closed.Icc_subset_of_forall_mem_nhdsWithin equal
  intro t ht
  exact (hf.equal_right Γ hg t ht.2 ht.1).filter_mono (nhdsWithin_mono t Ioi_subset_Ici_self)

#print axioms HamiltonTrace.equal_right
#print axioms HamiltonTrace.unique

/-- An ordinary Hamilton solution in any participating chart is a trace in
every overlapping frame. -/
theorem HamiltonTrace.of_chart (Γ : Geometry M m) (e : Frame M m) (he : e ∈ Γ.frames)
    (L : ℝ) (f : ℝ → Phase) (cf : ContinuousOn f (Icc 0 L))
    (inside : ∀ t ∈ Icc 0 L, (f t).1 ∈ e.chart.target)
    (ode : ∀ t ∈ Icc 0 L, HasDerivWithinAt f (hamiltonianField e.X (f t)) (Icc 0 L) t) :
    HamiltonTrace Γ L (fun t => packCov e.chart (e.chart.symm (f t).1) (f t).2) := by
  let x := fun t => e.chart.symm (f t).1
  let z := fun t => packCov e.chart (x t) (f t).2
  have cx : ContinuousOn x (Icc 0 L) := e.chart.symm.continuousOn.comp cf.fst inside
  have translate (d : Frame M m) (s : ℝ) (hs : s ∈ Icc 0 L) (dx : x s ∈ d.chart.source) :
      phaseView d.chart (z s) = phaseChange e.chart d.chart (f s) := by
    have h := phaseView_pack e.chart d.chart e.compatible d.compatible (x s) (e.chart.map_target (inside s hs)) dx (f s).2
    exact h
  have regular (d : Frame M m) (s : ℝ) (hs : s ∈ Icc 0 L) (dx : x s ∈ d.chart.source) :
      ContDiffAt ℝ 1 (phaseChange e.chart d.chart) (f s) := by
    have h := phaseChange_smooth _ _ e.compatible d.compatible (x s) (e.chart.map_target (inside s hs)) dx (f s).2
    simpa only [x,e.chart.right_inv (inside s hs),Prod.mk.eta] using h
  have localEq (d : Frame M m) (s : ℝ) (hs : s ∈ Icc 0 L) (dx : x s ∈ d.chart.source) :
      phaseView d.chart ∘ z =ᶠ[𝓝[Icc 0 L] s] phaseChange e.chart d.chart ∘ f := by
    filter_upwards [self_mem_nhdsWithin,(cx s hs) (d.chart.open_source.mem_nhds dx)] with t ht hd
    exact translate d t ht hd
  refine ⟨cx,?_,?_⟩
  · intro d _ t ht dx
    apply ((regular d t ht dx).continuousAt.comp_continuousWithinAt (cf t ht)).congr_of_eventuallyEq_of_mem
    · exact localEq d t ht dx
    · exact ht
  · intro d hd t ht dx
    have ti := Ico_subset_Icc_self ht
    have right := (ode t ti).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
    have der := ((regular d t ti dx).differentiableAt (by decide)).hasFDerivAt.comp_hasDerivWithinAt t right
    have field := phaseChange_hamiltonian Γ e d he hd (x t) (e.chart.map_target (inside t ti)) dx (f t).2
    simp only [x,e.chart.right_inv (inside t ti),Prod.mk.eta] at field
    rw [field,← translate d t ti dx] at der
    exact der.congr_of_eventuallyEq_of_mem ((localEq d t ti dx).filter_mono
      (nhdsWithin_le_of_mem (Icc_mem_nhdsGE_of_mem ht))) (le_refl t)

open Classical in
/-- A single fixed-source terminal point at normalized time one. Its value on
initial covectors with a trajectory is forced by trace uniqueness. -/
def normalTerminal (Γ : Geometry M m) (z : CotPoint M) : CotPoint M :=
  if h : ∃ f : ℝ → CotPoint M, HamiltonTrace Γ 1 f ∧ f 0 = z then h.choose 1 else z

theorem HamiltonTrace.terminal [T2Space M] (Γ : Geometry M m) {f : ℝ → CotPoint M}
    (tr : HamiltonTrace Γ 1 f) : normalTerminal Γ (f 0) = f 1 := by
  classical
  have h : ∃ g : ℝ → CotPoint M, HamiltonTrace Γ 1 g ∧ g 0 = f 0 := ⟨f,tr,rfl⟩
  rw [normalTerminal,dif_pos h]
  exact h.choose_spec.1.unique Γ tr h.choose_spec.2 (right_mem_Icc.mpr zero_le_one)

#print axioms HamiltonTrace.of_chart
#print axioms HamiltonTrace.terminal

end MinimizingSard.Five
