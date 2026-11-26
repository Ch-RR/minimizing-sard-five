import NormalArc

noncomputable section
open Set Filter IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five

variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M]
abbrev Covector := State →L[ℝ] ℝ
abbrev CotPoint (M : Type*) := M × Covector

/-- `chartJac a b x` sends tangent coordinates in chart `a` to those in `b`. -/
def chartJac (a b : OpenPartialHomeomorph M State) (x : M) := fderiv ℝ (b ∘ a.symm) (a x)

/-- Store the covector at its base in that point's preferred chart. No topology
on this storage product is needed to compare covectors in a common chart. -/
def packCov (a : OpenPartialHomeomorph M State) (x : M) (p : Covector) : CotPoint M :=
  (x,p.comp (chartJac (chartAt State x) a x))

def phaseView (a : OpenPartialHomeomorph M State) (z : CotPoint M) : Phase :=
  (a z.1,z.2.comp (chartJac a (chartAt State z.1) z.1))

def phaseChange (a b : OpenPartialHomeomorph M State) (z : Phase) : Phase :=
  let x := a.symm z.1
  (b x,z.2.comp (fderiv ℝ (a ∘ b.symm) (b x)))

variable [IsManifold 𝓘(ℝ,State) ∞ M]

theorem phaseView_pack (a b : OpenPartialHomeomorph M State)
    (ha : a ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (hb : b ∈ maximalAtlas 𝓘(ℝ,State) ∞ M)
    (x : M) (ax : x ∈ a.source) (bx : x ∈ b.source) (p : Covector) :
    phaseView b (packCov a x p) = (b x,p.comp (chartJac b a x)) := by
  refine Prod.ext (by rfl) ?_
  apply ContinuousLinearMap.ext
  intro h
  have chain := transition_chain b (chartAt State x) a hb (chart_mem_maximalAtlas _) ha x bx (mem_chart_source _ _) ax
  exact congrArg p (DFunLike.congr_fun chain h)

theorem pack_phaseView (a : OpenPartialHomeomorph M State)
    (ha : a ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (z : CotPoint M) (az : z.1 ∈ a.source) :
    packCov a z.1 (phaseView a z).2 = z := by
  refine Prod.ext (by rfl) ?_
  apply ContinuousLinearMap.ext
  intro h
  have left := transition_left (chartAt State z.1) a (chart_mem_maximalAtlas _) ha z.1 (mem_chart_source _ _) az
  exact congrArg z.2 (DFunLike.congr_fun left h)

theorem phaseView_injective (a : OpenPartialHomeomorph M State) (ha : a ∈ maximalAtlas 𝓘(ℝ,State) ∞ M)
    (z w : CotPoint M) (hz : z.1 ∈ a.source) (hw : w.1 ∈ a.source) (eq : phaseView a z = phaseView a w) : z = w := by
  have bases := a.injOn hz hw (congrArg Prod.fst eq)
  calc z = packCov a z.1 (phaseView a z).2 := (pack_phaseView a ha z hz).symm
       _ = packCov a w.1 (phaseView a w).2 := by rw [bases,eq]
       _ = w := pack_phaseView a ha w hw

theorem phaseView_change (a b : OpenPartialHomeomorph M State) (ha : a ∈ maximalAtlas 𝓘(ℝ,State) ∞ M)
    (hb : b ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (z : CotPoint M) (az : z.1 ∈ a.source) (bz : z.1 ∈ b.source) :
    phaseChange a b (phaseView a z) = phaseView b z := by
  have eq := phaseView_pack a b ha hb z.1 az bz (phaseView a z).2
  rw [pack_phaseView a ha z az] at eq
  simpa only [phaseChange,show (phaseView a z).1 = a z.1 from rfl,a.left_inv az,chartJac] using eq.symm

omit [IsManifold 𝓘(ℝ,State) ∞ M] in
theorem phaseChange_smooth (a b : OpenPartialHomeomorph M State)
    (ha : a ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (hb : b ∈ maximalAtlas 𝓘(ℝ,State) ∞ M)
    (x : M) (ax : x ∈ a.source) (bx : x ∈ b.source) (p : Covector) :
    ContDiffAt ℝ 1 (phaseChange a b) (a x,p) := by
  let F := b ∘ a.symm
  have atx : F (a x) = b x := congrArg b (a.left_inv ax)
  have cf : ContDiffAt ℝ 1 F (a x) := transition_smooth a b ha hb x ax bx
  have cb : ContDiffAt ℝ 2 (a ∘ b.symm) (b x) := transition_smooth b a hb ha x bx ax
  have reg := cf.comp (a x,p) contDiffAt_fst
  have cov := (cb.fderiv_right (m := 1) (by decide))
  rw [← atx] at cov
  exact reg.prodMk (contDiffAt_snd.clm_comp (cov.comp (a x,p) reg))

/-- The full cotangent change of coordinates sends the source Hamiltonian
vector to the target Hamiltonian vector. -/
theorem phaseChange_hamiltonian {m : ℕ} (Γ : Geometry M m) (e d : Frame M m)
    (he : e ∈ Γ.frames) (hd : d ∈ Γ.frames) (x : M) (ex : x ∈ e.chart.source) (dx : x ∈ d.chart.source)
    (p : Covector) :
    fderiv ℝ (phaseChange e.chart d.chart) (e.chart x,p) (hamiltonianField e.X (e.chart x,p)) =
      hamiltonianField d.X (phaseChange e.chart d.chart (e.chart x,p)) := by
  let F := d.chart ∘ e.chart.symm
  let B := e.chart ∘ d.chart.symm
  let q := e.chart x
  let k := d.chart x
  let z : Phase := (q,p)
  let J := fderiv ℝ F q
  let R := fderiv ℝ B k
  let R' := fderiv ℝ (fderiv ℝ B) k
  let v := hamiltonianField e.X z
  let w := hamiltonianField d.X (k,p.comp R)
  have fq : F q = k := congrArg d.chart (e.chart.left_inv ex)
  have bk : B k = q := congrArg e.chart (d.chart.left_inv dx)
  have cs : ContDiffAt ℝ 1 F q := transition_smooth _ _ e.compatible d.compatible x ex dx
  have cr : ContDiffAt ℝ 2 B k := transition_smooth _ _ d.compatible e.compatible x dx ex
  have ds := (cs.differentiableAt (by decide)).hasFDerivAt.comp z (hasFDerivAt_fst (𝕜 := ℝ) (p := z))
  have dr : HasFDerivAt (fderiv ℝ B) R' (F q) := fq ▸ ((cr.fderiv_right (m := 1) (by decide)).differentiableAt (by decide)).hasFDerivAt
  have der := ds.prodMk ((hasFDerivAt_snd (𝕜 := ℝ) (p := z)).clm_comp (dr.comp z ds))
  have reverse := hamiltonian_field_overlap Γ d e hd he x ⟨dx,ex⟩ p
  change R w.1 = (hamiltonianField e.X (B k,p)).1 ∧
    ∀ h, w.2 h = (hamiltonianField e.X (B k,p)).2 (R h) + p (R' w.1 h) at reverse
  rw [bk] at reverse
  have cancel := transition_left d.chart e.chart d.compatible e.compatible x dx ex
  have spatial : J v.1 = w.1 := (congrArg J reverse.1.symm).trans (DFunLike.congr_fun cancel w.1)
  have atz : phaseChange e.chart d.chart z = (k,p.comp R) := by
    change (F q,p.comp (fderiv ℝ B (F q))) = _
    rw [fq]
  change fderiv ℝ (phaseChange e.chart d.chart) z v = _
  rw [show fderiv ℝ (phaseChange e.chart d.chart) z = _ from der.fderiv,atz]
  apply Prod.ext spatial
  apply ContinuousLinearMap.ext
  intro h
  change p (R' (J v.1) h) + v.2 (fderiv ℝ B (F q) h) = w.2 h
  rw [fq,spatial,add_comm]
  exact (reverse.2 h).symm

#print axioms phaseView_pack
#print axioms phaseView_change
#print axioms phaseChange_smooth
#print axioms phaseChange_hamiltonian
end MinimizingSard.Five
