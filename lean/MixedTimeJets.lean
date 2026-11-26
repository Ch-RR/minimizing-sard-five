import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos

/-! The terminal first-jet inference from the two-time bracket constraint.
The reference-flow derivative identities and the two-time constraint are
explicit inputs; neither is asserted here for an arbitrary endpoint map. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace MinimizingSard.MixedTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
abbrev Jet (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] := E × (E →L[ℝ] E)
def jet (X : E → E) (q : E) : Jet E := (X q, fderiv ℝ X q)

private def bracketRight (v : Jet E) : Jet E →L[ℝ] E :=
  ((ContinuousLinearMap.apply ℝ E v.1).comp (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E))) -
    (v.2.comp (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E)))

private theorem bracketRight_jet (X Y : E → E) (q : E) :
    bracketRight (jet X q) (jet Y q) = VectorField.lieBracket ℝ X Y q := rfl

/-- Differentiate a vanishing functional on the two moving columns, then
recover the terminal value of the continuous bracket jet by a.e. equality. -/
theorem row_zero_of_two_columns {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : F →L[ℝ] ℝ) (X Y B : ℝ → F) (u v : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hB : ContinuousOn B (Icc a b))
    (hrow : ∀ t ∈ Ioo a b, L (X t) = 0 ∧ L (Y t) = 0)
    (hflow : ∀ᵐ t ∂volume.restrict (Ioo a b),
      HasDerivAt X (-(v t) • B t) t ∧ HasDerivAt Y (u t • B t) t ∧
      (u t ≠ 0 ∨ v t ≠ 0)) : L (B b) = 0 := by
  have interior : (fun t => L (B t)) =ᵐ[volume.restrict (Ioo a b)] fun _ => 0 := by
    filter_upwards [hflow, ae_restrict_mem measurableSet_Ioo] with t ht hmem
    have kill (Z : ℝ → F) (k : ℝ) (hd : HasDerivAt Z (k • B t) t)
        (hz : ∀ s ∈ Ioo a b, L (Z s) = 0) : k * L (B t) = 0 := by
      have der := L.hasFDerivAt.comp_hasDerivAt t hd
      have zero : HasDerivAt (L ∘ Z) 0 t :=
        (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq
          (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hmem) (fun s hs => hz s hs))
      simpa using der.unique zero
    rcases ht.2.2 with hu | hv
    · exact (mul_eq_zero.mp (kill Y (u t) ht.2.1 (fun s hs => (hrow s hs).2))).resolve_left hu
    · exact (mul_eq_zero.mp (kill X (-(v t)) ht.1 (fun s hs => (hrow s hs).1))).resolve_left
        (neg_ne_zero.mpr hv)
  rw [restrict_Ioo_eq_restrict_Icc] at interior
  exact Measure.eqOn_Icc_of_ae_eq volume hab.ne interior (L.continuous.comp_continuousOn hB)
    continuousOn_const (right_mem_Icc.mpr hab.le)

/-- The bracket is the actual mathlib spatial Lie bracket at q. Given
the pullback identities, the terminal row annihilates [Z,[X,Y]]. -/
theorem terminal_triple_bracket
    (p : E →L[ℝ] ℝ) (q : E) (X Y B : ℝ → E → E) (Z : E → E)
    (u v : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hend : B b = VectorField.lieBracket ℝ (X b) (Y b))
    (hB : ContinuousOn (fun t => jet (B t) q) (Icc a b))
    (mixed : ∀ t ∈ Ioo a b, p (VectorField.lieBracket ℝ Z (X t) q) = 0 ∧
      p (VectorField.lieBracket ℝ Z (Y t) q) = 0)
    (flow : ∀ᵐ t ∂volume.restrict (Ioo a b),
      HasDerivAt (fun s => jet (X s) q) (-(v t) • jet (B t) q) t ∧
      HasDerivAt (fun s => jet (Y s) q) (u t • jet (B t) q) t ∧
      (u t ≠ 0 ∨ v t ≠ 0)) :
    p (VectorField.lieBracket ℝ Z (VectorField.lieBracket ℝ (X b) (Y b)) q) = 0 := by
  rw [← hend]
  exact row_zero_of_two_columns (p.comp (bracketRight (jet Z q))) _ _ _ u v hab hB mixed flow

#print axioms terminal_triple_bracket

/-- For two signed column derivatives, a nonzero terminal row on their common
bracket forces an idle final interval. The row can test values or first jets. -/
theorem column_row_or_idle {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : F →L[ℝ] ℝ) (X Y B : ℝ → F) (u v : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hB : ContinuousAt B b) (columns : ∀ t ∈ Ioo a b, L (X t) = 0 ∧ L (Y t) = 0)
    (flow : ∀ᵐ t ∂volume.restrict (Ioo a b),
      HasDerivAt X (-(v t) • B t) t ∧ HasDerivAt Y (u t • B t) t) :
    L (B b) = 0 ∨ ∃ c ∈ Ico a b, ∀ᵐ t ∂volume.restrict (Ioo c b), u t = 0 ∧ v t = 0 := by
  by_cases endZero : L (B b) = 0
  · exact Or.inl endZero
  right
  have near : ∀ᶠ t in 𝓝 b, L (B t) ≠ 0 :=
    (L.continuous.continuousAt.comp (x := b) hB).eventually_ne endZero
  obtain ⟨c,hc,off⟩ := exists_Ioc_subset_of_mem_nhds' near hab
  refine ⟨c,hc,?_⟩
  have sub := Ioo_subset_Ioo_left (b := b) hc.1
  filter_upwards [ae_restrict_of_ae_restrict_of_subset sub flow,ae_restrict_mem measurableSet_Ioo] with t dt ht
  have nz := off (show t ∈ Ioc c b from ⟨ht.1,ht.2.le⟩)
  have kill (S : ℝ → F) (w : ℝ) (d : HasDerivAt S (w • B t) t)
      (row : ∀ s ∈ Ioo a b, L (S s) = 0) : w = 0 := by
    have zero : HasDerivAt (fun s => L (S s)) 0 t :=
      (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq
        (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds (sub ht)) row)
    have eq := (L.hasFDerivAt.comp_hasDerivAt t d).unique zero
    exact (mul_eq_zero.mp (show w * L (B t) = 0 by simpa using eq)).resolve_right nz
  exact ⟨kill Y _ dt.2 (fun s hs => (columns s hs).2),
    neg_eq_zero.mp (kill X _ dt.1 (fun s hs => (columns s hs).1))⟩

/-- A nonzero terminal bracket pairing forces both controls to vanish
almost everywhere on a final open interval. No speed condition is used. -/
theorem terminal_bracket_or_idle
    (p : E →L[ℝ] ℝ) (q : E) (X Y B : ℝ → E → E) (Z : E → E)
    (u v : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hB : ContinuousAt (fun t => jet (B t) q) b)
    (mixed : ∀ t ∈ Ioo a b, p (VectorField.lieBracket ℝ Z (X t) q) = 0 ∧
      p (VectorField.lieBracket ℝ Z (Y t) q) = 0)
    (flow : ∀ᵐ t ∂volume.restrict (Ioo a b),
      HasDerivAt (fun s => jet (X s) q) (-(v t) • jet (B t) q) t ∧
      HasDerivAt (fun s => jet (Y s) q) (u t • jet (B t) q) t) :
    p (VectorField.lieBracket ℝ Z (B b) q) = 0 ∨ ∃ c ∈ Ico a b,
      ∀ᵐ t ∂volume.restrict (Ioo c b), u t = 0 ∧ v t = 0 := by
  let L := p.comp (bracketRight (jet Z q))
  exact column_row_or_idle L _ _ _ u v hab hB mixed flow

#print axioms terminal_bracket_or_idle
end MinimizingSard.MixedTime
