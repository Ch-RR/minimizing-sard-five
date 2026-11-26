import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.FieldSimp

/-! A two-component symmetric Hessian with nowhere-surjective polar
has its whole range in a line. No dimension bound on the input. -/
namespace MinimizingSard.Hessian

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (A B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)

def minor (i j k l : V) : ℝ := A i j * B k l - B i j * A k l

theorem all_minors_zero
    (sA : ∀ i j, A i j = A j i) (sB : ∀ i j, B i j = B j i)
    (row : ∀ i j l, minor A B i j i l = 0) (i j k l : V) :
    minor A B i j k l = 0 := by
  have flip (a b c d : V) : minor A B a b c d = -minor A B c b a d := by
    have h := row (a + c) b d
    have ha := row a b d
    have hc := row c b d
    simp only [minor, map_add, LinearMap.add_apply] at h ha hc ⊢
    linarith only [h, ha, hc]
  have sym (a b c d : V) : minor A B a b c d = minor A B b a c d := by
    unfold minor
    rw [sA a b, sB a b]
  have hn : minor A B i j k l = -minor A B i j k l := calc
    minor A B i j k l = -minor A B k j i l := flip _ _ _ _
    _ = -minor A B j k i l := congrArg Neg.neg (sym _ _ _ _)
    _ = minor A B i k j l := by rw [flip j k i l, neg_neg]
    _ = minor A B k i j l := sym _ _ _ _
    _ = -minor A B j i k l := flip _ _ _ _
    _ = -minor A B i j k l := congrArg Neg.neg (sym _ _ _ _)
  linarith

theorem exists_annihilating_row
    (sA : ∀ i j, A i j = A j i) (sB : ∀ i j, B i j = B j i)
    (row : ∀ i j l, minor A B i j i l = 0) :
    ∃ p q : ℝ, (p ≠ 0 ∨ q ≠ 0) ∧ ∀ k l, p * A k l + q * B k l = 0 := by
  by_cases hex : ∃ i j, A i j ≠ 0
  · obtain ⟨i, j, h⟩ := hex
    refine ⟨-B i j, A i j, Or.inr h, ?_⟩
    intro k l
    have hm := all_minors_zero A B sA sB row i j k l
    unfold minor at hm
    linarith
  · refine ⟨1, 0, Or.inl one_ne_zero, ?_⟩
    intro k l
    have hz : A k l = 0 := by
      by_contra hn
      exact hex ⟨k, l, hn⟩
    simp [hz]

#print axioms all_minors_zero
#print axioms exists_annihilating_row

/-- Failure of surjectivity of the actual two-component polar implies
the pointwise determinant condition used above. -/
theorem minor_zero_of_polar_not_onto (i : V)
    (hs : ¬ Function.Surjective (fun v => (A i v, B i v))) (j l : V) :
    minor A B i j i l = 0 := by
  by_contra hn
  apply hs
  rintro ⟨x,y⟩
  let d := minor A B i j i l
  refine ⟨((x * B i l - y * A i l) / d) • j +
    ((y * A i j - x * B i j) / d) • l, ?_⟩
  have hd : d ≠ 0 := hn
  apply Prod.ext <;> simp only [map_add, map_smul, smul_eq_mul] <;>
    field_simp [hd] <;> dsimp [d, minor] <;> ring

open Module

private def rowOnPlane (p q : ℝ) : (ℝ × ℝ) →ₗ[ℝ] ℝ :=
  p • LinearMap.fst ℝ ℝ ℝ + q • LinearMap.snd ℝ ℝ ℝ

/-- The algebraic identification of the third layer. The analytic
finite-rank implication is visible as an input. The Hessian line,
its inverse image, and the infinite-rank assertion are conclusions. -/
theorem five_dimensional_hessian_flag {T : Type*} [AddCommGroup T] [Module ℝ T]
    [FiniteDimensional ℝ T] (dimT : finrank ℝ T = 5)
    (π : T →ₗ[ℝ] ℝ × ℝ) (onto : Function.Surjective π)
    (H : Submodule ℝ T) (growth : 4 ≤ finrank ℝ H)
    (sA : ∀ i j, A i j = A j i) (sB : ∀ i j, B i j = B j i)
    (noRegular : ∀ i, ¬ Function.Surjective (fun v => (A i v, B i v)))
    (finiteRow : ∀ p q : ℝ, FiniteDimensional ℝ (LinearMap.range (p • A + q • B)) →
      ∀ t ∈ H, p * (π t).1 + q * (π t).2 = 0) :
    let L := Submodule.span ℝ (Set.range (fun z : V × V => (A z.1 z.2, B z.1 z.2)))
    finrank ℝ L = 1 ∧ H = L.comap π ∧ finrank ℝ H = 4 ∧
      ¬ (FiniteDimensional ℝ (LinearMap.range A) ∧ FiniteDimensional ℝ (LinearMap.range B)) := by
  classical
  intro L
  have planeDim : finrank ℝ (ℝ × ℝ) = 2 := by simp [Module.finrank_prod]
  have dimKer := π.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr onto, finrank_top, planeDim, dimT] at dimKer
  have infiniteRow : ¬ (FiniteDimensional ℝ (LinearMap.range A) ∧
      FiniteDimensional ℝ (LinearMap.range B)) := by
    rintro ⟨hA,hB⟩
    have vanA := finiteRow 1 0 (by rw [one_smul, zero_smul, add_zero]; exact hA)
    have vanB := finiteRow 0 1 (by rw [zero_smul, one_smul, zero_add]; exact hB)
    have leKer : H ≤ LinearMap.ker π := by
      intro t ht
      apply Prod.ext
      · simpa using vanA t ht
      · simpa using vanB t ht
    have hle := Submodule.finrank_mono leKer
    omega
  obtain ⟨p,q,hpq,hrow⟩ := exists_annihilating_row A B sA sB
    (fun i => minor_zero_of_polar_not_onto A B i (noRegular i))
  have zeroRow : p • A + q • B = 0 := by
    ext a b
    exact hrow a b
  let f := rowOnPlane p q
  have f_ne : f ≠ 0 := by
    intro hf
    rcases hpq with hp | hq
    · exact hp (by simpa [f, rowOnPlane] using LinearMap.congr_fun hf ((1,0) : ℝ × ℝ))
    · exact hq (by simpa [f, rowOnPlane] using LinearMap.congr_fun hf ((0,1) : ℝ × ℝ))
  have fc_ne : f.comp π ≠ 0 := by
    intro hz
    apply f_ne
    apply LinearMap.ext
    intro z
    obtain ⟨t,rfl⟩ := onto z
    exact LinearMap.congr_fun hz t
  have dimLine := Module.Dual.finrank_ker_add_one_of_ne_zero f_ne
  rw [planeDim] at dimLine
  have dimHyper := Module.Dual.finrank_ker_add_one_of_ne_zero fc_ne
  rw [dimT] at dimHyper
  have HL : H ≤ LinearMap.ker (f.comp π) := by
    apply finiteRow p q
    rw [zeroRow, LinearMap.range_zero]
    infer_instance
  have eqH := Submodule.eq_of_le_of_finrank_le HL (by omega)
  have LL : L ≤ LinearMap.ker f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a,b⟩,rfl⟩
    exact hrow a b
  have nonzero : L ≠ ⊥ := by
    intro hz
    have zeroPair (a b : V) : (A a b, B a b) = 0 := by
      have hm : (A a b, B a b) ∈ L := Submodule.subset_span ⟨(a,b),rfl⟩
      rwa [hz, Submodule.mem_bot] at hm
    have hA : A = 0 := by ext a b; exact congrArg Prod.fst (zeroPair a b)
    have hB : B = 0 := by ext a b; exact congrArg Prod.snd (zeroPair a b)
    apply infiniteRow
    rw [hA,hB,LinearMap.range_zero]
    exact ⟨inferInstance,inferInstance⟩
  have pos := Submodule.one_le_finrank_iff.mpr nonzero
  have eqL := Submodule.eq_of_le_of_finrank_le LL (by omega)
  refine ⟨by rw [eqL]; omega, ?_, by rw [eqH]; omega, infiniteRow⟩
  rw [eqH,eqL]
  rfl

#print axioms minor_zero_of_polar_not_onto
#print axioms five_dimensional_hessian_flag
end MinimizingSard.Hessian
