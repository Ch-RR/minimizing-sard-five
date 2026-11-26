import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The dependent quadratic/cubic branch of the five-dimensional proof.
The input module need not carry a topology or have finite dimension. -/
namespace MinimizingSard.Jets

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (A : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (C : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ)

/-- A nonzero two-by-two minor guarantees a nonisotropic vector on the
orthogonal hyperplane of any nonisotropic vector. -/
private theorem orthogonal_witness
    (sym : ∀ x y, A x y = A y x)
    (rank : ∃ a b c d, A a c * A b d ≠ A a d * A b c)
    (x : V) (hx : A x x ≠ 0) : ∃ y, A x y = 0 ∧ A y y ≠ 0 := by
  by_contra! bad
  have diag (v : V) : A x x * A v v = A x v ^ 2 := by
    let y := A x x • v - A x v • x
    have hxy : A x y = 0 := by simp [y, mul_comm]
    have hz := bad y hxy
    simp only [y, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, ← sym x v] at hz
    apply (mul_left_cancel₀ hx)
    nlinarith only [hz]
  have pol (v w : V) : A x x * A v w = A x v * A x w := by
    have h := diag (v+w)
    simp only [map_add, LinearMap.add_apply, ← sym v w] at h
    linarith only [h, diag v, diag w]
  obtain ⟨a,b,c,d,hm⟩ := rank
  apply hm
  apply mul_left_cancel₀ (pow_ne_zero 2 hx)
  calc
    A x x ^ 2 * (A a c * A b d) = (A x x * A a c) * (A x x * A b d) := by ring
    _ = (A x x * A a d) * (A x x * A b c) := by rw [pol, pol, pol, pol]; ring
    _ = A x x ^ 2 * (A a d * A b c) := by ring

/-- If all polar minors of a quadratic and a cubic vanish and the
quadratic has rank at least two, the diagonal cubic vanishes everywhere. -/
theorem cubic_zero_of_dependent_polars
    (sym : ∀ x y, A x y = A y x)
    (s12 : ∀ x y z, C x y z = C y x z) (s23 : ∀ x y z, C x y z = C x z y)
    (rank : ∃ a b c d, A a c * A b d ≠ A a d * A b c)
    (dep : ∀ h a b, A h a * C h h b = A h b * C h h a) :
    ∀ x, C x x x = 0 := by
  have regular (x : V) (hx : A x x ≠ 0) : C x x x = 0 := by
    obtain ⟨y,hxy,hy⟩ := orthogonal_witness A sym rank x hx
    have hyx : A y x = 0 := (sym y x).trans hxy
    have h1 : C x x y = 0 := by
      simpa [hxy, hx] using dep x x y
    have h2 : C y y x = 0 := by
      simpa [hyx, hy] using dep y y x
    have h3 : C x y x = 0 := (s23 x y x).trans h1
    have h4 : C y x x = 0 := (s12 y x x).trans h3
    have h5 : C y x y = 0 := (s23 y x y).trans h2
    have h6 : C x y y = 0 := (s12 x y y).trans h5
    have plus := dep (x+y) x y
    have minus := dep (x-y) x y
    simp [hxy, hyx, h1, h2, h3, h4, h5, h6] at plus minus
    have : A y y * C x x x = 0 := by linarith only [plus, minus]
    exact (mul_eq_zero.mp this).resolve_left hy
  intro x
  by_cases hx : A x x = 0
  · by_cases hr : ∀ y, A x y = 0
    · have hex : ∃ y, A y y ≠ 0 := by
        by_contra! hz
        have hall (v w : V) : A v w = 0 := by
          have hh := hz (v+w)
          simp only [map_add, LinearMap.add_apply, hz, ← sym v w] at hh
          linarith
        obtain ⟨a,b,c,d,hm⟩ := rank
        exact hm (by simp [hall])
      obtain ⟨y,hy⟩ := hex
      have hyx := (sym y x).trans (hr y)
      have h1 : C y y x = 0 := by simpa [hy,hyx] using dep y y x
      have h2 := (s23 y x y).trans h1
      have h3 := (s12 x y y).trans h2
      have hp := regular (x+y) (by simpa [hr,hyx] using hy)
      have hm := regular (x-y) (by simpa [hr,hyx] using hy)
      simp [h1,h2,h3] at hp hm
      linarith only [hp,hm]
    · obtain ⟨y,hy⟩ := not_forall.mp hr
      simpa [hx,hy] using (dep x y x).symm
  · exact regular x hx

#print axioms cubic_zero_of_dependent_polars
end MinimizingSard.Jets
