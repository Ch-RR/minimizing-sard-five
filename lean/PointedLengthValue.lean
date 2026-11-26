import FiveDimensionalStatement

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace MinimizingSard.Five

variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] {m n : ℕ}

/-- Lengths of all competitors in the original, arbitrary finite-frame presentation. -/
def attainableLengths (Γ : Geometry M m) (x y : M) : Set ℝ :=
  {l | ∃ (k : ℕ) (e : Fin (k+1) → Frame M m) (u : Fin (k+1) → Control m),
    (∀ i, e i ∈ Γ.frames) ∧ Joins e u x y ∧ length u = l}

def pointedLengthValue (Γ : Geometry M m) (x y : M) : ℝ :=
  sInf (attainableLengths Γ x y)

theorem control_length_nonneg (u : Fin n → Control m) : 0 ≤ length u :=
  Finset.sum_nonneg fun _ _ => intervalIntegral.integral_nonneg zero_le_one
    (fun _ _ => Real.sqrt_nonneg _)

variable {Γ : Geometry M m} {x y : M} {e : Fin (n+1) → Frame M m}
  {w : Fin (n+1) → Control m}

theorem pointedLengthValue_le (he : ∀ i, e i ∈ Γ.frames) (hw : Joins e w x y) :
    pointedLengthValue Γ x y ≤ length w := by
  apply csInf_le (s := attainableLengths Γ x y)
  · refine ⟨0, ?_⟩
    rintro _ ⟨k,d,v,_,_,rfl⟩
    exact control_length_nonneg v
  · exact ⟨n,e,w,he,hw,rfl⟩

theorem pointedLengthValue_eq (he : ∀ i, e i ∈ Γ.frames) (hw : Joins e w x y)
    (hmin : ∀ (k : ℕ) (d : Fin (k+1) → Frame M m) (v : Fin (k+1) → Control m),
      (∀ i, d i ∈ Γ.frames) → Joins d v x y → length w ≤ length v) :
    pointedLengthValue Γ x y = length w := by
  refine le_antisymm (pointedLengthValue_le he hw) (le_csInf ?_ ?_)
  · exact ⟨_,n,e,w,he,hw,rfl⟩
  · rintro _ ⟨k,d,v,hd,hv,rfl⟩
    exact hmin k d v hd hv

/-- The actual endpoint graph supplies competitors, including at controls with idle pieces. -/
theorem pointedLengthValue_comparison (he : ∀ i, e i ∈ Γ.frames) (hw : Joins e w x y)
    (hmin : ∀ (k : ℕ) (d : Fin (k+1) → Frame M m) (v : Fin (k+1) → Control m),
      (∀ i, d i ∈ Γ.frames) → Joins d v x y → length w ≤ length v)
    (c : OpenPartialHomeomorph M State) (G : (Fin (n+1) → Control m) → State)
    (graph : ∀ᶠ v in 𝓝 w, ∀ z, Joins e v x z ↔ z = c.symm (G v)) :
    ∀ᶠ v in 𝓝 w, pointedLengthValue Γ x (c.symm (G v)) - pointedLengthValue Γ x y
      ≤ length v - length w := by
  rw [pointedLengthValue_eq he hw hmin]
  filter_upwards [graph] with v hv
  exact sub_le_sub_right (pointedLengthValue_le he ((hv _).mpr rfl)) _

#print axioms control_length_nonneg
#print axioms pointedLengthValue_le
#print axioms pointedLengthValue_eq
#print axioms pointedLengthValue_comparison
end MinimizingSard.Five
