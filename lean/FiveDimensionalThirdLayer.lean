import L2MovingEndpoint
import PulseExistence
import FiveDimensionalStatement
import TwoComponentHessian

/-! Identify the terminal rank-two layer with the bracket-word definition
used by the five-dimensional target, including both bracket orderings. -/
noncomputable section
open Set
open MinimizingSard.Five MinimizingSard.PulseGeometry
namespace MinimizingSard.Five

def BracketWord.order {m : ℕ} : BracketWord m → ℕ
  | .field _ => 1
  | .bracket a b => a.order + b.order

private theorem word_positive {m : ℕ} (w : BracketWord m) : 0 < w.order := by
  induction w with
  | field => exact Nat.one_pos
  | bracket a b ha hb => change 0 < a.order + b.order; omega

private theorem leaf {w : BracketWord 2} (h : w.order ≤ 1) : ∃ i, w = .field i := by
  cases w with
  | field i => exact ⟨i,rfl⟩
  | bracket a b =>
    have := word_positive a
    have := word_positive b
    change a.order + b.order ≤ 1 at h
    omega

def wordLayer {m : ℕ} (X : Fin m → State → State) (q : State) (k : ℕ) : Submodule ℝ State :=
  Submodule.span ℝ {v | ∃ w : BracketWord m, w.order ≤ k ∧ w.eval X q = v}

private theorem pair_shape (X : Fin 2 → State → State) (i j : Fin 2) :
    let B := VectorField.lieBracket ℝ (X 0) (X 1)
    VectorField.lieBracket ℝ (X i) (X j) = 0 ∨
    VectorField.lieBracket ℝ (X i) (X j) = B ∨ VectorField.lieBracket ℝ (X i) (X j) = -B := by
  fin_cases i <;> fin_cases j
  · exact Or.inl (VectorField.lieBracket_self ..)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (funext fun _ => VectorField.lieBracket_swap))
  · exact Or.inl (VectorField.lieBracket_self ..)

theorem frame_third_layer_eq_words (Y : Fin 2 → State → State) (q : State) :
    (let B := VectorField.lieBracket ℝ (Y 0) (Y 1)
     Submodule.span ℝ (range (fun i => Y i q) ∪ {B q} ∪ range (fun i => VectorField.lieBracket ℝ (Y i) B q))) =
      wordLayer Y q 3 := by
  let B := VectorField.lieBracket ℝ (Y 0) (Y 1)
  let L := Submodule.span ℝ (range (fun i => Y i q) ∪ {B q} ∪ range (fun i => VectorField.lieBracket ℝ (Y i) B q))
  have fieldMem (i) : Y i q ∈ L :=
    Submodule.subset_span (Or.inl (Or.inl ⟨i,rfl⟩))
  have bMem : B q ∈ L := Submodule.subset_span (Or.inl (Or.inr rfl))
  have tripleMem (i) : VectorField.lieBracket ℝ (Y i) B q ∈ L :=
    Submodule.subset_span (Or.inr ⟨i,rfl⟩)
  have pairMem (i j) : VectorField.lieBracket ℝ (Y i) (Y j) q ∈ L := by
    rcases pair_shape Y i j with h | h | h
    · rw [h]; exact L.zero_mem
    · rw [h]; exact bMem
    · rw [h]; exact L.neg_mem bMem
  have nested (i j k) :
      VectorField.lieBracket ℝ (Y i) (VectorField.lieBracket ℝ (Y j) (Y k)) q ∈ L := by
    rcases pair_shape Y j k with h | h | h
    · rw [h,VectorField.lieBracket_zero_right]; exact L.zero_mem
    · rw [h]; exact tripleMem i
    · rw [h]
      have neg : VectorField.lieBracket ℝ (Y i) (-B) q = -VectorField.lieBracket ℝ (Y i) B q := by
        simp only [VectorField.lieBracket,fderiv_neg,ContinuousLinearMap.neg_apply,
          Pi.neg_apply,map_neg]
        abel
      rw [neg]
      exact L.neg_mem (tripleMem i)
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ((⟨i,rfl⟩ | hx) | ⟨i,rfl⟩)
    · exact Submodule.subset_span ⟨.field i,by change 1 ≤ 3; decide,rfl⟩
    · obtain rfl := Set.mem_singleton_iff.mp hx
      exact Submodule.subset_span ⟨.bracket (.field 0) (.field 1),by decide,rfl⟩
    · exact Submodule.subset_span ⟨.bracket (.field i) (.bracket (.field 0) (.field 1)),
        by change 3 ≤ 3; decide,rfl⟩
  · apply Submodule.span_le.mpr
    rintro x ⟨w,h,rfl⟩
    cases w with
    | field i => exact fieldMem i
    | bracket a b =>
      change a.order + b.order ≤ 3 at h
      cases a with
      | field i =>
        cases b with
        | field j => exact pairMem i j
        | bracket b c =>
          change 1 + (b.order + c.order) ≤ 3 at h
          have hb := word_positive b
          have hc := word_positive c
          obtain ⟨j,rfl⟩ := leaf (w := b) (by omega)
          obtain ⟨k,rfl⟩ := leaf (w := c) (by omega)
          exact nested i j k
      | bracket a c =>
        have ha := word_positive a
        have hb := word_positive b
        have hc := word_positive c
        change a.order + c.order + b.order ≤ 3 at h
        obtain ⟨i,rfl⟩ := leaf (w := a) (by omega)
        obtain ⟨k,rfl⟩ := leaf (w := c) (by omega)
        obtain ⟨j,rfl⟩ := leaf (w := b) (by omega)
        change VectorField.lieBracket ℝ (VectorField.lieBracket ℝ (Y i) (Y k)) (Y j) q ∈ L
        rw [VectorField.lieBracket_swap]
        exact L.neg_mem (nested j i k)

theorem third_layer_eq_bracket_words (X : Columns State) (q : State) :
    thirdLayer X q = wordLayer (fun i => X.Y i 1) q 3 :=
  frame_third_layer_eq_words _ q

#print axioms third_layer_eq_bracket_words

open MeasureTheory

/-- At a rank-two patch satisfying the pointwise growth and polar
conditions, use the actual endpoint Hessian and the actual bracket words
to identify the four-dimensional hyperplane. No finite-row annihilation
or Hessian line is passed in as a hypothesis. -/
theorem terminal_hessian_flag_from_endpoint_ode
    (X : Columns State) (q : State) (F : Controls → State) (endpoint : X.Endpoint q F)
    (smooth : ContDiffAt ℝ 2 F 0)
    (π : State →L[ℝ] ℝ × ℝ) (onto : Function.Surjective π)
    (cokernel : LinearMap.ker π.toLinearMap = LinearMap.range (fderiv ℝ F 0).toLinearMap)
    (growth : 4 ≤ Module.finrank ℝ (wordLayer (fun i => X.Y i 1) q 3))
    (noRegular : ∀ h : LinearMap.ker (fderiv ℝ F 0).toLinearMap,
      ¬ Function.Surjective (fun w : LinearMap.ker (fderiv ℝ F 0).toLinearMap =>
        π ((fderiv ℝ (fderiv ℝ F) 0 h) w)))
    (B : ℝ → State → State) (u v : ℝ → ℝ)
    (hend : B 1 = VectorField.lieBracket ℝ (X.Y 0 1) (X.Y 1 1))
    (hB : ContinuousOn (fun t => MixedTime.jet (B t) q) (Icc 0 1))
    (flow : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1),
      HasDerivAt (fun s => MixedTime.jet (X.Y 0 s) q) (-(v t) • MixedTime.jet (B t) q) t ∧
      HasDerivAt (fun s => MixedTime.jet (X.Y 1 s) q) (u t • MixedTime.jet (B t) q) t ∧
      (u t ≠ 0 ∨ v t ≠ 0)) :
    let K := LinearMap.ker (fderiv ℝ F 0).toLinearMap
    let L := Submodule.span ℝ (range (fun z : K × K => π ((fderiv ℝ (fderiv ℝ F) 0 z.1) z.2)))
    Module.finrank ℝ L = 1 ∧ wordLayer (fun i => X.Y i 1) q 3 = L.comap π.toLinearMap ∧
      Module.finrank ℝ (wordLayer (fun i => X.Y i 1) q 3) = 4 := by
  let K := LinearMap.ker (fderiv ℝ F 0).toLinearMap
  let p₁ := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp π
  let p₂ := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp π
  let A := restrictedHessianRow F p₁
  let C := restrictedHessianRow F p₂
  have sym := smooth.isSymmSndFDerivAt (by simp)
  have fin (a b : ℝ) (hf : FiniteDimensional ℝ (LinearMap.range (a • A + b • C))) :
      ∀ z ∈ wordLayer (fun i => X.Y i 1) q 3, a * (π z).1 + b * (π z).2 = 0 := by
    let p := a • p₁ + b • p₂
    have add : restrictedHessianRow F p = a • A + b • C := by
      apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      rfl
    haveI : FiniteDimensional ℝ (LinearMap.range (restrictedHessianRow F p)) := add.symm ▸ hf
    have row (d : Controls) : p (fderiv ℝ F 0 d) = 0 := by
      have hz : π (fderiv ℝ F 0 d) = 0 := by
        change fderiv ℝ F 0 d ∈ LinearMap.ker π.toLinearMap
        rw [cokernel]
        exact ⟨d,rfl⟩
      change a * (π (fderiv ℝ F 0 d)).1 + b * (π (fderiv ℝ F 0 d)).2 = 0
      simp [hz]
    have ann := finite_row_annihilates_third_layer X q F p endpoint smooth row B u v hend hB flow
    rw [third_layer_eq_bracket_words] at ann
    exact fun z hz => ann hz
  have result := Hessian.five_dimensional_hessian_flag A C (T := State)
    (Module.finrank_fin_fun ℝ) π.toLinearMap onto _ growth
    (fun x y => congrArg p₁ (sym x y)) (fun x y => congrArg p₂ (sym x y)) noRegular fin
  exact ⟨result.1,result.2.1,result.2.2.1⟩

#print axioms terminal_hessian_flag_from_endpoint_ode

/-- Coefficient-level version. The control-space second derivative follows
from the integral ODE and the spatial jets of its moving columns. -/
theorem terminal_hessian_flag_from_spatial_jets
    (X : Columns State) (jets : SpatialJets X) (q : State) (F : Controls → State)
    (endpoint : X.Endpoint q F)
    (π : State →L[ℝ] ℝ × ℝ) (onto : Function.Surjective π)
    (cokernel : LinearMap.ker π.toLinearMap = LinearMap.range (fderiv ℝ F 0).toLinearMap)
    (growth : 4 ≤ Module.finrank ℝ (wordLayer (fun i => X.Y i 1) q 3))
    (noRegular : ∀ h : LinearMap.ker (fderiv ℝ F 0).toLinearMap,
      ¬ Function.Surjective (fun w : LinearMap.ker (fderiv ℝ F 0).toLinearMap =>
        π ((fderiv ℝ (fderiv ℝ F) 0 h) w)))
    (B : ℝ → State → State) (u v : ℝ → ℝ)
    (hend : B 1 = VectorField.lieBracket ℝ (X.Y 0 1) (X.Y 1 1))
    (hB : ContinuousOn (fun t => MixedTime.jet (B t) q) (Icc 0 1))
    (flow : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1),
      HasDerivAt (fun s => MixedTime.jet (X.Y 0 s) q) (-(v t) • MixedTime.jet (B t) q) t ∧
      HasDerivAt (fun s => MixedTime.jet (X.Y 1 s) q) (u t • MixedTime.jet (B t) q) t ∧
      (u t ≠ 0 ∨ v t ≠ 0)) :
    let K := LinearMap.ker (fderiv ℝ F 0).toLinearMap
    let L := Submodule.span ℝ (range (fun z : K × K => π ((fderiv ℝ (fderiv ℝ F) 0 z.1) z.2)))
    Module.finrank ℝ L = 1 ∧ wordLayer (fun i => X.Y i 1) q 3 = L.comap π.toLinearMap ∧
      Module.finrank ℝ (wordLayer (fun i => X.Y i 1) q 3) = 4 :=
  terminal_hessian_flag_from_endpoint_ode X q F endpoint
    (smooth_integral_endpoint X jets q F endpoint) π onto cokernel growth noRegular B u v hend hB flow

#print axioms terminal_hessian_flag_from_spatial_jets
end MinimizingSard.Five
