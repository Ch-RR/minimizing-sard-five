import ActiveTerminalSegment
import FiveDimensionalThirdLayer

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five

variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M]

/-- The third bracket-word layer expressed in the chosen endpoint chart. -/
def chartThirdLayer (f : Frame M 2) (c : OpenPartialHomeomorph M State) (y : M) : Submodule ℝ State :=
  (wordLayer f.X (f.chart y) 3).map (fderiv ℝ (c ∘ f.chart.symm) (f.chart y)).toLinearMap

private theorem layer_dimension [IsManifold 𝓘(ℝ,State) ∞ M] (f : Frame M 2) (c : OpenPartialHomeomorph M State)
    (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (y : M) (hy : y ∈ c.source) (hf : y ∈ f.chart.source) :
    Module.finrank ℝ (chartThirdLayer f c y) = Module.finrank ℝ (wordLayer f.X (f.chart y) 3) := by
  obtain ⟨T,eq⟩ := ContinuousLinearMap.IsInvertible.of_inverse
    (transition_left c f.chart hc f.compatible y hy hf) (transition_left f.chart c f.compatible hc y hf hy)
  unfold chartThirdLayer
  rw [← eq]
  exact T.toLinearEquiv.finrank_map_eq _

private theorem vanishes_on_layer (f : Frame M 2) (c : OpenPartialHomeomorph M State)
    (p : State →L[ℝ] ℝ) (y : M) (ann : AnnihilatesThirdFlag f c p y) :
    chartThirdLayer f c y ≤ LinearMap.ker p.toLinearMap := by
  change (wordLayer f.X (f.chart y) 3).map _ ≤ _
  apply Submodule.map_le_iff_le_comap.mpr
  rw [← frame_third_layer_eq_words]
  apply Submodule.span_le.mpr
  rintro v ((⟨i,rfl⟩ | h) | ⟨i,rfl⟩)
  · exact ann.1 i
  · obtain rfl := Set.mem_singleton_iff.mp h
    exact ann.2.1
  · exact ann.2.2 i

private theorem active_unique {n : ℕ} (w : Fin n → Control 2) {i j : Fin n}
    (mi : w i ≠ 0) (ti : ∀ k, i < k → w k = 0) (mj : w j ≠ 0) (tj : ∀ k, j < k → w k = 0) : j = i :=
  le_antisymm (le_of_not_gt fun h => mj (ti j h)) (le_of_not_gt fun h => mi (tj i h))

set_option maxHeartbeats 600000 in
private theorem active_source [IsManifold 𝓘(ℝ,State) ∞ M] {n : ℕ}
    (e : Fin (n+1) → Frame M 2) (w : Fin (n+1) → Control 2) {x y : M} (distinct : x ≠ y)
    (path : Joins e w x y) (c : OpenPartialHomeomorph M State)
    (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (hy : y ∈ c.source)
    (G : (Fin (n+1) → Control 2) → State)
    (graph : ∀ᶠ b in 𝓝 w, G b ∈ c.target ∧ ∀ z, Joins e b x z ↔ z = c.symm (G b))
    (i : Fin (n+1)) (moving : w i ≠ 0) (last : ∀ j, i < j → w j = 0) : y ∈ (e i).chart.source := by
  have zero : kernelRowAt G w (0 : State →L[ℝ] ℝ) = 0 := by ext h l; rfl
  have rz : FiniteDimensional ℝ (LinearMap.range (kernelRowAt G w (0 : State →L[ℝ] ℝ))) := by
    rw [zero,LinearMap.range_zero]; infer_instance
  obtain ⟨j,mj,tj,inside,_⟩ := whole_third_flag_at_distinct_endpoint x y distinct c hc hy 0 n e w path G graph
    (fun _ => rfl) rz
  exact active_unique w moving last mj tj ▸ inside

set_option maxHeartbeats 800000 in
/-- The two-component polar calculation for the original full endpoint,
its actual kernel, and the third bracket-word layer of the last active
frame. The geometric growth and polar hypotheses remain explicit. -/
theorem whole_hessian_flag [IsManifold 𝓘(ℝ,State) ∞ M] {n : ℕ}
    (e : Fin (n+1) → Frame M 2) (w : Fin (n+1) → Control 2) {x y : M} (distinct : x ≠ y)
    (path : Joins e w x y) (c : OpenPartialHomeomorph M State)
    (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (hy : y ∈ c.source)
    (G : (Fin (n+1) → Control 2) → State)
    (graph : ∀ᶠ b in 𝓝 w, G b ∈ c.target ∧ ∀ z, Joins e b x z ↔ z = c.symm (G b))
    (i : Fin (n+1)) (moving : w i ≠ 0) (last : ∀ j, i < j → w j = 0)
    (π : State →L[ℝ] ℝ × ℝ) (onto : Function.Surjective π)
    (cokernel : LinearMap.ker π.toLinearMap = LinearMap.range (fderiv ℝ G w).toLinearMap)
    (growth : 4 ≤ Module.finrank ℝ (wordLayer (e i).X ((e i).chart y) 3))
    (noRegular : ∀ h : LinearMap.ker (fderiv ℝ G w).toLinearMap,
      ¬ Function.Surjective (fun l : LinearMap.ker (fderiv ℝ G w).toLinearMap =>
        π (fderiv ℝ (fderiv ℝ G) w h l))) :
    let K := LinearMap.ker (fderiv ℝ G w).toLinearMap
    let L := Submodule.span ℝ (range (fun z : K × K => π (fderiv ℝ (fderiv ℝ G) w z.1 z.2)))
    Module.finrank ℝ L = 1 ∧ chartThirdLayer (e i) c y = L.comap π.toLinearMap ∧
      Module.finrank ℝ (chartThirdLayer (e i) c y) = 4 ∧
      ¬ (FiniteDimensional ℝ (LinearMap.range (kernelRowAt G w ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp π))) ∧
        FiniteDimensional ℝ (LinearMap.range (kernelRowAt G w ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp π)))) := by
  let K := LinearMap.ker (fderiv ℝ G w).toLinearMap
  let p₁ := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp π
  let p₂ := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp π
  let A := kernelRowAt G w p₁
  let B := kernelRowAt G w p₂
  have hi := active_source e w distinct path c hc hy G graph i moving last
  have dimension := layer_dimension (e i) c hc y hy hi
  have finiteRow (a b : ℝ) (hf : FiniteDimensional ℝ (LinearMap.range (a • A + b • B))) :
      ∀ z ∈ chartThirdLayer (e i) c y, a * (π z).1 + b * (π z).2 = 0 := by
    let p := a • p₁ + b • p₂
    have add : kernelRowAt G w p = a • A + b • B := by
      apply LinearMap.ext
      intro h
      apply LinearMap.ext
      intro l
      rfl
    have rank : FiniteDimensional ℝ (LinearMap.range (kernelRowAt G w p)) := add.symm ▸ hf
    have ann (h) : p (fderiv ℝ G w h) = 0 := by
      have hz : π (fderiv ℝ G w h) = 0 := by
        change fderiv ℝ G w h ∈ LinearMap.ker π.toLinearMap
        rw [cokernel]; exact ⟨h,rfl⟩
      change a * (π (fderiv ℝ G w h)).1 + b * (π (fderiv ℝ G w h)).2 = 0
      simp [hz]
    obtain ⟨j,mj,tail,_,kills⟩ := whole_third_flag_at_distinct_endpoint x y distinct c hc hy p n e w path G graph ann rank
    have same := active_unique w moving last mj tail
    subst j
    exact fun z hz => vanishes_on_layer _ _ p _ kills hz
  have sym := (endpoint_representative_smooth e w path c hc hy G graph).isSymmSndFDerivAt (by simp)
  exact Hessian.five_dimensional_hessian_flag A B (T := State) (Module.finrank_fin_fun ℝ) π.toLinearMap onto
    (chartThirdLayer (e i) c y) (dimension.symm ▸ growth) (fun h l => congrArg p₁ (sym h.val l.val))
    (fun h l => congrArg p₂ (sym h.val l.val)) noRegular finiteRow

#print axioms whole_hessian_flag
end MinimizingSard.Five
