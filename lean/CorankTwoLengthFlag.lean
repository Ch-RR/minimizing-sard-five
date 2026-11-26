import MinimizingLengthPolar

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
open Reduced

private abbrev Ordering := (Fin 3 ⊕ Fin 2) ≃ Fin 5

private def splitCoords (σ : Ordering) : State ≃L[ℝ] Ambient :=
  (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin 5 => ℝ) σ).symm.trans
    (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin 3) (Fin 2) (fun _ => ℝ))

private theorem ordering_of_pair (i j : Fin 5) (ne : i ≠ j) :
    ∃ σ : Ordering, σ (.inr 0) = i ∧ σ (.inr 1) = j := by
  let e : Ordering := finSumFinEquiv
  let t := e.trans (Equiv.swap (e (.inr 0)) i)
  have h0 : t (.inr 0) = i := by simp [t]
  have dif : i ≠ t (.inr 1) := h0 ▸ (t.injective.ne (by decide : (Sum.inr 0 : Fin 3 ⊕ Fin 2) ≠ .inr 1))
  exact ⟨t.trans (Equiv.swap (t (.inr 1)) j), by
    change Equiv.swap _ j (t _) = i
    rw [h0,Equiv.swap_apply_of_ne_of_ne dif ne], Equiv.swap_apply_left _ _⟩

private theorem regular_coordinate_split {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (D : U →L[ℝ] State) (π : State →L[ℝ] ℝ × ℝ) (sur : Function.Surjective π)
    (cok : LinearMap.ker π.toLinearMap = LinearMap.range D.toLinearMap) :
    ∃ σ : Ordering, Function.Surjective (fun v => (splitCoords σ (D v)).1) := by
  classical
  let e (i : Fin 5) : State := Pi.single i 1
  let a (i : Fin 5) := (π (e i)).1
  let b (i : Fin 5) := (π (e i)).2
  have decomp (z : State) : ∑ i, z i • e i = z := by
    ext j
    simp [e,Pi.single_apply]
  have coord (z : State) : (π z).1 = ∑ i, z i*a i ∧ (π z).2 = ∑ i, z i*b i := by
    have eq := congrArg π (decomp z)
    rw [map_sum] at eq
    exact ⟨by simpa [a] using congrArg Prod.fst eq.symm,by simpa [b] using congrArg Prod.snd eq.symm⟩
  have minor : ∃ i j, a i*b j ≠ b i*a j := by
    by_contra! flat
    obtain ⟨u,hu⟩ := sur (1,0)
    obtain ⟨v,hv⟩ := sur (0,1)
    have col (i) : a i*(π v).2 = b i*(π v).1 := by
      rw [(coord v).1,(coord v).2,Finset.mul_sum,Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by linear_combination v j * flat i j
    have az (i) : a i = 0 := by simpa [hv] using col i
    have one := (coord u).1
    simp [az,hu] at one
  obtain ⟨i,j,minor⟩ := minor
  have ij : i ≠ j := by rintro rfl; exact minor (mul_comm _ _)
  obtain ⟨σ,hi,hj⟩ := ordering_of_pair i j ij
  let τ := splitCoords σ
  have zero (k : Fin 2) : (τ (e (σ (.inr k)))).1 = 0 := by
    ext l
    change (Pi.single (σ (.inr k)) 1 : State) (σ (.inl l)) = 0
    simp
  have zi : (τ (e i)).1 = 0 := hi ▸ zero 0
  have zj : (τ (e j)).1 = 0 := hj ▸ zero 1
  let det := a i*b j-b i*a j
  have dn : det ≠ 0 := sub_ne_zero.mpr minor
  refine ⟨σ,fun y => ?_⟩
  let z := τ.symm (y,0)
  let r := ((π z).1*b j-(π z).2*a j)/det
  let s := (a i*(π z).2-b i*(π z).1)/det
  let corrected := z - (r • e i + s • e j)
  have cancel : π corrected = 0 := by
    apply Prod.ext
    · change (π corrected).1 = 0
      simp only [corrected,map_sub,map_add,map_smul,Prod.fst_sub,Prod.fst_add,Prod.smul_fst,smul_eq_mul]
      change (π z).1 - (r*a i+s*a j) = 0
      dsimp only [r,s]
      field_simp [dn]
      dsimp [det]
      ring
    · change (π corrected).2 = 0
      simp only [corrected,map_sub,map_add,map_smul,Prod.snd_sub,Prod.snd_add,Prod.smul_snd,smul_eq_mul]
      change (π z).2 - (r*b i+s*b j) = 0
      dsimp only [r,s]
      field_simp [dn]
      dsimp [det]
      ring
  obtain ⟨v,hv⟩ := (show corrected ∈ LinearMap.range D.toLinearMap from cok ▸ cancel)
  refine ⟨v,?_⟩
  change (τ (D.toLinearMap v)).1 = y
  rw [hv]
  simp [corrected,map_sub,map_add,map_smul,zi,zj,z]

/-- Any two distinct coordinate directions can be used, in the specified
order, as the vertical axes of a fixed three-plus-two splitting. -/
theorem split_coordinate_axes (i j : Fin 5) (ne : i ≠ j) :
    ∃ τ : State ≃L[ℝ] Ambient, τ (Pi.single i 1) = (0,![1,0]) ∧ τ (Pi.single j 1) = (0,![0,1]) := by
  obtain ⟨σ,hi,hj⟩ := ordering_of_pair i j ne
  subst i
  subst j
  refine ⟨splitCoords σ,?_,?_⟩ <;> apply Prod.ext
  · ext l
    change (Pi.single (σ (.inr 0)) 1 : State) (σ (.inl l)) = 0
    simp
  · ext l
    change (Pi.single (σ (.inr 0)) 1 : State) (σ (.inr l)) = ![1,0] l
    fin_cases l <;> simp
  · ext l
    change (Pi.single (σ (.inr 1)) 1 : State) (σ (.inl l)) = 0
    simp
  · ext l
    change (Pi.single (σ (.inr 1)) 1 : State) (σ (.inr l)) = ![0,1] l
    fin_cases l <;> simp

#print axioms split_coordinate_axes

/-- In the original state chart this conclusion needs no prescribed regular
minor, choice of quotient basis or auxiliary extension of the pointed value. -/
theorem ae_corank_two_length_flag {M : Type*} [TopologicalSpace M] [ChartedSpace State M]
    [IsManifold 𝓘(ℝ,State) ∞ M] (Γ : Geometry M 2) (x : M) (chart : OpenPartialHomeomorph M State)
    (hc : chart ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) :
    ∀ᵐ z : State, z ∈ continuityRegion (fun s => pointedLengthValue Γ x (chart.symm s)) →
      ∀ (n : ℕ) (e : Fin (n+1) → Frame M 2) (w : Fin (n+1) → Control 2)
      (y : M) (G : (Fin (n+1) → Control 2) → State),
      y ∈ chart.source → (∀ i, e i ∈ Γ.frames) → Joins e w x y →
      (∀ (k : ℕ) (d : Fin (k+1) → Frame M 2) (v : Fin (k+1) → Control 2),
        (∀ i, d i ∈ Γ.frames) → Joins d v x y → length w ≤ length v) →
      (∀ᶠ v in 𝓝 w, G v ∈ chart.target ∧ ∀ q, Joins e v x q ↔ q = chart.symm (G v)) →
      z = G w → ∀ π : State →L[ℝ] ℝ × ℝ, Function.Surjective π →
      LinearMap.ker π.toLinearMap = LinearMap.range (fderiv ℝ G w).toLinearMap →
      ¬ HasCostMultiplier length (fderiv ℝ G w) w →
      let K := LinearMap.ker (fderiv ℝ G w).toLinearMap
      let L := Submodule.span ℝ (range (fun u : K × K => π (fderiv ℝ (fderiv ℝ G) w u.1 u.2)))
      (∀ h : K, ¬ Function.Surjective (fun l : K => π (fderiv ℝ (fderiv ℝ G) w h l))) ∧
      (x ≠ y → ∀ i : Fin (n+1), w i ≠ 0 → (∀ j, i < j → w j = 0) →
        4 ≤ Module.finrank ℝ (wordLayer (e i).X ((e i).chart y) 3) →
        Module.finrank ℝ L = 1 ∧ chartThirdLayer (e i) chart y = L.comap π.toLinearMap ∧
          Module.finrank ℝ (chartThirdLayer (e i) chart y) = 4) := by
  classical
  filter_upwards [ae_all_iff.mpr (fun σ : Ordering => ae_chart_length_polar Γ x chart hc (splitCoords σ))] with z good
  intro localCont n e w y G hy he path hmin graph hz π sur cok absent
  obtain ⟨σ,onto⟩ := regular_coordinate_split _ π sur cok
  exact good σ localCont n e w y G hy he path hmin graph
    (congrArg (splitCoords σ) hz) onto π sur cok absent

#print axioms ae_corank_two_length_flag
end MinimizingSard.Five
