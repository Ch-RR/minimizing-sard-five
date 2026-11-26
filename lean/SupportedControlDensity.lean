import NormalLengthDensity
import L2Volterra

noncomputable section
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace
namespace MinimizingSard.Five

abbrev controlMeasure := volume.restrict (Icc (0:ℝ) 1)
abbrev EuclideanControl (m : ℕ) := Lp (EuclideanSpace ℝ (Fin m)) 2 controlMeasure

def euclideanControl (m : ℕ) : Control m →L[ℝ] EuclideanControl m :=
  (EuclideanSpace.equiv (Fin m) ℝ).symm.toContinuousLinearMap.compLpL 2 controlMeasure

def coordinateControl (m : ℕ) : EuclideanControl m →L[ℝ] Control m :=
  (EuclideanSpace.equiv (Fin m) ℝ).toContinuousLinearMap.compLpL 2 controlMeasure

private theorem coordinate_cancel {m : ℕ} (w : Control m) : coordinateControl m (euclideanControl m w) = w := by
  let T := EuclideanSpace.equiv (Fin m) ℝ
  apply Lp.ext
  filter_upwards [T.toContinuousLinearMap.coeFn_compLp (euclideanControl m w), T.symm.toContinuousLinearMap.coeFn_compLp w] with t h₁ h₂
  exact h₁.trans ((congrArg T h₂).trans (T.apply_symm_apply _))

private theorem euclidean_cancel {m : ℕ} (w : EuclideanControl m) : euclideanControl m (coordinateControl m w) = w := by
  let T := EuclideanSpace.equiv (Fin m) ℝ
  apply Lp.ext
  filter_upwards [T.symm.toContinuousLinearMap.coeFn_compLp (coordinateControl m w), T.toContinuousLinearMap.coeFn_compLp w] with t h₁ h₂
  exact h₁.trans ((congrArg T.symm h₂).trans (T.symm_apply_apply _))

def pieceLength {m : ℕ} (v : Control m) := ∫ t, ‖euclideanControl m v t‖ ∂controlMeasure

theorem length_pieces {m n : ℕ} (w : Fin n → Control m) : length w = ∑ i, pieceLength (w i) := by
  unfold length
  apply Finset.sum_congr rfl
  intro i _
  rw [intervalIntegral.integral_of_le zero_le_one,Measure.restrict_congr_set Ioc_ae_eq_Icc]
  apply integral_congr_ae
  let T := (EuclideanSpace.equiv (Fin m) ℝ).symm.toContinuousLinearMap
  filter_upwards [T.coeFn_compLp (w i)] with t ht
  change Real.sqrt (speedSq _) = ‖T.compLp (w i) t‖
  rw [ht,EuclideanSpace.norm_eq]
  simp only [speedSq,Real.norm_eq_abs,sq_abs]
  rfl

theorem support_piece {E : Type*} [AddCommGroup E] {n : ℕ}
    (φ : E → ℝ) (w : Fin n → E) (B : (Fin n → E) → ℝ)
    (all : ∀ v : Fin n → E, (∑ i, φ (w i))+B (v-w) ≤ ∑ i, φ (v i)) (j : Fin n) (v : E) :
    φ (w j) + B (Pi.single j (v-w j)) ≤ φ v := by
  let d := Function.update w j v
  have delta : d-w = Pi.single j (v-w j) := by
    funext i
    by_cases h : i = j
    · subst i; simp [d]
    · simp [d,h]
  have cost := all d
  rw [delta,← Finset.sum_erase_add _ (fun i => φ (w i)) (Finset.mem_univ j),
    ← Finset.sum_erase_add _ (fun i => φ (d i)) (Finset.mem_univ j)] at cost
  have eq : (∑ i ∈ Finset.univ.erase j, φ (d i)) =
      ∑ i ∈ Finset.univ.erase j, φ (w i) := Finset.sum_congr rfl fun i hi =>
    congrArg φ (Function.update_of_ne (Finset.ne_of_mem_erase hi) _ _)
  rw [eq,show d j = v from Function.update_self ..] at cost
  linarith only [cost]

private def singleFunctional {m n : ℕ} (A : (Fin n → Control m) →L[ℝ] State)
    (η : State →L[ℝ] ℝ) (j : Fin n) : EuclideanControl m →L[ℝ] ℝ :=
  ((η.comp A).comp (ContinuousLinearMap.single ℝ (fun _ : Fin n => Control m) j)).comp (coordinateControl m)

private theorem single_support {m n : ℕ} (w : Fin n → Control m)
    (A : (Fin n → Control m) →L[ℝ] State) (η : State →L[ℝ] ℝ)
    (support : ∀ v, length w+η (A (v-w)) ≤ length v) (j : Fin n) (v : EuclideanControl m) :
    pieceLength (w j) + singleFunctional A η j (v-euclideanControl m (w j)) ≤ ∫ t, ‖v t‖ ∂controlMeasure := by
  have totals (b : Fin n → Control m) : (∑ i, pieceLength (w i))+η (A (b-w)) ≤ ∑ i, pieceLength (b i) := by
    rw [← length_pieces,← length_pieces]
    exact support b
  have h := support_piece pieceLength w (fun b => η (A b)) totals j (coordinateControl m v)
  change pieceLength (w j)+η (A (Pi.single j (coordinateControl m (v-euclideanControl m (w j))))) ≤ _
  rw [map_sub,coordinate_cancel]
  change pieceLength (w j)+η (A (Pi.single j (coordinateControl m v-w j))) ≤ _
  exact h.trans_eq (by simp only [pieceLength,euclidean_cancel])

private theorem density_on_piece {m n : ℕ} (w : Fin n → Control m)
    (A : (Fin n → Control m) →L[ℝ] State) (η : State →L[ℝ] ℝ)
    (support : ∀ v, length w+η (A (v-w)) ≤ length v) (j : Fin n) :
    ∃ a : EuclideanControl m, (∀ v : Control m, η (A (Pi.single j v)) =
      ∫ t, ⟪a t,euclideanControl m v t⟫_ℝ ∂controlMeasure) ∧
      ∀ᵐ t ∂controlMeasure, ‖a t‖ ≤ 1 ∧ euclideanControl m (w j) t = ‖euclideanControl m (w j) t‖ • a t := by
  haveI : IsProbabilityMeasure controlMeasure := ⟨by simp [controlMeasure]⟩
  obtain ⟨a,rep,aligned⟩ := norming_control_density (euclideanControl m (w j)) (singleFunctional A η j)
    (single_support w A η support j)
  refine ⟨a,?_,aligned⟩
  intro v
  have h := rep (euclideanControl m v)
  change η (A (Pi.single j (coordinateControl m (euclideanControl m v)))) = _ at h
  rwa [coordinate_cancel] at h

/-- Every supporting covector of the actual finite-piece endpoint produces
a unique integral functional on each piece; its density calibrates speed
on that same piece, including idle sets. -/
theorem supported_endpoint_density {m n : ℕ} (w : Fin n → Control m)
    (A : (Fin n → Control m) →L[ℝ] State) (η : State →L[ℝ] ℝ)
    (support : ∀ v, length w+η (A (v-w)) ≤ length v) :
    ∃ a : Fin n → EuclideanControl m, (∀ i (v : Control m),
        η (A (Pi.single i v)) = ∫ t, ⟪a i t,euclideanControl m v t⟫_ℝ ∂controlMeasure) ∧
      ∀ i, ∀ᵐ t ∂controlMeasure, ‖a i t‖ ≤ 1 ∧
        euclideanControl m (w i) t = ‖euclideanControl m (w i) t‖ • a i t := by
  choose a rep aligned using density_on_piece w A η support
  exact ⟨a,rep,aligned⟩

#print axioms supported_endpoint_density

/-- A continuous coefficient representing the supporting linear functional
is determined almost everywhere and aligns the original control. -/
theorem explicit_support_alignment {m : ℕ} (u : Control m) (B : Control m →L[ℝ] ℝ)
    (b : C(Volterra.Time,Fiber m)) (sup : ∀ v, pieceLength u + B (v-u) ≤ pieceLength v)
    (functional : ∀ v, B v = ∫ t in (0:ℝ)..1, ∑ i, v t i*b (Volterra.clamp t) i) :
    ∀ᵐ t ∂controlMeasure, u t = Real.sqrt (speedSq (u t)) • b (Volterra.clamp t) := by
  haveI : IsProbabilityMeasure controlMeasure := ⟨by simp [controlMeasure]⟩
  let H := EuclideanSpace ℝ (Fin m)
  let T := EuclideanSpace.equiv (Fin m) ℝ
  let Z := euclideanControl m u
  let row := B.comp (coordinateControl m)
  have test (v : EuclideanControl m) :
      (∫ t, ‖Z t‖ ∂controlMeasure)+row (v-Z) ≤ ∫ t, ‖v t‖ ∂controlMeasure := by
    have h := sup (coordinateControl m v)
    change pieceLength u+B (coordinateControl m (v-Z)) ≤ _
    rw [map_sub,show coordinateControl m Z = u from coordinate_cancel _]
    exact h.trans_eq (by simp only [pieceLength,euclidean_cancel])
  obtain ⟨a,rep,cal⟩ := norming_control_density Z row test
  let f : C(Volterra.Time,H) := ⟨fun t => T.symm (b t),T.symm.continuous.comp b.continuous⟩
  have mem : MemLp (fun t : ℝ => f (Volterra.clamp t)) 2 controlMeasure :=
    MemLp.of_bound (f.continuous.comp continuous_projIcc).aestronglyMeasurable ‖f‖
      (.of_forall fun t => f.norm_coe_le_norm _)
  let v := mem.toLp _
  have eq : a = v := by
    apply ext_inner_right ℝ
    intro h
    change (∫ t, ⟪a t,h t⟫_ℝ ∂controlMeasure) = ∫ t, ⟪v t,h t⟫_ℝ ∂controlMeasure
    rw [← rep h,show row h = B (coordinateControl m h) from rfl,functional,
      intervalIntegral.integral_of_le zero_le_one,Measure.restrict_congr_set Ioc_ae_eq_Icc]
    apply integral_congr_ae
    filter_upwards [mem.coeFn_toLp,T.toContinuousLinearMap.coeFn_compLp h] with t vt ht
    change (∑ i, T.toContinuousLinearMap.compLp h t i*b (Volterra.clamp t) i) = ⟪v t,h t⟫_ℝ
    rw [show v t = f (Volterra.clamp t) from vt,ht,PiLp.inner_apply]
    rfl
  filter_upwards [cal,mem.coeFn_toLp,T.symm.toContinuousLinearMap.coeFn_compLp u] with t ht vt ut
  have h := ht.2
  rw [eq,show v t = f (Volterra.clamp t) from vt] at h
  have actual : Z t = T.symm (u t) := ut
  have size : ‖Z t‖ = Real.sqrt (speedSq (u t)) := by
    rw [actual,EuclideanSpace.norm_eq]
    simp only [Real.norm_eq_abs,sq_abs,speedSq]
    rfl
  rw [size,actual] at h
  simpa only [map_smul,T.apply_symm_apply,f,ContinuousMap.coe_mk] using congrArg T h

#print axioms explicit_support_alignment


theorem original_speed_integrable {m : ℕ} (u : Control m) :
    IntervalIntegrable (fun t => Real.sqrt (speedSq (u t))) volume 0 1 := by
  haveI : IsProbabilityMeasure controlMeasure := ⟨by simp [controlMeasure]⟩
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  change Integrable _ (volume.restrict (Ioc (0:ℝ) 1))
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]
  apply ((Lp.memLp (euclideanControl m u)).integrable (by norm_num)).norm.congr
  let T := (EuclideanSpace.equiv (Fin m) ℝ).symm.toContinuousLinearMap
  filter_upwards [T.coeFn_compLp u] with t ht
  change ‖T.compLp u t‖ = Real.sqrt (speedSq (u t))
  rw [ht,EuclideanSpace.norm_eq]
  simp only [Real.norm_eq_abs,sq_abs,speedSq]
  rfl

#print axioms original_speed_integrable

end MinimizingSard.Five
