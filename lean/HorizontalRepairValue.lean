import PointedLengthValue
import QuarticReturn

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace MinimizingSard.Five

variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] {m : ℕ}
  {Γ : Geometry M m} {x y z : M}

private def segmentLength (u : Control m) : ℝ :=
  ∫ t in (0:ℝ)..1, Real.sqrt (speedSq (u t))

private theorem add_segment {a : ℝ} (ha : a ∈ attainableLengths Γ x y)
    {d : Frame M m} (hd : d ∈ Γ.frames) {v : Control m} (seg : Segment d v y z) :
    a + segmentLength v ∈ attainableLengths Γ x z := by
  obtain ⟨k,e,u,he,⟨q,qx,qy,parts⟩,rfl⟩ := ha
  refine ⟨k+1, Fin.snoc e d, Fin.snoc u v, ?_, ?_, ?_⟩
  · intro j
    exact Fin.lastCases (by simpa using hd) (fun i => by simpa using he i) j
  · let nodes : Fin (k+3) → M := Fin.snoc q z
    refine ⟨nodes,by simpa [nodes] using qx,by simp [nodes],?_⟩
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [nodes,Fin.succ_last,qy] using seg
    · simpa [nodes,← Fin.castSucc_succ] using parts j
  · unfold length
    rw [Fin.sum_univ_castSucc]
    simp [segmentLength]

/-- Concatenation preserves the sum of actual attained lengths with arbitrary frames. -/
theorem attainableLengths_add {a b : ℝ} (ha : a ∈ attainableLengths Γ x y)
    (hb : b ∈ attainableLengths Γ y z) : a+b ∈ attainableLengths Γ x z := by
  obtain ⟨k,d,v,hd,⟨q,qy,qz,parts⟩,rfl⟩ := hb
  have append (k : ℕ) (d : Fin k → Frame M m) (v : Fin k → Control m) (q : Fin (k+1) → M)
      (hd : ∀ i, d i ∈ Γ.frames) (qy : q 0 = y)
      (parts : ∀ i, Segment (d i) (v i) (q i.castSucc) (q i.succ)) :
      a+length v ∈ attainableLengths Γ x (q (Fin.last k)) := by
    induction k with
    | zero => simpa [length,qy] using ha
    | succ k ih =>
      have pre := ih (fun i => d i.castSucc) (fun i => v i.castSucc) (fun i => q i.castSucc)
        (fun i => hd _) qy (fun i => by simpa only [Fin.castSucc_succ] using parts i.castSucc)
      have step := add_segment pre (hd (Fin.last k)) (parts (Fin.last k))
      change a+(∑ i, segmentLength (v i)) ∈ _
      rw [Fin.sum_univ_castSucc,← add_assoc]
      exact step
  simpa only [qz] using append _ d v q hd qy parts

/-- The value inequality follows from concatenating competitors before taking
the infimum. It also holds when the first leg has no shortest path. -/
theorem pointedLengthValue_le_add_connector (reach : (attainableLengths Γ x y).Nonempty)
    {b : ℝ} (hb : b ∈ attainableLengths Γ y z) :
    pointedLengthValue Γ x z ≤ pointedLengthValue Γ x y + b := by
  apply sub_le_iff_le_add.mp
  apply le_csInf reach
  intro a ha
  obtain ⟨k,e,u,he,path,h⟩ := attainableLengths_add ha hb
  exact sub_le_iff_le_add.mpr ((pointedLengthValue_le he path).trans_eq h)

/-- This capped infimum is finite at every point, including outside the
source component. It agrees with the true value wherever a competitor costs less than N. -/
private def cappedValue (Γ : Geometry M m) (x : M) (N : ℝ) (y : M) :=
  sInf (insert N (attainableLengths Γ x y))

private theorem attained_bdd (Γ : Geometry M m) (x y : M) : BddBelow (attainableLengths Γ x y) := by
  refine ⟨0,?_⟩
  rintro _ ⟨k,e,v,_,_,rfl⟩
  exact control_length_nonneg v

private theorem capped_le (N : ℝ) (y : M) : cappedValue Γ x N y ≤ N :=
  csInf_le ((attained_bdd _ _ _).insert _) (mem_insert _ _)

private theorem capped_connector (N : ℝ) {b : ℝ} (hb : b ∈ attainableLengths Γ y z) :
    cappedValue Γ x N z ≤ cappedValue Γ x N y + b := by
  have nb : 0 ≤ b := by
    obtain ⟨k,e,v,_,_,rfl⟩ := hb
    exact control_length_nonneg v
  apply sub_le_iff_le_add.mp
  apply le_csInf (insert_nonempty N _)
  intro a ha
  apply sub_le_iff_le_add.mpr
  rcases mem_insert_iff.mp ha with rfl | mem
  · exact (capped_le _ _).trans (le_add_of_nonneg_right nb)
  · exact csInf_le ((attained_bdd _ _ _).insert _) (mem_insert_of_mem _ (attainableLengths_add mem hb))

private theorem actual_of_capped_lt {N : ℝ} (lt : cappedValue Γ x N y < N) :
    pointedLengthValue Γ x y = cappedValue Γ x N y := by
  have reach : (attainableLengths Γ x y).Nonempty := by
    by_contra! empty
    simp [cappedValue,empty] at lt
  have eq : cappedValue Γ x N y = min N (pointedLengthValue Γ x y) :=
    csInf_insert (attained_bdd _ _ _) reach
  rw [eq] at lt ⊢
  exact (min_eq_right (lt_of_not_ge (fun h => lt.ne (min_eq_left h))).le).symm

#print axioms attainableLengths_add
#print axioms pointedLengthValue_le_add_connector

private theorem continuousAt_of_pair_bound (C : State → ℝ) (q : State) (K : ℝ)
    (bound : ∀ᶠ p : State × State in 𝓝 (q,q), C p.2 ≤ C p.1 + K*‖p.2-p.1‖^(1/4:ℝ)) :
    ContinuousAt C q := by
  have up : Tendsto (fun z : State => (q,z)) (𝓝 q) (𝓝 (q,q)) :=
    tendsto_const_nhds.prodMk_nhds tendsto_id
  have dn : Tendsto (fun z : State => (z,q)) (𝓝 q) (𝓝 (q,q)) :=
    tendsto_id.prodMk_nhds tendsto_const_nhds
  have fcont : Continuous (fun z : State => K*‖z-q‖^(1/4:ℝ)) :=
    continuous_const.mul ((Real.continuous_rpow_const (by norm_num : 0 ≤ (1/4:ℝ))).comp
      (continuous_id.sub continuous_const).norm)
  have small : Tendsto (fun z : State => K*‖z-q‖^(1/4:ℝ)) (𝓝 q) (𝓝 0) := by
    simpa [Real.zero_rpow (by norm_num : (1/4:ℝ) ≠ 0)] using fcont.tendsto q
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) _ small
  filter_upwards [up bound,dn bound] with z ub lb
  change C z ≤ C q + K*‖z-q‖^(1/4:ℝ) at ub
  change C q ≤ C z + K*‖q-z‖^(1/4:ℝ) at lb
  rw [norm_sub_rev] at lb
  rw [Real.dist_eq,abs_le]
  constructor <;> linarith

/-- Actual short connectors with a full-rank signed displacement jet give
two-point fourth-root control and continuity of the original pointed value.
Reachability is required only at the center. -/
theorem pointedLengthValue_holder_of_horizontal_motions
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    (chart : OpenPartialHomeomorph M State) (q : State)
    (reach : (attainableLengths Γ x (chart.symm q)).Nonempty)
    (A : State × P → State) (basis : P ≃L[ℝ] State)
    (zero : ∀ᶠ z in 𝓝 q, A (z,0) = 0)
    (jet : HasStrictFDerivAt A ((basis : P →L[ℝ] State).comp (ContinuousLinearMap.snd ℝ State P)) (q,0))
    {L : ℝ} (hL : 0 ≤ L)
    (motion : ∀ᶠ p : State × P in 𝓝 (q,0), ∃ b ∈
      attainableLengths Γ (chart.symm p.1) (chart.symm (p.1+A p)), b ≤ L*‖p.2‖^(1/4:ℝ)) :
    let D := fun z => pointedLengthValue Γ x (chart.symm z)
    (∃ U : Set State, IsOpen U ∧ q ∈ U ∧ ContinuousOn D U) ∧
      ∃ K : ℝ, ∀ᶠ p : State × State in 𝓝 (q,q),
      D p.2 ≤ D p.1 + K*‖p.2-p.1‖^(1/4:ℝ) := by
  obtain ⟨l,hl⟩ := reach
  let N := l+1
  let C (z : State) := cappedValue Γ x N (chart.symm z)
  have gap : C q < N := (csInf_le ((attained_bdd _ _ _).insert N) (mem_insert_of_mem N hl)).trans_lt
    (by dsimp [N]; linarith)
  obtain ⟨K,bound⟩ := Return.holder_of_signed_motions q A basis zero jet C hL (by
    filter_upwards [motion] with p ⟨b,hb,le⟩
    exact (capped_connector N hb).trans (add_le_add_left le _))
  have cc := continuousAt_of_pair_bound C q K bound
  have eq : (fun z => pointedLengthValue Γ x (chart.symm z)) =ᶠ[𝓝 q] C :=
    (cc.eventually_lt_const gap).mono (fun z h => actual_of_capped_lt h)
  let D := fun z => pointedLengthValue Γ x (chart.symm z)
  have estimate : ∀ᶠ p : State × State in 𝓝 (q,q), D p.2 ≤ D p.1 + K*‖p.2-p.1‖^(1/4:ℝ) := by
    filter_upwards [bound,continuous_fst.continuousAt.tendsto eq,continuous_snd.continuousAt.tendsto eq]
      with p hb h₁ h₂
    change D p.1 = C p.1 at h₁
    change D p.2 = C p.2 at h₂
    simpa only [h₁,h₂] using hb
  have nearby : ∀ᶠ z in 𝓝 q, ContinuousAt D z := by
    have diag : Tendsto (fun z : State => (z,z)) (𝓝 q) (𝓝 (q,q)) := tendsto_id.prodMk_nhds tendsto_id
    filter_upwards [diag estimate.eventually_nhds] with z hz using continuousAt_of_pair_bound D z K hz
  obtain ⟨U,allc,op,mem⟩ := eventually_nhds_iff.mp nearby
  exact ⟨⟨U,op,mem,fun z hz => (allc z hz).continuousWithinAt⟩,K,estimate⟩

#print axioms pointedLengthValue_holder_of_horizontal_motions
end MinimizingSard.Five
