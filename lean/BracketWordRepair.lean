import SignedRootMotion
import HorizontalRepairValue
import ReversedFramePaths

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace MinimizingSard.Five
open MinimizingSard.Return
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] {m : ℕ}
  (Γ : Geometry M m) (chart : OpenPartialHomeomorph M State) (q : State)

/-- Local data of an unsigned word and its inverse. Length bounds refer to
competitors for the original segment equations. -/
structure RepairWord where
  order : ℕ
  positive : 0 < order
  atMostFour : order ≤ 4
  forward : State × ℝ → State
  backward : State × ℝ → State
  profile : State × ℝ → State
  smoothProfile : ContDiffAt ℝ 1 profile (q,0)
  smoothBackward : ContDiffAt ℝ 1 backward (q,0)
  backwardZero : backward (q,0) = q
  expansion : ∀ᶠ p in 𝓝 (q,(0:ℝ)), forward p = p.1 + p.2^order • profile p
  undo : ∀ᶠ p in 𝓝 (q,(0:ℝ)), forward (backward p,p.2) = p.1
  cost : ℝ
  nonneg : 0 ≤ cost
  paths : ∀ᶠ p in 𝓝 (q,(0:ℝ)), 0 ≤ p.2 →
    ∃ b ∈ attainableLengths Γ (chart.symm p.1) (chart.symm (forward p)), b ≤ cost*p.2

variable {Γ chart q}
private abbrev RepairWord.move (W : RepairWord Γ chart q) := rootEndpoint W.forward W.backward W.order

private theorem backward_paths (W : RepairWord Γ chart q) :
    ∀ᶠ p in 𝓝 (q,(0:ℝ)), 0 ≤ p.2 →
      ∃ b ∈ attainableLengths Γ (chart.symm p.1) (chart.symm (W.backward p)), b ≤ W.cost*p.2 := by
  have toB : Tendsto (fun p : State × ℝ => (W.backward p,p.2)) (𝓝 (q,0)) (𝓝 (q,0)) := by
    simpa only [W.backwardZero] using W.smoothBackward.continuousAt.tendsto.prodMk_nhds
      (continuous_snd.continuousAt (x := (q,(0:ℝ)))).tendsto
  filter_upwards [toB W.paths,W.undo] with p path undo
  intro pos
  obtain ⟨b,hb,bd⟩ := path pos
  change b ∈ attainableLengths Γ (chart.symm (W.backward p)) (chart.symm (W.forward (W.backward p,p.2))) at hb
  rw [undo,attainableLengths_reverse Γ] at hb
  exact ⟨b,hb,bd⟩

private theorem signed_cost_order (W : RepairWord Γ chart q) {d : ℕ} (hd : W.order ≤ d) :
    ∀ᶠ p : State × ℝ in 𝓝 (q,0), ∃ b ∈ attainableLengths Γ (chart.symm p.1) (chart.symm (W.move p)),
      b ≤ W.cost*|p.2|^(1/(d:ℝ)) := by
  let a := (W.order:ℝ)⁻¹
  have kp : (0:ℝ) < W.order := by exact_mod_cast W.positive
  have ha : 0 < a := inv_pos.mpr kp
  have lower : (1/(d:ℝ)) ≤ a := by
    change 1/(d:ℝ) ≤ (W.order:ℝ)⁻¹
    rw [← one_div]
    exact one_div_le_one_div_of_le kp (by exact_mod_cast hd)
  let T (p : State × ℝ) := (p.1, |p.2|^a)
  have tc : Continuous T := continuous_fst.prodMk ((Real.continuous_rpow_const ha.le).comp continuous_snd.abs)
  have tend : Tendsto T (𝓝 (q,0)) (𝓝 (q,0)) := by simpa [T,Real.zero_rpow ha.ne'] using tc.tendsto (q,0)
  have small : ∀ᶠ p : State × ℝ in 𝓝 (q,0), |p.2| < 1 :=
    continuous_snd.abs.continuousAt.eventually_lt_const (by simp)
  filter_upwards [tend W.paths,tend (backward_paths W),small] with p forward backward lt
  have pos := Real.rpow_nonneg (abs_nonneg p.2) a
  have powers : |p.2|^a ≤ |p.2|^(1/(d:ℝ)) := by
    rcases (abs_nonneg p.2).eq_or_lt with h | h
    · rw [← h,Real.zero_rpow ha.ne']; exact Real.rpow_nonneg (by norm_num) _
    · exact Real.rpow_le_rpow_of_exponent_ge h lt.le lower
  have le := mul_le_mul_of_nonneg_left powers W.nonneg
  by_cases h : 0 ≤ p.2
  · obtain ⟨b,hb,bd⟩ := forward pos
    exact ⟨b,by simpa [RepairWord.move,rootEndpoint,h,T,a] using hb,bd.trans le⟩
  · obtain ⟨b,hb,bd⟩ := backward pos
    exact ⟨b,by simpa [RepairWord.move,rootEndpoint,h,T,a] using hb,bd.trans le⟩

private theorem word_at_zero (W : RepairWord Γ chart q) :
    ∀ᶠ z in 𝓝 q, W.move (z,0) = z := by
  have kp : (0:ℝ) < W.order := by exact_mod_cast W.positive
  have to0 : Tendsto (fun z : State => (z,(0:ℝ))) (𝓝 q) (𝓝 (q,0)) := tendsto_id.prodMk_nhds tendsto_const_nhds
  filter_upwards [to0 W.expansion] with z h
  simpa [RepairWord.move,rootEndpoint,Real.zero_rpow (inv_pos.mpr kp).ne',W.positive.ne'] using h

/-- Signed motions realized by original controls retain the largest order of the selected basis. -/
theorem word_motion_of_order (W : Fin 5 → RepairWord Γ chart q)
    {d : ℕ} (hd : ∀ i, (W i).order ≤ d)
    (basis : State ≃L[ℝ] State)
    (cols : ∀ s : State, ∑ i, s i • (W i).profile (q,0) = basis s)
    : ∃ A : State × State → State, (∀ᶠ z in 𝓝 q, A (z,0) = 0) ∧
      HasStrictFDerivAt A (basis.toContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ State State)) (q,0) ∧
      ∀ᶠ p : State × State in 𝓝 (q,0), ∃ b ∈ attainableLengths Γ (chart.symm p.1) (chart.symm (p.1+A p)),
        b ≤ (∑ i, (W i).cost)*‖p.2‖^(1/(d:ℝ)) := by
  let fst := ContinuousLinearMap.fst ℝ State State
  let snd := ContinuousLinearMap.snd ℝ State State
  let coord (i : Fin 5) := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 5 => ℝ) i).comp snd
  let col (i : Fin 5) := (coord i).smulRight ((W i).profile (q,0))
  have build (I : Finset (Fin 5)) : ∃ F : State × State → State,
      (∀ᶠ z in 𝓝 q, F (z,0) = z) ∧
      HasStrictFDerivAt F (fst + ∑ i ∈ I, col i) (q,0) ∧
      ∀ᶠ p in 𝓝 (q,(0:State)), ∃ b ∈ attainableLengths Γ (chart.symm p.1) (chart.symm (F p)),
        b ≤ (∑ i ∈ I, (W i).cost)*‖p.2‖^(1/(d:ℝ)) := by
    induction I using Finset.induction_on with
    | empty =>
      refine ⟨Prod.fst,Eventually.of_forall fun _ => rfl, by simpa [fst] using
        (hasStrictFDerivAt_fst (𝕜 := ℝ) (p := (q,(0:State)))),?_⟩
      have tz : Tendsto (fun p : State × State => (p.1,(0:ℝ))) (𝓝 (q,0)) (𝓝 (q,0)) :=
        continuous_fst.continuousAt.tendsto.prodMk_nhds tendsto_const_nhds
      filter_upwards [tz (signed_cost_order (W 0) (hd 0)), continuous_fst.continuousAt.tendsto (word_at_zero (W 0))]
        with p h zero
      obtain ⟨b,path,bd⟩ := h
      have dp : 0 < (d:ℝ) := by exact_mod_cast ((W 0).positive.trans_le (hd 0))
      exact ⟨b,zero ▸ path,by simpa [Real.zero_rpow (inv_pos.mpr dp).ne'] using bd⟩
    | insert i I hi ih =>
      obtain ⟨F,zF,dF,cF⟩ := ih
      let T (p : State × State) := (F p,coord i p)
      have dt := dF.prodMk ((coord i).hasStrictFDerivAt (x := (q,(0:State))))
      have tz : T (q,0) = (q,0) := Prod.ext zF.self_of_nhds rfl
      have tend : Tendsto T (𝓝 (q,0)) (𝓝 (q,0)) := by simpa only [tz] using
        (show ContinuousAt T (q,0) from dt.continuousAt).tendsto
      let w := W i
      have dw := inverse_word_root_jet w.forward w.backward w.profile q w.positive w.smoothProfile
        w.smoothBackward w.backwardZero w.expansion w.undo
      refine ⟨w.move ∘ T, ?_, ?_, ?_⟩
      · filter_upwards [zF,word_at_zero w] with z h k
        change w.move (F (z,0),0) = z
        rwa [h]
      · have du : HasStrictFDerivAt w.move
            (ContinuousLinearMap.fst ℝ State ℝ + (ContinuousLinearMap.snd ℝ State ℝ).smulRight (w.profile (q,0))) (T (q,0)) := by
          rw [tz]
          exact dw
        have dh := du.comp (q,0) dt
        have maps : (fst + ∑ j ∈ insert i I, col j) =
            (ContinuousLinearMap.fst ℝ State ℝ + (ContinuousLinearMap.snd ℝ State ℝ).smulRight (w.profile (q,0))).comp
              ((fst + ∑ j ∈ I, col j).prod (coord i)) := by
          apply ContinuousLinearMap.ext
          intro p
          simp [Finset.sum_insert,hi,col,w,add_comm,add_assoc]
        rw [maps]
        exact dh
      · filter_upwards [cF,tend (signed_cost_order w (hd i))] with p hf hw
        obtain ⟨b,first,bd⟩ := hf
        obtain ⟨c,second,cd⟩ := hw
        refine ⟨b+c,attainableLengths_add first second,?_⟩
        have le := Real.rpow_le_rpow (abs_nonneg (p.2 i)) (norm_le_pi_norm p.2 i) (by positivity : 0 ≤ (1/(d:ℝ)))
        change c ≤ w.cost*|p.2 i|^(1/(d:ℝ)) at cd
        rw [Finset.sum_insert hi,add_mul,add_comm ((W i).cost*_)]
        exact add_le_add bd (cd.trans (mul_le_mul_of_nonneg_left le w.nonneg))
  obtain ⟨F,zero,der,cost⟩ := build Finset.univ
  let A (p : State × State) := F p - p.1
  refine ⟨A,?_,?_,?_⟩
  · filter_upwards [zero] with z hz using sub_eq_zero.mpr hz
  · have maps : basis.toContinuousLinearMap.comp snd = (fst + ∑ i, col i) - fst := by
      apply ContinuousLinearMap.ext
      intro p
      simpa [fst,snd,col,coord,ContinuousLinearMap.sum_apply] using (cols p.2).symm
    rw [show ContinuousLinearMap.snd ℝ State State = snd from rfl,maps]
    exact der.sub (hasStrictFDerivAt_fst (𝕜 := ℝ) (p := (q,(0:State))))
  · simpa [A,add_sub_cancel] using cost

#print axioms word_motion_of_order

/-- Compose the words before taking the inverse in the two-point repair estimate.
Both the full parameter derivative and the cost of the composite are derived. -/
theorem pointed_value_repair_of_words (W : Fin 5 → RepairWord Γ chart q)
    (basis : State ≃L[ℝ] State)
    (cols : ∀ s : State, ∑ i, s i • (W i).profile (q,0) = basis s)
    (x : M) (reach : (attainableLengths Γ x (chart.symm q)).Nonempty) :
    let D := fun z => pointedLengthValue Γ x (chart.symm z)
    (∃ U : Set State, IsOpen U ∧ q ∈ U ∧ ContinuousOn D U) ∧
    ∃ K : ℝ, ∀ᶠ p : State × State in 𝓝 (q,q), D p.2 ≤ D p.1 + K*‖p.2-p.1‖^(1/4:ℝ) := by
  obtain ⟨A,z,d,cost⟩ := word_motion_of_order W (d := 4) (fun i => (W i).atMostFour) basis cols
  exact pointedLengthValue_holder_of_horizontal_motions chart q reach A basis z d
    (Finset.sum_nonneg fun i _ => (W i).nonneg) cost

#print axioms pointed_value_repair_of_words
end MinimizingSard.Five
