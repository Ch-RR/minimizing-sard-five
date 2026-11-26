import FrameBracketInduction
import Mathlib.Analysis.Analytic.Uniqueness

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace MinimizingSard.Five
variable {m n : ℕ}
private abbrev U (n m : ℕ) := Fin n → Control m

/-- A nonzero analytic test on the endpoint derivative kernel is nonzero at
some strictly length-shortening direction. Only the test requires analyticity. -/
theorem shortening_with_test (A : U n m →L[ℝ] State) (w : U n m)
    (absent : ¬ HasCostMultiplier length A w)
    (P : LinearMap.ker A.toLinearMap → ℝ) (analytic : AnalyticOnNhd ℝ P univ)
    (nonzero : ∃ v, P v ≠ 0) :
    ∃ h : LinearMap.ker A.toLinearMap, length (w+h.val) < length w ∧ P h ≠ 0 := by
  obtain ⟨k,hk,down⟩ := (no_length_multiplier_iff_shorter A w).mp absent
  let d : LinearMap.ker A.toLinearMap := ⟨k,hk⟩
  have shorter : ∀ᶠ h : LinearMap.ker A.toLinearMap in 𝓝 d, length (w+h.val) < length w :=
    (continuous_control_length.comp (continuous_const.add continuous_subtype_val)).continuousAt.eventually_lt_const down
  by_contra! fail
  have vanish : P =ᶠ[𝓝 d] (fun _ => (0:ℝ)) := shorter.mono fun h lt => fail h lt
  have allzero := analytic.eq_of_eventuallyEq analyticOnNhd_const vanish
  obtain ⟨v,hv⟩ := nonzero
  exact hv (congrFun allzero v)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem quadratic_row (f : E → ℝ) (hf : ContDiffAt ℝ 2 f 0) (h : E) :
    fderiv ℝ (Return.coeff f 2 0) h = fderiv ℝ (fderiv ℝ f) 0 h := by
  let A := fderiv ℝ (fderiv ℝ f) 0
  have sym := hf.isSymmSndFDerivAt (by simp)
  have eq : Return.coeff f 2 0 = fun v => (1/2:ℝ) * A v v := by
    funext v
    simp only [Return.coeff,iteratedFDeriv_two_apply,show Nat.factorial 2 = 2 from rfl,Nat.cast_ofNat,A]
    ring
  have df := (((A.hasFDerivAt).clm_apply (hasFDerivAt_id h)).const_mul (1/2:ℝ)).fderiv
  simp only [id_eq] at df
  rw [eq,df]
  ext v
  change (1/2:ℝ)*(A h v+A v h) = A h v
  rw [show A v h = A h v from sym v h]
  ring

theorem shortening_with_quadratic_row (A : U n m →L[ℝ] State) (w : U n m)
    (absent : ¬ HasCostMultiplier length A w) (f : LinearMap.ker A.toLinearMap → ℝ)
    (hf : ContDiffAt ℝ 2 f 0) (rank : fderiv ℝ (fderiv ℝ f) 0 ≠ 0) :
    ∃ h : LinearMap.ker A.toLinearMap, length (w+h.val) < length w ∧ fderiv ℝ (Return.coeff f 2 0) h ≠ 0 := by
  let Q := fderiv ℝ (fderiv ℝ f) 0
  obtain ⟨v,b,pos⟩ : ∃ v b, Q v b ≠ 0 := by
    by_contra! all
    exact rank (ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun b => all v b)
  let L := (ContinuousLinearMap.apply ℝ ℝ b).comp Q
  obtain ⟨h,down,test⟩ := shortening_with_test A w absent L L.contDiff.analyticOnNhd ⟨v,pos⟩
  refine ⟨h,down,?_⟩
  rw [quadratic_row f hf]
  intro van
  exact test (DFunLike.congr_fun van b)

private theorem polar_analytic (f : E → ℝ) (k : ℕ) (b : E) :
    ContDiff ℝ ω (fun h => Return.polarRow f k h b) := by
  let diag : E →L[ℝ] Fin k → E := ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℝ E
  let T := iteratedFDeriv ℝ k (fderiv ℝ f) 0
  let ev := ContinuousLinearMap.apply ℝ ℝ b
  change ContDiff ℝ ω (fun h => (k.factorial:ℝ)⁻¹ * ev (T (diag h)))
  exact contDiff_const.mul (ev.contDiff.comp (T.contDiff.comp diag.contDiff))

theorem shortening_with_cubic_minor (A : U n m →L[ℝ] State) (w : U n m)
    (absent : ¬ HasCostMultiplier length A w) (f g : LinearMap.ker A.toLinearMap → ℝ)
    (a b v : LinearMap.ker A.toLinearMap)
    (rank : Return.polarRow f 1 v a * Return.polarRow g 2 v b ≠ Return.polarRow f 1 v b * Return.polarRow g 2 v a) :
    ∃ h : LinearMap.ker A.toLinearMap, length (w+h.val) < length w ∧
      Return.polarRow f 1 h a * Return.polarRow g 2 h b ≠ Return.polarRow f 1 h b * Return.polarRow g 2 h a := by
  let P (h : LinearMap.ker A.toLinearMap) := Return.polarRow f 1 h a * Return.polarRow g 2 h b -
    Return.polarRow f 1 h b * Return.polarRow g 2 h a
  have poly : ContDiff ℝ ω P := ((polar_analytic f 1 a).mul (polar_analytic g 2 b)).sub
    ((polar_analytic f 1 b).mul (polar_analytic g 2 a))
  obtain ⟨h,down,good⟩ := shortening_with_test A w absent P poly.analyticOnNhd ⟨v,sub_ne_zero.mpr rank⟩
  exact ⟨h,down,sub_ne_zero.mp good⟩

#print axioms shortening_with_test
#print axioms shortening_with_quadratic_row
#print axioms shortening_with_cubic_minor

/-- Apply the selection to the kernel of the derivative of the actual endpoint
graph. No regular shortening direction is input to the quartic alternative. -/
abbrev QuarticKernelBoxes {M : Type*} [TopologicalSpace M] [ChartedSpace State M] (Γ : Geometry M 2) (chart : OpenPartialHomeomorph M State) : Prop :=
    ∀ᵐ q : State, q ∈ chart.target → ∀ {N : ℕ} (d : Fin (N+1) → Frame M 2)
      (w : Fin (N+1) → Control 2) (x : M) (G : (Fin (N+1) → Control 2) → State),
      (∀ i, d i ∈ Γ.frames) → Joins d w x (chart.symm q) →
      (∀ (k : ℕ) (r : Fin (k+1) → Frame M 2) (v : Fin (k+1) → Control 2),
        (∀ i, r i ∈ Γ.frames) → Joins r v x (chart.symm q) → length w ≤ length v) →
      (∀ᶠ v in 𝓝 w, ∀ y, Joins d v x y ↔ y = chart.symm (G v)) →
      ¬ HasCostMultiplier length (fderiv ℝ G w) w →
      let K := LinearMap.ker (fderiv ℝ G w).toLinearMap
      ∀ (S : K → (Fin (N+1) → Control 2)) (f g : K → ℝ) (u v : State),
      S 0 = 0 → HasFDerivAt S K.subtypeL 0 →
      (∀ᶠ z in 𝓝 0, G (w+S z) = q+f z • u+g z • v) →
      ContDiffAt ℝ 2 f 0 → ContDiffAt ℝ 4 g 0 →
      (∀ j ≤ 1, ∀ b : K, iteratedFDeriv ℝ j f 0 (fun _ => b) = 0) →
      (∀ j ≤ 3, ∀ b : K, iteratedFDeriv ℝ j g 0 (fun _ => b) = 0) →
      fderiv ℝ (fderiv ℝ f) 0 ≠ 0 →
      ∃ a₀ b₀ c : ℝ, 0 < c ∧ ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ → ∀ a b : ℝ,
        |a-a₀| < δ → |b-b₀| < δ →
        pointedLengthValue Γ x (chart.symm (q+(t^2*a) • u+(t^4*b) • v)) ≤
          pointedLengthValue Γ x (chart.symm q)-c*t

theorem quartic_kernel_boxes_of_repair {M : Type*} [TopologicalSpace M] [ChartedSpace State M] (Γ : Geometry M 2) (chart : OpenPartialHomeomorph M State)
    (repair : ChartValueRepair Γ chart) : QuarticKernelBoxes Γ chart := by
  filter_upwards [quartic_boxes_of_repair Γ chart repair] with q box
  intro hq N d w x G hd hw minimal graph absent K S f g u v s0 ds ends cf cg ff gg rank
  obtain ⟨h,down,regular⟩ := shortening_with_quadratic_row _ w absent f cf rank
  have push : Tendsto (fun z => w+S z) (𝓝 0) (𝓝 w) := by
    simpa only [s0,add_zero] using (continuousAt_const.add ds.continuousAt).tendsto
  have joins : ∀ᶠ z in 𝓝 0, Joins d (w+S z) x (chart.symm (q+f z • u+g z • v)) := by
    filter_upwards [push graph,ends] with z hz eq
    exact (hz _).mpr (congrArg chart.symm eq.symm)
  exact ⟨_,_,box hq d w x hd hw minimal S _ h s0 ds down f g u v cf cg ff gg regular joins⟩

theorem ae_quartic_box_of_kernel_data {M : Type*} [TopologicalSpace M] [ChartedSpace State M]
    (Γ : Geometry M 2) (e : Frame M 2) (he : e ∈ Γ.frames) : QuarticKernelBoxes Γ e.chart :=
  quartic_kernel_boxes_of_repair Γ e.chart (ae_frame_value_repair e he)

#print axioms ae_quartic_box_of_kernel_data

set_option maxHeartbeats 1200000 in
/-- The cubic and quartic alternatives for the actual length use the same
endpoint kernel and reduced chart, including when some speeds vanish. -/
abbrev MixedKernelBoxes {M : Type*} [TopologicalSpace M] [ChartedSpace State M] (Γ : Geometry M 2) (chart : OpenPartialHomeomorph M State) : Prop :=
    ∀ᵐ q : State, q ∈ chart.target → ∀ {N : ℕ} (d : Fin (N+1) → Frame M 2)
      (w : Fin (N+1) → Control 2) (x : M) (G : (Fin (N+1) → Control 2) → State),
      (∀ i, d i ∈ Γ.frames) → Joins d w x (chart.symm q) →
      (∀ (k : ℕ) (r : Fin (k+1) → Frame M 2) (v : Fin (k+1) → Control 2),
        (∀ i, r i ∈ Γ.frames) → Joins r v x (chart.symm q) → length w ≤ length v) →
      (∀ᶠ v in 𝓝 w, ∀ y, Joins d v x y ↔ y = chart.symm (G v)) →
      ¬ HasCostMultiplier length (fderiv ℝ G w) w →
      let K := LinearMap.ker (fderiv ℝ G w).toLinearMap
      ∀ (S : K → (Fin (N+1) → Control 2)) (f g : K → ℝ) (u v : State),
      S 0 = 0 → HasFDerivAt S K.subtypeL 0 →
      (∀ᶠ z in 𝓝 0, G (w+S z) = q+f z • u+g z • v) →
      ContDiffAt ℝ 2 f 0 → ContDiffAt ℝ 4 g 0 →
      f 0 = 0 → fderiv ℝ f 0 = 0 → g 0 = 0 → fderiv ℝ g 0 = 0 → fderiv ℝ (fderiv ℝ g) 0 = 0 →
      (∃ i j a b, Return.polarRow f 1 i a * Return.polarRow f 1 j b ≠
                   Return.polarRow f 1 i b * Return.polarRow f 1 j a) →
      ∃ k : ℕ, (k = 3 ∨ k = 4) ∧ ∃ a₀ b₀ c : ℝ, 0 < c ∧ ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ → ∀ a b : ℝ,
        |a-a₀| < δ → |b-b₀| < δ →
        pointedLengthValue Γ x (chart.symm (q+(t^2*a) • u+(t^k*b) • v)) ≤
          pointedLengthValue Γ x (chart.symm q)-c*t

set_option maxHeartbeats 1200000 in
theorem mixed_kernel_boxes_of_repair {M : Type*} [TopologicalSpace M] [ChartedSpace State M] (Γ : Geometry M 2) (chart : OpenPartialHomeomorph M State)
    (repair : ChartValueRepair Γ chart) : MixedKernelBoxes Γ chart := by
  filter_upwards [quartic_kernel_boxes_of_repair Γ chart repair] with q quartic
  intro hq N d w x G hd hw minimal graph absent K S f g u v s0 ds ends cf cg f0 f1 g0 g1 g2 rank
  have cg₃ : ContDiffAt ℝ 3 g 0 := cg.of_le (by decide)
  by_cases reg : ∃ i a b, Return.polarRow f 1 i a * Return.polarRow g 2 i b ≠
      Return.polarRow f 1 i b * Return.polarRow g 2 i a
  · obtain ⟨i,a,b,minor⟩ := reg
    obtain ⟨h,down,rh⟩ := shortening_with_cubic_minor _ w absent f g a b i minor
    let V (p : ℝ × ℝ) := pointedLengthValue Γ x (chart.symm (q+p.1 • u+p.2 • v))
    have val : V 0 = length w := by simpa [V] using pointedLengthValue_eq hd hw minimal
    have push : Tendsto (fun z => w+S z) (𝓝 0) (𝓝 w) := by
      simpa only [s0,add_zero] using (continuousAt_const.add ds.continuousAt).tendsto
    have cand : ∀ᶠ z in 𝓝 0, V (f z,g z) ≤ length (w+S z) := by
      filter_upwards [push graph,ends] with z hz eq
      exact pointedLengthValue_le hd ((hz _).mpr (congrArg chart.symm eq.symm))
    have save (B : (ℝ × ℝ) →L[ℝ] K) : ∃ c > 0, ∀ᶠ p : ℝ × (ℝ × ℝ) in 𝓝 0, 0 < p.1 →
        V (f (p.1 • (h+B p.2)),g (p.1 • (h+B p.2))) ≤ V 0-c*p.1 := by
      obtain ⟨c,hc,cone⟩ := length_cone_on_level_chart w S K.subtypeL s0 ds h down B
      let Z (p : ℝ × (ℝ × ℝ)) := p.1 • (h+B p.2)
      have cz : Continuous Z := continuous_fst.smul (continuous_const.add (B.continuous.comp continuous_snd))
      have lim : Tendsto Z (𝓝 0) (𝓝 0) := by simpa [Z] using cz.tendsto 0
      refine ⟨c,hc,?_⟩
      filter_upwards [lim cand,cone] with p hc hs
      intro ht
      rw [val]
      exact le_trans hc (hs ht)
    obtain ⟨c,hc,δ,hδ,box⟩ := Return.cubic_box_of_regular_cone f g V h a b cf cg₃ f0 f1 g0 g1 g2 rh save
    refine ⟨3,Or.inl rfl,Return.coeff f 2 0 h,Return.coeff g 3 0 h,c,hc,δ,hδ,?_⟩
    simpa [V] using box
  · push_neg at reg
    have flat := Return.third_jet_zero_of_dependent_rows f g cf cg₃ rank reg
    refine ⟨4,Or.inr rfl,quartic hq d w x G hd hw minimal graph absent S f g u v s0 ds ends cf cg ?_ ?_ ?_⟩
    · intro j hj v
      interval_cases j <;> simp [f0,f1]
    · intro j hj v
      interval_cases j
      · simpa using g0
      · simp [g1]
      · rw [iteratedFDeriv_two_apply,g2]; rfl
      · exact flat v
    · intro vanish
      obtain ⟨i,j,a,b,ne⟩ := rank
      apply ne
      simp [Return.polarRow,vanish]
      rfl

theorem ae_descent_box_of_kernel_jets {M : Type*} [TopologicalSpace M] [ChartedSpace State M]
    (Γ : Geometry M 2) (e : Frame M 2) (he : e ∈ Γ.frames) : MixedKernelBoxes Γ e.chart :=
  mixed_kernel_boxes_of_repair Γ e.chart (ae_frame_value_repair e he)

#print axioms ae_descent_box_of_kernel_jets
end MinimizingSard.Five
