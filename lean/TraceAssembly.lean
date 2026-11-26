import HamiltonTrace

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] {m : ℕ}

def TraceReach (Γ : Geometry M m) (L : ℝ) (x y : CotPoint M) : Prop :=
  ∃ f : ℝ → CotPoint M, HamiltonTrace Γ L f ∧ f 0 = x ∧ f L = y

theorem TraceReach.zero (Γ : Geometry M m) (x : CotPoint M) : TraceReach Γ 0 x x := by
  refine ⟨fun _ => x,⟨continuousOn_const,fun _ _ _ _ _ => continuousWithinAt_const,?_⟩,rfl,rfl⟩
  intro e he t ht
  exact (ht.2.not_ge ht.1).elim

private theorem within_paste {E : Type*} [TopologicalSpace E] (h : ℝ → E) {a b t : ℝ}
    (pa : 0 ≤ a) (pb : 0 ≤ b)
    (left : t ∈ Icc 0 a → ContinuousWithinAt h (Icc 0 a) t)
    (right : t ∈ Icc a (a+b) → ContinuousWithinAt h (Icc a (a+b)) t) :
    ContinuousWithinAt h (Icc 0 (a+b)) t := by
  rw [← Icc_union_Icc_eq_Icc pa (le_add_of_nonneg_right pb)]
  apply ContinuousWithinAt.union
  · by_cases ht : t ∈ Icc 0 a
    · exact left ht
    · exact continuousWithinAt_of_notMem_closure (by rwa [isClosed_Icc.closure_eq])
  · by_cases ht : t ∈ Icc a (a+b)
    · exact right ht
    · exact continuousWithinAt_of_notMem_closure (by rwa [isClosed_Icc.closure_eq])

private theorem paste_observable {A E : Type*} [TopologicalSpace E] {H f g : ℝ → A} {a b : ℝ}
    (pa : 0 ≤ a) (pb : 0 ≤ b) (left : ∀ t ≤ a, H t = f t) (right : ∀ t ≥ a, H t = g (t-a))
    (P : A → E) (t : ℝ)
    (c1 : t ∈ Icc 0 a → ContinuousWithinAt (P ∘ f) (Icc 0 a) t)
    (c2 : t ∈ Icc a (a+b) → ContinuousWithinAt (P ∘ g) (Icc 0 b) (t-a)) :
    ContinuousWithinAt (P ∘ H) (Icc 0 (a+b)) t := by
  have shift : MapsTo (fun r : ℝ => r-a) (Icc a (a+b)) (Icc 0 b) :=
    fun r h => ⟨sub_nonneg.mpr h.1,by linarith only [h.2]⟩
  have cs : Continuous (fun r : ℝ => r-a) := continuous_id.sub continuous_const
  apply within_paste _ pa pb
  · intro ht
    exact (c1 ht).congr_of_mem (fun r hr => congrArg P (left r hr.2)) ht
  · intro ht
    have cr : ContinuousWithinAt ((P ∘ g) ∘ (fun r : ℝ => r-a)) (Icc a (a+b)) t :=
      (c2 ht).comp (f := fun r : ℝ => r-a) cs.continuousAt.continuousWithinAt shift
    exact cr.congr_of_mem
      (fun r hr => congrArg P (right r hr.1)) ht

/-- Concatenation uses only equality of the intrinsic base point and covector.
The two pieces may have arbitrarily different frames and zero duration. -/
theorem TraceReach.add (Γ : Geometry M m) {a b : ℝ} (pa : 0 ≤ a) (pb : 0 ≤ b)
    {x y z : CotPoint M} (one : TraceReach Γ a x y) (two : TraceReach Γ b y z) :
    TraceReach Γ (a+b) x z := by
  obtain ⟨f,hf,start,stop⟩ := one
  obtain ⟨g,hg,init,fin⟩ := two
  let H (t : ℝ) := if t < a then f t else g (t-a)
  have left (t : ℝ) (h : t ≤ a) : H t = f t := by
    rcases h.lt_or_eq with ht | rfl
    · simp only [H,if_pos ht]
    · simp [H,init,stop]
  have right (t : ℝ) (h : a ≤ t) : H t = g (t-a) := if_neg h.not_gt
  have shift : MapsTo (fun r : ℝ => r-a) (Icc a (a+b)) (Icc 0 b) :=
    fun r h => ⟨sub_nonneg.mpr h.1,by linarith only [h.2]⟩
  refine ⟨H,⟨?_,?_,?_⟩,(left 0 pa).trans start,?_⟩
  · intro t _
    exact paste_observable pa pb left right Prod.fst t (fun ht => hf.base t ht) (fun ht => hg.base _ (shift ht))
  · intro e he t ht hE
    exact paste_observable pa pb left right (phaseView e.chart) t
      (fun h => hf.coord e he t h ((left t h.2) ▸ hE))
      (fun h => hg.coord e he _ (shift h) ((right t h.1) ▸ hE))
  · intro e he t ht hE
    by_cases before : t < a
    · have eq := left t before.le
      have d := hf.ode e he t ⟨ht.1,before⟩ (eq ▸ hE)
      rw [eq]
      apply d.congr_of_eventuallyEq_of_mem _ (le_refl t)
      filter_upwards [Ico_mem_nhdsGE before] with r hr using congrArg (phaseView e.chart) (left r hr.2.le)
    · have afterCut := le_of_not_gt before
      have eq := right t afterCut
      have d := hg.ode e he (t-a) ⟨sub_nonneg.mpr afterCut,by linarith only [ht.2]⟩ (eq ▸ hE)
      have der := d.scomp t ((hasDerivAt_id t).sub_const a).hasDerivWithinAt
        (show MapsTo (fun s : ℝ => s-a) (Ici t) (Ici (t-a)) from fun _ h => sub_le_sub_right h a)
      rw [one_smul] at der
      rw [eq]
      apply der.congr_of_eventuallyEq_of_mem _ (le_refl t)
      filter_upwards [self_mem_nhdsWithin] with r hr using congrArg (phaseView e.chart) (right r (afterCut.trans hr))
  · simpa only [right _ (le_add_of_nonneg_right pb),add_sub_cancel_left] using fin

theorem TraceReach.chain (Γ : Geometry M m) {n : ℕ} (d : Fin n → ℝ) (pd : ∀ i, 0 ≤ d i)
    (q : Fin (n+1) → CotPoint M) (cells : ∀ i, TraceReach Γ (d i) (q i.castSucc) (q i.succ)) :
    TraceReach Γ (∑ i, d i) (q 0) (q (Fin.last n)) := by
  induction n with
  | zero => simpa using TraceReach.zero Γ (q 0)
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    have prev := ih (fun i => d i.castSucc) (fun i => pd i.castSucc) (fun j => q j.castSucc) (fun i => cells i.castSucc)
    exact TraceReach.add Γ (Finset.sum_nonneg fun i _ => pd i.castSucc) (pd _) prev (cells (Fin.last n))

#print axioms TraceReach.add
#print axioms TraceReach.chain
end MinimizingSard.Five
