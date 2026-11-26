import SupportedControlDensity
import EndpointComposition

noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace MinimizingSard.Five

section Chain
variable {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] {n : ℕ}



theorem chain_adjoint (H : Fin n → E × U → E) (s : E) (w : Fin n → U)
    (d : ∀ i, DifferentiableAt ℝ (H i) (chainNode H i.castSucc (s,w),w i))
    (η : E →L[ℝ] ℝ) :
    ∃ p : Fin (n+1) → E →L[ℝ] ℝ, p (Fin.last n) = η ∧
      (∀ i h, p i.castSucc h = p i.succ (fderiv ℝ (H i) (chainNode H i.castSucc (s,w),w i) (h,0))) ∧
      ∀ h v, η (fderiv ℝ (chainNode H (Fin.last n)) (s,w) (h,v)) =
        p 0 h + ∑ i, p i.succ (fderiv ℝ (H i) (chainNode H i.castSucc (s,w),w i) (0,v i)) := by
  let a := (s,w)
  let Z := chainNode H
  let A i := fderiv ℝ (H i) (Z i.castSucc a,w i)
  let p : Fin (n+1) → E →L[ℝ] ℝ := Fin.reverseInduction (motive := fun _ => E →L[ℝ] ℝ) η
    (fun i next => next.comp ((A i).comp (ContinuousLinearMap.inl ℝ E U)))
  have last : p (Fin.last n) = η := Fin.reverseInduction_last
  have prev (i : Fin n) (h : E) : p i.castSucc h = p i.succ (A i (h,0)) := by
    simp only [p,Fin.reverseInduction_castSucc,ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply]
  let B i := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => U) i).comp
    (ContinuousLinearMap.snd ℝ E (Fin n → U))
  have dz (j) : DifferentiableAt ℝ (Z j) a := by
    induction j using Fin.induction with
    | zero => exact differentiableAt_fst
    | succ i ih =>
      change DifferentiableAt ℝ (H i ∘ (fun b => (Z i.castSucc b,B i b))) a
      exact (d i).comp a (ih.prodMk (B i).differentiableAt)
  refine ⟨p,last,prev,?_⟩
  intro h v
  let g (j : Fin (n+1)) := p j (fderiv ℝ (Z j) a (h,v))
  have step (i : Fin n) : g i.succ-g i.castSucc = p i.succ (A i (0,v i)) := by
    have der := (d i).hasFDerivAt.comp a ((dz i.castSucc).hasFDerivAt.prodMk (B i).hasFDerivAt)
    have eq : fderiv ℝ (Z i.succ) a (h,v) = A i (fderiv ℝ (Z i.castSucc) a (h,v),v i) :=
      DFunLike.congr_fun der.fderiv (h,v)
    change p i.succ _-p i.castSucc _ = _
    rw [eq,prev]
    have split (b : E) (c : U) : A i (b,c) = A i (b,0)+A i (0,c) :=
      by simpa only [Prod.mk_add_mk,add_zero,zero_add] using (A i).map_add (b,0) (0,c)
    rw [split (fderiv ℝ (Z i.castSucc) a (h,v)) (v i),map_add,add_sub_cancel_left]
  have total : (∑ i : Fin n, (g i.succ-g i.castSucc)) = g (Fin.last n)-g 0 := by
    rw [Finset.sum_sub_distrib]
    linarith only [Fin.sum_univ_succ g,Fin.sum_univ_castSucc g]
  simp_rw [step] at total
  have first : g 0 = p 0 h := congrArg (p 0) (DFunLike.congr_fun (hasFDerivAt_fst (𝕜 := ℝ) (p := a)).fderiv (h,v))
  change η _ = p 0 h + _
  rw [← last,← first]
  exact (eq_add_of_sub_eq' total.symm)

#print axioms chain_adjoint
end Chain


/-- Pull an actual cost supporter of a fixed-source endpoint graph back through
all the intermediate charts. Each row supports arbitrary perturbations of its
own block, with both its incoming and outgoing endpoint covectors identified. -/
theorem supported_chain {M : Type*} [TopologicalSpace M] [ChartedSpace State M] {m n : ℕ}
    (e : Fin n → Frame M m) (c : Fin (n+1) → OpenPartialHomeomorph M State)
    (w : Fin n → Control m) (q : Fin (n+1) → M) (hq : ∀ j, q j ∈ (c j).source)
    (seg : ∀ i, Segment (e i) (w i) (q i.castSucc) (q i.succ))
    (H : Fin n → State × Control m → State)
    (sm : ∀ i, ContDiffAt ℝ 1 (H i) (c i.castSucc (q i.castSucc),w i))
    (graph : ∀ i, ∀ᶠ b in 𝓝 (c i.castSucc (q i.castSucc),w i),
      b.1 ∈ (c i.castSucc).target ∧ H i b ∈ (c i.succ).target ∧
      ∀ y, Segment (e i) b.2 ((c i.castSucc).symm b.1) y ↔ y = (c i.succ).symm (H i b))
    (G : (Fin n → Control m) → State)
    (globalGraph : ∀ᶠ v in 𝓝 w, G v ∈ (c (Fin.last n)).target ∧
      ∀ y, Joins e v (q 0) y ↔ y = (c (Fin.last n)).symm (G v))
    (η : State →L[ℝ] ℝ) (support : ∀ v, length w + η (fderiv ℝ G w (v-w)) ≤ length v) :
    ∃ p : Fin (n+1) → State →L[ℝ] ℝ, p (Fin.last n) = η ∧
      (∀ i h, p i.castSucc h = p i.succ (fderiv ℝ (H i) (c i.castSucc (q i.castSucc),w i) (h,0))) ∧
      (∀ h, η (fderiv ℝ (chainNode H (Fin.last n)) (c 0 (q 0),w) (h,0)) = p 0 h) ∧
      ∀ i v, pieceLength (w i) + p i.succ (fderiv ℝ (H i) (c i.castSucc (q i.castSucc),w i) (0,v-w i))
        ≤ pieceLength v := by
  obtain ⟨nodes,cs,gr⟩ := prescribed_composite_graph e c w q hq seg H sm graph
  let s := c 0 (q 0)
  let Z := chainNode H (Fin.last n)
  let I := fun v : Fin n → Control m => (s,v)
  have inc : HasFDerivAt I (ContinuousLinearMap.inr ℝ State (Fin n → Control m)) w :=
    (hasFDerivAt_const s w).prodMk (hasFDerivAt_id w)
  have same : G =ᶠ[𝓝 w] Z ∘ I := by
    filter_upwards [globalGraph,inc.continuousAt.tendsto gr] with v hv hf
    have path := (hv.2 _).mpr rfl
    rw [← (c 0).left_inv (hq 0)] at path
    have eq := (hf.2.2 _).mp path
    exact ((c (Fin.last n)).right_inv hv.1).symm.trans
      ((congrArg (c (Fin.last n)) eq).trans ((c (Fin.last n)).right_inv hf.2.1))
  have dz := (cs.differentiableAt (by decide)).hasFDerivAt.comp w inc
  have dg : ∀ h, fderiv ℝ G w h = fderiv ℝ Z (s,w) (0,h) :=
    fun h => DFunLike.congr_fun (dz.congr_of_eventuallyEq same).fderiv h
  have d i : DifferentiableAt ℝ (H i) (chainNode H i.castSucc (s,w),w i) := by
    rw [show chainNode H i.castSucc (s,w) = _ from nodes i.castSucc]
    exact (sm i).differentiableAt (by decide)
  obtain ⟨p,last,prev,allRows⟩ := chain_adjoint H s w d η
  have nodeEq (i : Fin n) : chainNode H i.castSucc (s,w) = c i.castSucc (q i.castSucc) := nodes i.castSucc
  simp_rw [nodeEq] at prev allRows
  refine ⟨p,last,prev,?_,?_⟩
  · intro h
    have zeroPair : ((0 : State),(0 : Control m)) = 0 := rfl
    simpa only [Pi.zero_apply,zeroPair,map_zero,Finset.sum_const_zero,add_zero] using allRows h 0
  intro j v
  have total (b : Fin n → Control m) : (∑ i, pieceLength (w i))+η (fderiv ℝ G w (b-w)) ≤ ∑ i, pieceLength (b i) := by
    simpa only [← length_pieces] using support b
  have cost := support_piece pieceLength w (fun h => η (fderiv ℝ G w h)) total j v
  change pieceLength (w j) + η (fderiv ℝ G w (Pi.single j (v-w j))) ≤ pieceLength v at cost
  rw [dg,allRows,map_zero,zero_add,Finset.sum_eq_single j] at cost
  · simpa using cost
  · intro i _ hij
    rw [Pi.single_eq_of_ne hij]
    rw [show ((0 : State),(0 : Control m)) = 0 from rfl,map_zero,map_zero]
  · simp

#print axioms supported_chain

end MinimizingSard.Five
