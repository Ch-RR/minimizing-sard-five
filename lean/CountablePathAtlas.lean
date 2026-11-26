import NativePathCalculus
import Mathlib.Analysis.InnerProductSpace.Dual

noncomputable section
open Set Filter MeasureTheory IsManifold TopologicalSpace
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
open Volterra

private theorem countable_of_functionals {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [Countable ι] (L : ι → H →L[ℝ] ℝ) (separates : ∀ u, (∀ i, L i u = 0) → u = 0) :
    SecondCountableTopology H := by
  let Y (i : ι) := (InnerProductSpace.toDual ℝ H).symm (L i)
  let K := Submodule.span ℝ (range Y)
  have orth : Kᗮ = ⊥ := by
    apply eq_bot_iff.mpr
    intro u hu
    apply separates u
    intro i
    have eq := (K.mem_orthogonal u).mp hu (Y i) (Submodule.subset_span (mem_range_self i))
    exact (InnerProductSpace.toDual_symm_apply (y := L i) (x := u)).symm.trans eq
  have top : K.topologicalClosure = ⊤ := by rw [← K.orthogonal_orthogonal_eq_closure,orth,Submodule.bot_orthogonal_eq_top]
  have sep : IsSeparable (K.topologicalClosure : Set H) :=
    (show IsSeparable (K : Set H) from (countable_range Y).isSeparable.span).closure
  rw [top,Submodule.top_coe] at sep
  letI := isSeparable_univ_iff.mp sep
  exact UniformSpace.secondCountable_of_separable H

private def primitiveMap (m : ℕ) : Control m →L[ℝ] C(Time,Fiber m) :=
  (Volterra.operator (Fiber m) (Fiber m) (ContinuousMap.const Time (ContinuousLinearMap.id ℝ (Fiber m)))).comp
    (frameSignal m).toContinuousLinearEquiv.toContinuousLinearMap

private theorem primitiveMap_spec {m : ℕ} (u : Control m) : TimePrimitive (primitiveMap m u) 0 (fun r => u r) := by
  let A := ContinuousMap.const Time (ContinuousLinearMap.id ℝ (Fiber m))
  refine ⟨?_,fun t => ?_⟩
  · simpa only [A,ContinuousMap.const_apply,ContinuousLinearMap.id_apply,frameSignal_apply] using
      Volterra.intervalIntegrable A (frameSignal m u)
  · change Volterra.operator (Fiber m) (Fiber m) A (frameSignal m u) t = _
    rw [operator_eq_interval]
    simp only [A,ContinuousMap.const_apply,ContinuousLinearMap.id_apply,frameSignal_apply,zero_add]

private theorem primitiveMap_inj (m : ℕ) : Function.Injective (primitiveMap m) := by
  intro u v h
  have p := primitiveMap_spec u
  rw [h] at p
  exact p.velocity_unique (primitiveMap_spec v)

private theorem countable_of_paths {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {m : ℕ} (J : H →L[ℝ] C(Time,Fiber m)) (inj : Function.Injective J) : SecondCountableTopology H := by
  obtain ⟨S,count,dense⟩ := exists_countable_dense Time
  letI : Countable S := count.to_subtype
  let L (i : S × Fin m) := (ContinuousLinearMap.proj i.2 : Fiber m →L[ℝ] ℝ).comp ((ContinuousMap.evalCLM ℝ i.1.val).comp J)
  apply countable_of_functionals L
  intro u hu
  apply inj
  rw [map_zero]
  have h : EqOn (J u) (fun _ => 0) S := fun t ht => funext (fun j => hu (⟨t,ht⟩,j))
  exact ContinuousMap.ext fun t => h.closure (J u).continuous continuous_const (dense t)

/-- Evaluation of the indefinite integral on a countable dense set of times
separates controls, so the Riesz representatives have dense span. -/
theorem pathModel_second_countable (m : ℕ) : SecondCountableTopology (PathModel m) :=
  countable_of_paths ((primitiveMap m).comp (modelControlEquiv m).toContinuousLinearMap)
    ((primitiveMap_inj m).comp (modelControlEquiv m).injective)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] [T2Space M] [IsManifold 𝓘(ℝ,State) ∞ M]
variable {m : ℕ} {Γ : Geometry M m} {x : M}

omit [IsManifold 𝓘(ℝ,State) ∞ M] in
private theorem in_source (A : ControlChart Γ x) (γ : HorizontalPaths Γ x)
    (src : ∀ i s, γ.val (A.partition.atTime i s) ∈ (A.frames i).chart.source) : γ ∈ A.chart.source := by
  let P := A.partition
  let e := A.frames
  have hl := γ.property.2.choose_spec
  have clock (i) (s : Time) : clamp (P.left i+P.duration i*s) = P.atTime i s := projIcc_of_mem _ (P.atTime i s).property
  choose p pos using fun i => hl.chart_sobolev (P.left i) (P.duration i) (P.cut_mem i.castSucc).1 (P.duration_pos i)
    ((P.end_eq i).symm ▸ (P.cut_mem i.succ).2) (e i).chart (e i).compatible (fun s => (clock i s).symm ▸ src i s)
  have atP (i s) : ambientPath (p i) s = (e i).chart (γ.val (P.atTime i s)) := by simpa only [clock] using pos i s
  obtain ⟨walk,rep⟩ := horizontal_in_requested_pieces hl P e A.member p src atP
  obtain ⟨v,codes⟩ := walk.has_codes
  exact ⟨A.split.symm v,p,(congrArg (fun a => SobolevJoins e p a γ.endpoint) γ.property.1).mp walk,rep,
    (A.split.apply_symm_apply _).symm ▸ codes⟩

theorem path_second_countable [SecondCountableTopology M] (Γ : Geometry M m) (x : M) : SecondCountableTopology (HorizontalPaths Γ x) := by
  classical
  cases isEmpty_or_nonempty (HorizontalPaths Γ x) with
  | inl empty => exact inferInstance
  | inr nonempty =>
    let base := nonempty.some
    have cover : (univ : Set M) ⊆ ⋃ e : Γ.frames, e.val.chart.source := by
      intro y _
      obtain ⟨e,he,hy⟩ := Γ.cover y
      exact mem_iUnion.mpr ⟨⟨e,he⟩,hy⟩
    obtain ⟨S,count,sub⟩ := isLindelof_univ.elim_countable_subcover (fun e : Γ.frames => e.val.chart.source)
      (fun e => e.val.chart.open_source) cover
    letI : Countable S := count.to_subtype
    have partitions (j : ℕ) : ∃ n, ∃ P : TimePartition (n+1), ∀ i, P.duration i < 1/((j:ℝ)+1) := by
      obtain ⟨n,P,mesh⟩ := fine_partition (show 0 < 1/((j:ℝ)+1) by positivity)
      cases n with
      | zero => have h := P.last; rw [show Fin.last 0 = 0 from rfl,P.first] at h; norm_num at h
      | succ n => exact ⟨n,P,mesh⟩
    choose n P mesh using partitions
    let Index := Σ j : ℕ, Fin (n j+1) → S
    let A (i : Index) : ControlChart Γ x := ⟨n i.1,P i.1,fun l => (i.2 l).val.val,fun l => (i.2 l).val.property,base⟩
    let a (i : Index) := (pathChartCore Γ x).openPartialHomeomorph (A i).chart (mem_range_self (A i))
    letI := pathModel_second_countable m
    letI (i : Index) : SecondCountableTopology (a i).source := (a i).secondCountableTopology_source
    apply secondCountableTopology_of_countable_cover (U := fun i => (a i).source) (fun i => (a i).open_source)
    apply eq_univ_of_forall
    intro γ
    let O (b : S) := γ.val ⁻¹' b.val.val.chart.source
    have cov : (univ : Set Time) ⊆ ⋃ b, O b := by
      intro t _
      obtain ⟨e,hit⟩ := mem_iUnion.mp (sub (mem_univ (γ.val t)))
      obtain ⟨he,hy⟩ := mem_iUnion.mp hit
      exact mem_iUnion.mpr ⟨⟨e,he⟩,hy⟩
    obtain ⟨δ,dp,balls⟩ := lebesgue_number_lemma_of_metric isCompact_univ
      (fun b : S => b.val.val.chart.open_source.preimage γ.val.continuous) cov
    obtain ⟨j,hj⟩ := exists_nat_one_div_lt dp
    choose e hit using fun i : Fin (n j+1) => balls (⟨(P j).left i,(P j).cut_mem i.castSucc⟩ : Time) (mem_univ _)
    apply mem_iUnion.mpr
    refine ⟨⟨j,e⟩,in_source (A ⟨j,e⟩) γ ?_⟩
    intro i s
    apply hit i
    have hi := (P j).atTime_mem i s
    change |(((P j).atTime i s : Time):ℝ)-(P j).left i| < δ
    rw [abs_of_nonneg (sub_nonneg.mpr hi.1)]
    exact (sub_le_sub_right hi.2 _).trans_lt ((mesh j i).trans hj)

def PathAtlas.countableBasis {Q : C(Time,M) → Prop} (A : PathAtlas Q m) : Prop :=
  @SecondCountableTopology (Subtype Q) A.topology

omit [ChartedSpace State M] [T2Space M] [IsManifold 𝓘(ℝ,State) ∞ M] in
private theorem countable_transport {Q R : C(Time,M) → Prop} (h : Q = R) (A : PathAtlas Q m) :
    (h ▸ A : PathAtlas R m).countableBasis ↔ A.countableBasis := by subst R; rfl

theorem intrinsic_path_second_countable [SecondCountableTopology M] {Δ : (y : M) → Submodule ℝ (Tangent y)}
    {g : (y : M) → Δ y → ℝ} (geometry : HasBundleCoordinates m Δ g) (hm : 0 < m) (x : M) :
    (intrinsicPathAtlas geometry hm x).countableBasis := by
  rw [intrinsicPathAtlas,countable_transport]
  exact path_second_countable _ _

#print axioms intrinsic_path_second_countable
#print axioms pathModel_second_countable
#print axioms path_second_countable
end MinimizingSard.Five
