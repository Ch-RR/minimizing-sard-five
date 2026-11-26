import GlobalSobolevCurves

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
open Volterra
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] {m n : ℕ}

def TimePartition.uniform (n : ℕ) : TimePartition (n+1) where
  cut i := (i.val:ℝ)/(n+1:ℕ)
  first := by simp
  last := by change ((n+1:ℕ):ℝ)/((n+1:ℕ):ℝ) = 1; exact div_self (by positivity)
  increasing := fun i j h => div_lt_div_of_pos_right (by exact_mod_cast h) (by positivity)

def PathHasLength (Γ : Geometry M m) (γ : C(Time,M)) (l : ℝ) : Prop :=
  ∃ (n : ℕ) (P : TimePartition (n+1)) (e : Fin (n+1) → Frame M m) (p : Fin (n+1) → SobolevData),
    (∀ i, e i ∈ Γ.frames) ∧ SobolevJoins e p (γ (clamp 0)) (γ (clamp 1)) ∧
    RepresentsPath P e p γ ∧ sobolevLength e p = l

/-- One differentiable family of horizontal paths on the original
unit interval. The chart sequence and time partition can be chosen
independently for each family. -/
def HorizontalVariation (Γ : Geometry M m) (x : M) (F : ℝ → C(Time,M)) : Prop :=
  ∃ (n : ℕ) (P : TimePartition (n+1)) (e : Fin (n+1) → Frame M m) (Z : ℝ → Fin (n+1) → SobolevData),
    (∀ i, e i ∈ Γ.frames) ∧ DifferentiableAt ℝ Z 0 ∧
    ∀ᶠ t in 𝓝 0, F t (clamp 0) = x ∧ SobolevJoins e (Z t) x (F t (clamp 1)) ∧
      RepresentsPath P e (Z t) (F t)

def CurveSingular (Γ : Geometry M m) (x : M) (γ : C(Time,M)) : Prop :=
  ∃ c : OpenPartialHomeomorph M State, c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M ∧ γ (clamp 1) ∈ c.source ∧
    ∃ η : State →L[ℝ] ℝ, η ≠ 0 ∧ ∀ F : ℝ → C(Time,M), F 0 = γ → HorizontalVariation Γ x F →
      DifferentiableAt ℝ (fun t => c (F t (clamp 1))) 0 → η (deriv (fun t => c (F t (clamp 1))) 0) = 0

theorem CurveSingular.in_presentation {Γ : Geometry M m} {x : M} {γ : C(Time,M)}
    {P : TimePartition (n+1)} {e : Fin (n+1) → Frame M m} {p : Fin (n+1) → SobolevData}
    (h : CurveSingular Γ x γ) (he : ∀ i, e i ∈ Γ.frames) (base : RepresentsPath P e p γ) :
    SobolevSingular e p x (γ (clamp 1)) := by
  classical
  obtain ⟨c,hc,cy,η,nz,test⟩ := h
  refine ⟨c,hc,cy,η,nz,?_⟩
  intro Z f z0 f0 dz df graph
  let A (t : ℝ) := ∃ ξ : C(Time,M), ξ (clamp 0) = x ∧ ξ (clamp 1) = c.symm (f t) ∧ RepresentsPath P e (Z t) ξ
  let F (t : ℝ) : C(Time,M) := if h : A t then h.choose else γ
  have has : ∀ᶠ t in 𝓝 0, A t := graph.mono (fun t ht => ht.2.realize P)
  have good : ∀ᶠ t in 𝓝 0, F t (clamp 0) = x ∧ F t (clamp 1) = c.symm (f t) ∧ RepresentsPath P e (Z t) (F t) := by
    filter_upwards [has] with t ht
    simpa only [F,dif_pos ht] using ht.choose_spec
  have center : F 0 = γ := (z0 ▸ good.self_of_nhds.2.2).unique base
  have variation : HorizontalVariation Γ x F := by
    refine ⟨n,P,e,Z,he,dz,?_⟩
    filter_upwards [good,graph] with t ht hg
    exact ⟨ht.1,ht.2.1.symm ▸ hg.2,ht.2.2⟩
  have same : (fun t => c (F t (clamp 1))) =ᶠ[𝓝 0] f := by
    filter_upwards [good,graph] with t ht hg
    exact (congrArg c ht.2.1).trans (c.right_inv hg.1)
  rw [← same.deriv_eq]
  exact test F center variation (df.congr_of_eventuallyEq same)

def curveMinEndpoints (Γ : Geometry M m) (x : M) : Set M :=
  {y | ∃ (γ : C(Time,M)) (l : ℝ), γ (clamp 0) = x ∧ γ (clamp 1) = y ∧ PathHasLength Γ γ l ∧
    CurveSingular Γ x γ ∧ ∀ (ξ : C(Time,M)) (d : ℝ), ξ (clamp 0) = x → ξ (clamp 1) = y →
      PathHasLength Γ ξ d → l ≤ d}

theorem curveMinEndpoints_subset (Γ : Geometry M m) (x : M) :
    curveMinEndpoints Γ x ⊆ sobolevMinEndpoints Γ x := by
  rintro y ⟨γ,l,src,dst,⟨n,P,e,p,he,path,rep,len⟩,sing,minimal⟩
  refine ⟨n,e,p,he,src ▸ dst ▸ path,dst ▸ sing.in_presentation he rep,?_⟩
  intro k d z hd walk
  obtain ⟨ξ,a,b,r⟩ := walk.realize (TimePartition.uniform k)
  rw [len]
  exact minimal ξ _ a b ⟨k,_,d,z,hd,a.symm ▸ b.symm ▸ walk,r,rfl⟩

theorem five_dimensional_curve_sard [T2Space M] [SecondCountableTopology M] [ConnectedSpace M]
    [IsManifold 𝓘(ℝ,State) ∞ M] (m : ℕ) (hm : 0 < m) (h5 : m < 5) (Γ : Geometry M m) (x : M)
    (c : OpenPartialHomeomorph M State) (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) :
    volume (c '' (c.source ∩ curveMinEndpoints Γ x)) = 0 :=
  measure_mono_null (image_mono (inter_subset_inter_right _ (curveMinEndpoints_subset Γ x)))
    (five_dimensional_sobolev_sard m hm h5 Γ x c hc)

#print axioms CurveSingular.in_presentation
#print axioms curveMinEndpoints_subset
#print axioms five_dimensional_curve_sard
end MinimizingSard.Five
