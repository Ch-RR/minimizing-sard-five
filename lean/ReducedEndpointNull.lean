import MixedOrderBox
import SparseClock

/-! From actual reduced derivatives to ambient outer nullity in fixed
product coordinates. The modeling assumptions refer to individual witnesses. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace MinimizingSard.Reduced

abbrev Plane := Fin 2 → ℝ
abbrev Ambient := (Fin 3 → ℝ) × Plane
private def weight (k : ℕ) : Fin 2 → ℕ := ![2,k]

def localValue (V : Ambient → ℝ) (p : Ambient) (w : ℝ × ℝ) :=
  V (p.1,p.2 + ![w.1,w.2])

/-- Analytic properties of one reduced endpoint germ at one fixed-plane
point. Each derivative is computed on the given control variation space. -/
structure Germ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Ambient → ℝ) (p : Ambient) where
  f : E → ℝ
  g : E → ℝ
  cost : E → ℝ
  hf : ContDiffAt ℝ 2 f 0
  hg : ContDiffAt ℝ 4 g 0
  hc : ContDiffAt ℝ 1 cost 0
  f0 : f 0 = 0
  f1 : fderiv ℝ f 0 = 0
  g0 : g 0 = 0
  g1 : fderiv ℝ g 0 = 0
  g2 : fderiv ℝ (fderiv ℝ g) 0 = 0
  rank : ∃ a b c d, Return.polarRow f 1 a c * Return.polarRow f 1 b d ≠
    Return.polarRow f 1 a d * Return.polarRow f 1 b c
  cz : cost 0 = 0
  strict : fderiv ℝ cost 0 ≠ 0
  competitors : ∀ᶠ x in 𝓝 0, localValue V p (f x,g x) ≤ localValue V p 0 + cost x
  K : ℝ
  holder : ∀ᶠ z : ℝ × ℝ × ℝ in 𝓝 0,
    localValue V p (z.1,z.2.1) ≤ localValue V p (z.1,z.2.2) + K * |z.2.1-z.2.2|^(1/4:ℝ)

private theorem box_mem {V : Ambient → ℝ} {p : Ambient} (k : ℕ) (A B c δ : ℝ) (cp : 0 < c) (dp : 0 < δ)
    (box : ∀ t : ℝ, 0 < t → t < δ → ∀ a b : ℝ, |a-A| < δ → |b-B| < δ →
      localValue V p (t^2*a,t^k*b) ≤ localValue V p 0 - c*t) :
    p.2 ∈ Sparse.descentSet (fun y => V (p.1,y)) (weight k) := by
  refine ⟨![A,B],δ,c,δ,dp,cp,dp,?_⟩
  intro t ht w hw
  have pos (j : ℕ) := pow_pos ht.1 j
  have scaled (x a : ℝ) (j : ℕ) (h : |x-t^j*a| < δ*t^j) : |x/t^j-a| < δ := by
    rw [← div_lt_iff₀ (pos j),← abs_of_pos (pos j),← abs_div] at h
    rwa [sub_div,abs_of_pos (pos j),mul_div_cancel_left₀ _ (pos j).ne'] at h
  have hit := box t ht.1 ht.2 (w 0/t^2) (w 1/t^k) (scaled _ _ 2 (hw 0)) (scaled _ _ k (hw 1))
  have eq : ![t^2*(w 0/t^2),t^k*(w 1/t^k)] = w := by
    ext i
    fin_cases i <;> simp [mul_div_cancel₀,ht.1.ne']
  have zz : (![0,0] : Plane) = 0 := by ext i; fin_cases i <;> rfl
  simpa only [localValue,Prod.fst_zero,Prod.snd_zero,eq,zz,add_zero] using hit

/-- The fixed-plane null set also excludes boxes for any value agreeing with
the continuous representative on a neighborhood of the center. -/
theorem ae_no_box_germ (V : Ambient → ℝ) (cV : Continuous V) (k : ℕ) (hk : 2 ≤ k) :
    ∀ᵐ p : Ambient, ∀ (D : Ambient → ℝ), V =ᶠ[𝓝 p] D → ∀ A B c δ : ℝ, 0 < c → 0 < δ →
      ¬ (∀ t : ℝ, 0 < t → t < δ → ∀ a b : ℝ, |a-A| < δ → |b-B| < δ →
        localValue D p (t^2*a,t^k*b) ≤ D p - c*t) := by
  have null := Sparse.parallel_planes_null V cV (weight k) (fun i => by fin_cases i <;> first | exact hk | exact le_rfl)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp null] with p outside
  intro D eq A B c δ cp dp box
  let z (s : ℝ × ℝ × ℝ) : Ambient := (p.1,p.2 + ![s.1^2*s.2.1,s.1^k*s.2.2])
  have cz : Continuous z := by
    apply Continuous.prodMk continuous_const
    apply continuous_const.add
    apply continuous_pi
    intro i
    fin_cases i
    · exact (continuous_fst.pow 2).mul (continuous_fst.comp continuous_snd)
    · exact (continuous_fst.pow k).mul (continuous_snd.comp continuous_snd)
  have zz : z (0,A,B) = p := by
    refine Prod.ext ?_ ?_
    · rfl
    ext i
    fin_cases i <;> simp [z,zero_pow (by omega : k ≠ 0)]
  have near := (zz ▸ cz.tendsto (0,A,B) : Tendsto z (𝓝 (0,A,B)) (𝓝 p)) eq
  obtain ⟨r,rp,inside⟩ := Metric.mem_nhds_iff.mp near
  let η := min r δ
  apply outside (box_mem k A B c η cp (lt_min rp dp) ?_)
  intro t ht htη a b ha hb
  have ht' := lt_min_iff.mp htη
  have ha' := lt_min_iff.mp ha
  have hb' := lt_min_iff.mp hb
  have hit : (t,a,b) ∈ Metric.ball ((0,A,B) : ℝ × ℝ × ℝ) r := by
    simpa [Metric.mem_ball,Prod.dist_eq,max_lt_iff,Real.dist_eq,abs_of_pos ht]
      using And.intro ht'.1 (And.intro ha'.1 hb'.1)
  have same : V (z (t,a,b)) = D (z (t,a,b)) := inside hit
  have at0 : localValue V p 0 = V p := by
    change V (p.1,p.2 + ![0,0]) = V p
    rw [show (![0,0] : Plane) = 0 by ext i; fin_cases i <;> rfl,add_zero]
  rw [at0,eq.self_of_nhds]
  exact same.le.trans (box t ht ht'.2 a b ha'.2 hb'.2)

#print axioms ae_no_box_germ

theorem germ_gives_descent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : Ambient → ℝ} {p : Ambient} (G : Germ E V p) :
    ∃ k : ℕ, (k = 3 ∨ k = 4) ∧ p.2 ∈ Sparse.descentSet (fun y => V (p.1,y)) (weight k) := by
  obtain ⟨k,hk,A,B,c,cp,δ,dp,box⟩ := Return.descent_box_from_reduced_jets G.f G.g G.cost
    (localValue V p) G.hf G.hg G.hc G.f0 G.f1 G.g0 G.g1 G.g2 G.rank G.cz G.strict G.competitors G.K G.holder
  exact ⟨k,hk,box_mem k A B c δ cp dp box⟩

/-- One common ambient null set excludes surjectivity of the two-row
quadratic polar for every descending reduced control germ off that set. -/
theorem ae_no_regular_polar {I : Type*} (E : I → Type*) [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)] (V : Ambient → ℝ) (hV : Continuous V) :
    ∀ᵐ p : Ambient, ∀ (i : I) (f g c : E i → ℝ),
      ContDiffAt ℝ 2 f 0 → ContDiffAt ℝ 2 g 0 → ContDiffAt ℝ 1 c 0 →
      f 0 = 0 → fderiv ℝ f 0 = 0 → g 0 = 0 → fderiv ℝ g 0 = 0 →
      c 0 = 0 → fderiv ℝ c 0 ≠ 0 →
      (∀ᶠ v in 𝓝 0, localValue V p (f v,g v) ≤ localValue V p 0+c v) →
      ∀ h, ¬ Function.Surjective (fun a : E i => (fderiv ℝ (fderiv ℝ f) 0 h a,fderiv ℝ (fderiv ℝ g) 0 h a)) := by
  have null := Sparse.parallel_planes_null V hV (weight 2) (fun i => by fin_cases i <;> decide)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp null] with p hp
  intro i f g c hf hg hc f0 f1 g0 g1 c0 strict comp h sur
  obtain ⟨a,ha⟩ := sur (1,0)
  obtain ⟨b,hb⟩ := sur (0,1)
  have minor : Return.polarRow f 1 h a * Return.polarRow g 1 h b ≠
      Return.polarRow f 1 h b * Return.polarRow g 1 h a := by
    have a₁ := congrArg Prod.fst ha
    have a₂ := congrArg Prod.snd ha
    have b₁ := congrArg Prod.fst hb
    have b₂ := congrArg Prod.snd hb
    simp only at a₁ a₂ b₁ b₂
    simp [Return.polarRow,a₁,a₂,b₁,b₂]
  obtain ⟨A,B,C,cp,δ,dp,box⟩ := Return.quadratic_box_from_reduced_jets f g c (localValue V p)
    hf hg hc f0 f1 g0 g1 ⟨h,a,b,minor⟩ c0 strict comp
  exact hp (box_mem 2 A B C δ cp dp box)

#print axioms ae_no_regular_polar

/-- A single exceptional set works for every reduced endpoint pair with
an open set of descending directions, including nonsmooth length costs. -/
theorem ae_no_regular_polar_of_cones (V : Ambient → ℝ) (hV : Continuous V) :
    ∀ᵐ p : Ambient, ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      (f g : E → ℝ), ContDiffAt ℝ 2 f 0 → ContDiffAt ℝ 2 g 0 →
      f 0 = 0 → fderiv ℝ f 0 = 0 → g 0 = 0 → fderiv ℝ g 0 = 0 →
      ∀ O : Set E, IsOpen O → O.Nonempty →
      (∀ h ∈ O, ∀ B : (ℝ × ℝ) →L[ℝ] E, ∃ c > 0, ∀ᶠ q : ℝ × (ℝ × ℝ) in 𝓝 0,
        0 < q.1 → localValue V p (f (q.1 • (h+B q.2)),g (q.1 • (h+B q.2))) ≤ localValue V p 0-c*q.1) →
      ∀ h, ¬ Function.Surjective (fun a => (fderiv ℝ (fderiv ℝ f) 0 h a,fderiv ℝ (fderiv ℝ g) 0 h a)) := by
  have null := Sparse.parallel_planes_null V hV (weight 2) (fun i => by fin_cases i <;> decide)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp null] with p hp
  intro E _ _ f g hf hg f0 f1 g0 g1 O ho ne cone h sur
  obtain ⟨a,ha⟩ := sur (1,0)
  obtain ⟨b,hb⟩ := sur (0,1)
  have a₁ := congrArg Prod.fst ha
  have a₂ := congrArg Prod.snd ha
  have b₁ := congrArg Prod.fst hb
  have b₂ := congrArg Prod.snd hb
  simp only at a₁ a₂ b₁ b₂
  obtain ⟨A,B,c,cp,δ,dp,box⟩ := Return.quadratic_box_from_descent_cones f g (localValue V p)
    hf hg f0 f1 g0 g1 h a b (by simp [a₁,a₂,b₁,b₂]) O ho ne cone
  exact hp (box_mem 2 A B c δ cp dp box)

#print axioms ae_no_regular_polar_of_cones

/-- The witness index may be uncountable and its control spaces can vary.
The exceptional set is measured using outer measure without a selection. -/
theorem null_of_reduced_endpoints {I : Type*} (E : I → Type*) [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)] (V : Ambient → ℝ) (hV : Continuous V) (S : Set Ambient)
    (witness : ∀ p ∈ S, ∃ i, Nonempty (Germ (E i) V p)) :
    volume S = 0 := by
  let bad (k : ℕ) := {p : Ambient | p.2 ∈ Sparse.descentSet (fun y => V (p.1,y)) (weight k)}
  have null (k : ℕ) (hk : 2 ≤ k) : volume (bad k) = 0 := by
    apply Sparse.parallel_planes_null V hV (weight k)
    intro i
    fin_cases i <;> simp [weight,hk]
  apply measure_mono_null (t := bad 3 ∪ bad 4) _ (measure_union_null (null 3 (by decide)) (null 4 (by decide)))
  intro p hp
  obtain ⟨i,⟨G⟩⟩ := witness p hp
  obtain ⟨k,hk,mem⟩ := germ_gives_descent G
  rcases hk with rfl | rfl
  · exact Or.inl mem
  · exact Or.inr mem

#print axioms germ_gives_descent
#print axioms null_of_reduced_endpoints
end MinimizingSard.Reduced
