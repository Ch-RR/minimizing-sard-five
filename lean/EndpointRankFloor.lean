import CorankOneLength

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] [IsManifold 𝓘(ℝ,State) ∞ M]

/-- One measure exception works for all frames meeting the endpoint, even if
the frame atlas itself has uncountably many members. -/
theorem ae_second_layer_dimension (Γ : Geometry M 2) (c : OpenPartialHomeomorph M State)
    (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) :
    ∀ᵐ q : State, q ∈ c.target → ∀ e ∈ Γ.frames, c.symm q ∈ e.chart.source →
      Module.finrank ℝ ((wordLayer e.X (e.chart (c.symm q)) 2).map
        (fderiv ℝ (c ∘ e.chart.symm) (e.chart (c.symm q))).toLinearMap) = 3 := by
  let U (e : Γ.frames) := (c.symm.trans e.val.chart).source
  have cover (q) (inside : q ∈ c.target) : q ∈ ⋃ e, U e := by
    obtain ⟨e,he,hy⟩ := Γ.cover (c.symm q)
    exact mem_iUnion.mpr ⟨⟨e,he⟩,inside,hy⟩
  obtain ⟨T,count,cov⟩ := (IsLindelof.of_coe : IsLindelof c.target).elim_countable_subcover
    U (fun e => (c.symm.trans e.val.chart).open_source) cover
  letI : Countable T := count.to_subtype
  have good (b : Γ.frames) : ∀ᵐ q : State, q ∈ U b →
      Module.finrank ℝ (wordLayer b.val.X (b.val.chart (c.symm q)) 2) = 3 := by
    apply ae_chart_overlap b.val.chart c b.val.compatible hc (fun q => Module.finrank ℝ (wordLayer b.val.X q 2) = 3)
    exact (ae_frame_flag b.val).mono fun _ h inside => (h inside).1
  filter_upwards [ae_all_iff.mpr fun b : T => good b.val] with q all
  intro hq e he ey
  let y := c.symm q
  obtain ⟨b,hit⟩ := mem_iUnion.mp (cov hq)
  obtain ⟨bt,inside⟩ := mem_iUnion.mp hit
  have by' : y ∈ b.val.chart.source := inside.2
  have cy : y ∈ c.source := c.map_target hq
  rw [frame_word_layer_invariant Γ e b.val he b.property c hc y ey by' cy 2]
  obtain ⟨L,eq⟩ := ContinuousLinearMap.IsInvertible.of_inverse
    (transition_left c b.val.chart hc b.val.compatible y cy by')
    (transition_left b.val.chart c b.val.compatible hc y by' cy)
  rw [← eq]
  exact (L.toLinearEquiv.finrank_map_eq _).trans (all ⟨b,bt⟩ inside)

/-- A nonconstant path has the full transported second layer in its endpoint
derivative range at the last moving piece. This statement is pointwise. -/
theorem second_layer_in_endpoint_range (x y : M) (distinct : x ≠ y)
    (c : OpenPartialHomeomorph M State) (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (hy : y ∈ c.source)
    {n : ℕ} (e : Fin (n+1) → Frame M 2) (w : Fin (n+1) → Control 2) (path : Joins e w x y)
    (G : (Fin (n+1) → Control 2) → State)
    (graph : ∀ᶠ b in 𝓝 w, G b ∈ c.target ∧ ∀ z, Joins e b x z ↔ z = c.symm (G b)) :
    ∃ i, w i ≠ 0 ∧ (∀ j, i < j → w j = 0) ∧ y ∈ (e i).chart.source ∧
      (wordLayer (e i).X ((e i).chart y) 2).map (fderiv ℝ (c ∘ (e i).chart.symm) ((e i).chart y)).toLinearMap ≤
        LinearMap.range (fderiv ℝ G w).toLinearMap := by
  obtain ⟨i,mi,tail,iy,_⟩ := whole_second_flag_at_distinct_endpoint x y distinct c hc hy 0 n e w path G graph
    (fun _ => rfl)
  refine ⟨i,mi,tail,iy,?_⟩
  let f := e i
  let z := f.chart y
  let J := fderiv ℝ (c ∘ f.chart.symm) z
  let W := LinearMap.range (fderiv ℝ G w).toLinearMap
  have pairing (p : State →L[ℝ] ℝ) (ann : ∀ h, p (fderiv ℝ G w h) = 0) :
      (wordLayer f.X z 2).map J.toLinearMap ≤ LinearMap.ker p.toLinearMap := by
    obtain ⟨j,mj,last,_,flag⟩ := whole_second_flag_at_distinct_endpoint x y distinct c hc hy p n e w path G graph ann
    obtain rfl : j = i := le_antisymm (le_of_not_gt fun h => mj (tail j h)) (le_of_not_gt fun h => mi (last i h))
    apply Submodule.map_le_iff_le_comap.mpr
    apply (second_layer_le_span _ _).trans
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    fin_cases j
    · exact flag.1 0
    · exact flag.1 1
    · exact flag.2
  intro b hb
  by_contra out
  obtain ⟨l,nz,zero⟩ := W.exists_dual_map_eq_bot_of_notMem out inferInstance
  have annih : W ≤ LinearMap.ker l := by
    intro v hv
    have h : l v ∈ W.map l := ⟨v,hv,rfl⟩
    rwa [zero] at h
  have kill := pairing l.toContinuousLinearMap (fun h => annih (show fderiv ℝ G w h ∈ W from ⟨h,rfl⟩))
  exact nz (kill hb)

/-- At almost every endpoint every path from a distinct source has endpoint
derivative rank at least three, without a minimizing or speed hypothesis. -/
theorem ae_endpoint_rank_at_least_three (Γ : Geometry M 2) (x : M) (c : OpenPartialHomeomorph M State)
    (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) :
    ∀ᵐ q : State, q ∈ c.target → ∀ {n : ℕ} (e : Fin (n+1) → Frame M 2) (w : Fin (n+1) → Control 2),
    let y := c.symm q
    x ≠ y → (∀ i, e i ∈ Γ.frames) → Joins e w x y → ∀ G : (Fin (n+1) → Control 2) → State,
    (∀ᶠ b in 𝓝 w, G b ∈ c.target ∧ ∀ z, Joins e b x z ↔ z = c.symm (G b)) →
    3 ≤ Module.finrank ℝ (LinearMap.range (fderiv ℝ G w).toLinearMap) := by
  filter_upwards [ae_second_layer_dimension Γ c hc] with q good
  intro hq n e w y away he path G graph
  obtain ⟨i,_,_,iy,inc⟩ := second_layer_in_endpoint_range x y away c hc (c.map_target hq) e w path G graph
  exact (good hq _ (he i) iy) ▸ Submodule.finrank_mono inc

#print axioms ae_second_layer_dimension
#print axioms second_layer_in_endpoint_range
#print axioms ae_endpoint_rank_at_least_three

/-- Outside a single null set, every minimizing singular control in horizontal
rank two supports the original length at its endpoint derivative. -/
theorem ae_singular_minimizer_has_multiplier (Γ : Geometry M 2) (x : M) (c : OpenPartialHomeomorph M State)
    (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) :
    ∀ᵐ q : State, q ∈ c.target → ∀ {n : ℕ} (e : Fin (n+1) → Frame M 2) (w : Fin (n+1) → Control 2)
      (G : (Fin (n+1) → Control 2) → State),
      let y := c.symm q
      (∀ i, e i ∈ Γ.frames) → Joins e w x y →
      (∀ (k : ℕ) (a : Fin (k+1) → Frame M 2) (b : Fin (k+1) → Control 2),
        (∀ i, a i ∈ Γ.frames) → Joins a b x y → length w ≤ length b) →
      (∀ᶠ b in 𝓝 w, G b ∈ c.target ∧ ∀ z, Joins e b x z ↔ z = c.symm (G b)) →
      ¬ Function.Surjective (fderiv ℝ G w) → HasCostMultiplier length (fderiv ℝ G w) w := by
  have off : ∀ᵐ q : State, q ≠ c x := by
    apply ae_iff.mpr
    simpa only [not_not] using measure_singleton (μ := (volume : Measure State)) (c x)
  filter_upwards [off,ae_endpoint_rank_at_least_three Γ x c hc,ae_corank_two_length_multiplier Γ x c hc,
    ae_corank_one_length_multiplier Γ x c hc] with q outside floor three four
  intro hq n e w G y he path minimal graph singular
  have away : x ≠ y := fun h => outside ((c.right_inv hq).symm.trans (congrArg c h.symm))
  let W := LinearMap.range (fderiv ℝ G w).toLinearMap
  have low : 3 ≤ Module.finrank ℝ W := floor hq e w away he path G graph
  have proper : W < ⊤ := lt_top_iff_ne_top.mpr fun eq =>
    singular (LinearMap.range_eq_top.mp eq)
  have upper := Submodule.finrank_lt_finrank_of_lt proper
  rw [finrank_top,Module.finrank_fin_fun] at upper
  rcases (show Module.finrank ℝ W = 3 ∨ Module.finrank ℝ W = 4 by omega) with h | h
  · exact three hq e w G away he path minimal graph h
  · exact four hq e w G he path minimal graph h

#print axioms ae_singular_minimizer_has_multiplier

end MinimizingSard.Five
