import SobolevChartChange

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
open Volterra
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] {m : ℕ}

/-- Actual squared horizontal speed computed from ambient Sobolev coordinates. -/
def Frame.rawSpeedSq (e : Frame M m) (p : State × Control 5) (r : ℝ) : ℝ :=
  speedSq (e.recover (ambientPath p (clamp r)) (p.2 r))

theorem Frame.raw_speed_of_control (e : Frame M m) {p : State × Control 5} {u : Control m}
    (sol : e.Solves u p.1 (ambientPath p)) : ∀ᵐ r ∂controlMeasure, e.rawSpeedSq p r = speedSq (u r) := by
  let A : C(Time,Fiber m →L[ℝ] State) := ⟨fun t => e.coefficient (ambientPath p t),
    e.coefficient_smooth.continuousOn.comp_continuous (ambientPath p).continuous sol.1⟩
  have v := (e.solve_primitive sol).replace_ae (multiplyVelocity_ae A u).symm
  have eq : multiplyVelocity (Fiber m) State A u = p.2 := v.velocity_unique (ambient_primitive p)
  filter_upwards [multiplyVelocity_ae A u] with r hr
  rw [eq] at hr
  unfold Frame.rawSpeedSq
  rw [hr]; exact congrArg speedSq (e.recover_coefficient (sol.1 _) _)

variable [IsManifold 𝓘(ℝ,State) ∞ M]
private theorem pointwise_transfer (Γ : Geometry M m) (a b : Frame M m) (ha : a ∈ Γ.frames) (hb : b ∈ Γ.frames)
    (z : State) (hz : z ∈ (a.chart.symm.trans b.chart).source) (v : State) :
    let T := b.chart ∘ a.chart.symm
    let J := fderiv ℝ T z
    (v ∈ LinearMap.range (a.coefficient z).toLinearMap ↔ J v ∈ LinearMap.range (b.coefficient (T z)).toLinearMap) ∧
      (v ∈ LinearMap.range (a.coefficient z).toLinearMap →
        speedSq (a.recover z v) = speedSq (b.recover (T z) (J v))) := by
  intro T J
  let y := a.chart.symm z
  have ay : y ∈ a.chart.source := a.chart.map_target hz.1
  have by' : y ∈ b.chart.source := hz.2
  have az : a.chart y = z := a.chart.right_inv hz.1
  obtain ⟨R,swap⟩ := Γ.overlap a ha b hb y ⟨ay,by'⟩
  have formula (u : Fiber m) : J (a.coefficient z u) = b.coefficient (T z) (R u) := by
    have h := (swap u).2
    rw [az] at h
    simpa only [Frame.coefficient_apply] using h
  have inv := transition_left a.chart b.chart a.compatible b.compatible y ay by'
  have inj : Function.Injective J := by
    intro h k eq
    have l := DFunLike.congr_fun inv h
    have r := DFunLike.congr_fun inv k
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,az] at l r
    exact l.symm.trans ((congrArg (fderiv ℝ (a.chart ∘ b.chart.symm) (b.chart y)) eq).trans r)
  refine ⟨⟨?_,?_⟩,?_⟩
  · rintro ⟨u,rfl⟩; exact ⟨R u,(formula u).symm⟩
  · rintro ⟨u,hu⟩; refine ⟨R.symm u,inj ?_⟩
    change J (a.coefficient z (R.symm u)) = J v
    rw [formula,R.apply_symm_apply]; exact hu
  · rintro ⟨u,rfl⟩
    change speedSq (a.recover z (a.coefficient z u)) = speedSq (b.recover (T z) (J (a.coefficient z u)))
    rw [a.recover_coefficient hz.1,formula,b.recover_coefficient (z := T z) (b.chart.map_source by') (R u)]
    exact (swap u).1.symm

/-- Change of state chart preserves the geometric horizontal condition
and the speed almost everywhere on all nearby Sobolev trajectories. -/
theorem sobolev_frame_transition (Γ : Geometry M m) (a b : Frame M m) (ha : a ∈ Γ.frames) (hb : b ∈ Γ.frames)
    (p : State × Control 5) (inside : ∀ t, ambientPath p t ∈ (a.chart.symm.trans b.chart).source)
    (k : ℕ) :
    ∃ H : State × Control 5 → State × Control 5, ContDiffAt ℝ k H p ∧ ∀ᶠ z in 𝓝 p,
      (H z).1 = b.chart (a.chart.symm z.1) ∧
      (∀ t, ambientPath z t ∈ (a.chart.symm.trans b.chart).source ∧
        ambientPath (H z) t = b.chart (a.chart.symm (ambientPath z t))) ∧
      (a.HorizontalSobolev z ↔ b.HorizontalSobolev (H z)) ∧
      (a.HorizontalSobolev z → a.rawSpeedSq z =ᵐ[controlMeasure] b.rawSpeedSq (H z)) := by
  let O := (a.chart.symm.trans b.chart).source
  let T := b.chart ∘ a.chart.symm
  have smooth : ContDiffOn ℝ ∞ T O := by
    have h := (compatible_of_mem_maximalAtlas a.compatible b.compatible).1
    change ContDiffOn ℝ ∞ T (O ∩ range (𝓘(ℝ,State))) at h
    simpa using h
  obtain ⟨H,ch,loc⟩ := sobolev_coordinate_germ O (a.chart.symm.trans b.chart).open_source T
    smooth p inside k
  refine ⟨H,ch,?_⟩
  filter_upwards [loc] with z h
  obtain ⟨start,states,vel⟩ := h
  refine ⟨start,states,⟨?_,?_⟩,?_⟩
  · rintro ⟨_,horizontal⟩
    refine ⟨fun t => (states t).2.symm ▸ b.chart.map_source (states t).1.2,?_⟩
    filter_upwards [horizontal,vel] with r hr hv
    rw [hv,(states _).2]
    exact (pointwise_transfer Γ a b ha hb _ (states _).1 _).1.mp hr
  · rintro ⟨_,horizontal⟩
    refine ⟨fun t => (states t).1.1,?_⟩
    filter_upwards [horizontal,vel] with r hr hv
    rw [hv,(states _).2] at hr
    exact (pointwise_transfer Γ a b ha hb _ (states _).1 _).1.mpr hr
  · intro horiz
    filter_upwards [horiz.2,vel] with r hr hv
    unfold Frame.rawSpeedSq
    rw [hv,(states _).2]
    exact (pointwise_transfer Γ a b ha hb _ (states _).1 _).2 hr

#print axioms Frame.raw_speed_of_control
#print axioms sobolev_frame_transition
end MinimizingSard.Five
