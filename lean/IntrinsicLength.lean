import PartitionVelocity
import GlobalCurveSard

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
open Volterra
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] {m : ℕ}

private def VelocityCode (Γ : Geometry M m) (γ : C(Time,M)) (t : ℝ) (u : Fiber m) : Prop :=
  ∃ e ∈ Γ.frames, γ (clamp t) ∈ e.chart.source ∧ HasDerivAt (fun s => e.chart (γ (clamp s)))
    (e.coefficient (e.chart (γ (clamp t))) u) t

private theorem global_velocity (Γ : Geometry M m) (γ : C(Time,M)) (l : ℝ) (path : PathHasLength Γ γ l) :
    ∃ U : Control m, l = length (fun _ : Fin 1 => U) ∧
      ∀ᵐ t ∂volume.restrict (Ioc (0:ℝ) 1), VelocityCode Γ γ t (U t) := by
  classical
  obtain ⟨n,P,e,p,he,walk,rep,rfl⟩ := path
  obtain ⟨u,sol⟩ := walk.has_codes
  obtain ⟨R,forward,back⟩ := P.coordinates m
  let U := R.symm u
  have ru : R U = u := R.apply_symm_apply u
  refine ⟨U,sol.length_eq.trans (P.length_eq_of_rescaling _ _ (ru ▸ forward U)),?_⟩
  have each := fun i => chart_derivative_on_block rep sol i (ru ▸ back U i)
  have avoid (i : Fin (n+1)) : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ P.cut i.succ := by
    exact (ae_iff.mpr (by simp) : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ P.cut i.succ)
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [ae_all_iff.mpr each,ae_all_iff.mpr avoid] with t dt no
  intro ht
  obtain ⟨i,hi⟩ := mem_iUnion.mp (P.covers ht)
  have h := dt i ⟨hi.1,lt_of_le_of_ne hi.2 (no i)⟩
  exact ⟨e i,he i,h⟩


private theorem metric_speed_agrees (Γ : Geometry M m) (γ : C(Time,M)) {t : ℝ} {u v : Fiber m}
    (hu : VelocityCode Γ γ t u) (hv : VelocityCode Γ γ t v) : speedSq u = speedSq v := by
  obtain ⟨e,he,src,du⟩ := hu
  obtain ⟨b,hb,dst,dv⟩ := hv
  let y := γ (clamp t)
  let T := b.chart ∘ e.chart.symm
  have dt := (transition_smooth (k := 1) e.chart b.chart e.compatible b.compatible y src dst).differentiableAt (by decide)
  have same : (fun s => b.chart (γ (clamp s))) =ᶠ[𝓝 t] (T ∘ (fun s => e.chart (γ (clamp s)))) := by
    have ct : Continuous (fun s : ℝ => γ (clamp s)) := γ.continuous.comp continuous_projIcc
    filter_upwards [ct.continuousAt (e.chart.open_source.mem_nhds src)] with s hs
    simp [T,Function.comp_apply,e.chart.left_inv hs]
  have D := ((dt.hasFDerivAt.comp_hasDerivAt t du).congr_of_eventuallyEq same).unique dv
  obtain ⟨R,swap⟩ := Γ.overlap e he b hb y ⟨src,dst⟩
  have rval : R u = v := by
    apply b.coefficient_injective (b.chart.map_source dst)
    rw [Frame.coefficient_apply,← (swap u).2]
    simpa only [Frame.coefficient_apply] using D
  exact (swap u).1.symm.trans (congrArg speedSq rval)

/-- The same actual curve has the same length in any two finite
Sobolev representations, for arbitrary subdivisions and chart changes. -/
theorem PathHasLength.unique {Γ : Geometry M m} {γ : C(Time,M)} {l d : ℝ}
    (a : PathHasLength Γ γ l) (b : PathHasLength Γ γ d) : l = d := by
  obtain ⟨U,hl,hu⟩ := global_velocity Γ γ l a
  obtain ⟨V,hd,hv⟩ := global_velocity Γ γ d b
  rw [hl,hd]
  simp only [length,Finset.univ_unique,Finset.sum_singleton]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le zero_le_one]
  filter_upwards [hu,hv] with t ut vt using congrArg Real.sqrt (metric_speed_agrees Γ γ ut vt)

/-- Geometric horizontality expressed by the actual chart derivative at
almost every physical time, in any frame of the cover. -/
theorem PathHasLength.chart_velocity {Γ : Geometry M m} {γ : C(Time,M)} {l : ℝ}
    (path : PathHasLength Γ γ l) (b : Frame M m) (hb : b ∈ Γ.frames) :
    ∀ᵐ t ∂volume.restrict (Ioc (0:ℝ) 1), γ (clamp t) ∈ b.chart.source →
      ∃ v : Fiber m, HasDerivAt (fun s => b.chart (γ (clamp s))) (b.coefficient (b.chart (γ (clamp t))) v) t := by
  obtain ⟨U,_,hu⟩ := global_velocity Γ γ l path
  filter_upwards [hu] with t ht
  intro dst
  obtain ⟨e,he,src,du⟩ := ht
  let y := γ (clamp t)
  let T := b.chart ∘ e.chart.symm
  have dt := (transition_smooth (k := 1) e.chart b.chart e.compatible b.compatible y src dst).differentiableAt (by decide)
  have same : (fun s => b.chart (γ (clamp s))) =ᶠ[𝓝 t] (T ∘ (fun s => e.chart (γ (clamp s)))) := by
    have ct : Continuous (fun s : ℝ => γ (clamp s)) := γ.continuous.comp continuous_projIcc
    filter_upwards [ct.continuousAt (e.chart.open_source.mem_nhds src)] with s hs
    simp [T,Function.comp_apply,e.chart.left_inv hs]
  obtain ⟨R,swap⟩ := Γ.overlap e he b hb y ⟨src,dst⟩
  refine ⟨R (U t),((dt.hasFDerivAt.comp_hasDerivAt t du).congr_of_eventuallyEq same).congr_deriv ?_⟩
  simpa only [Frame.coefficient_apply] using (swap (U t)).2

theorem PathHasLength.physical_velocity {Γ : Geometry M m} {γ : C(Time,M)} {l : ℝ}
    (path : PathHasLength Γ γ l) : ∃ U : Control m, l = (∫ t in (0:ℝ)..1, Real.sqrt (speedSq (U t))) ∧
      ∀ᵐ t ∂volume.restrict (Ioc (0:ℝ) 1), ∃ e ∈ Γ.frames, γ (clamp t) ∈ e.chart.source ∧
        HasDerivAt (fun s => e.chart (γ (clamp s))) (e.coefficient (e.chart (γ (clamp t))) (U t)) t := by
  obtain ⟨U,eq,vel⟩ := global_velocity Γ γ l path
  exact ⟨U,by simpa [length] using eq,vel⟩

#print axioms PathHasLength.physical_velocity
#print axioms PathHasLength.chart_velocity
#print axioms PathHasLength.unique
end MinimizingSard.Five
