import FlowVariation
import TrajectoryTransport

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace MinimizingSard.Five
open Volterra PulseGeometry PathCalculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def autonomousColumns (X : Fin 2 → E → E) (sm : ∀ i, ContDiff ℝ ∞ (X i)) : Columns E where
  Y i _ := X i
  continuous i := (sm i).continuous.comp continuous_snd
  differentiable i _ _ := (sm i).differentiable (by simp)
  jacobian i := ((sm i).continuous_fderiv (by simp)).comp continuous_snd

private theorem first_jets (X : Fin 2 → E → E) (sm : ∀ i, ContDiff ℝ ∞ (X i)) (i : Fin 2) :
    SpatialOrder 1 ((autonomousColumns X sm).spatialField i) := by
  exact ⟨⟨fun p => fderiv ℝ (X i) p.2,((sm i).continuous_fderiv (by simp)).comp continuous_snd⟩,
    fun _ x => ((sm i).differentiable (by simp) x).hasFDerivAt,trivial⟩

private theorem second_jets (X : Fin 2 → E → E) (sm : ∀ i, ContDiff ℝ ∞ (X i)) (i : Fin 2) :
    SpatialOrder 2 ((autonomousColumns X sm).spatialField i) := by
  let D := fderiv ℝ (X i)
  have cd : ContDiff ℝ ∞ D := (sm i).fderiv_right (by simp)
  exact ⟨⟨fun p => D p.2,cd.continuous.comp continuous_snd⟩,
    fun _ x => ((sm i).differentiable (by simp) x).hasFDerivAt,
    ⟨fun p => fderiv ℝ D p.2,(cd.continuous_fderiv (by simp)).comp continuous_snd⟩,
    fun _ x => (cd.differentiable (by simp) x).hasFDerivAt,trivial⟩

theorem smooth_tangentLift (X : E → E) (sm : ContDiff ℝ ∞ X) : ContDiff ℝ ∞ (tangentLift X) :=
  (sm.comp contDiff_fst).prodMk (((sm.fderiv_right (by simp)).comp contDiff_fst).clm_apply contDiff_snd)

private theorem velocity_integrable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (X : Fin 2 → V → V) (sm : ∀ i, ContDiff ℝ ∞ (X i)) (w : C(Time,V)) (u : Controls) :
    IntervalIntegrable (fun t => (autonomousColumns X sm).velocity t (w (clamp t)) (u t)) volume 0 1 := by
  let L (i : Fin 2) := ContinuousLinearMap.smulRightL ℝ (Fin 2 → ℝ) V (ContinuousLinearMap.proj i)
  let A : C(Time,(Fin 2 → ℝ) →L[ℝ] V) := ⟨fun t => L 0 (X 0 (w t))+L 1 (X 1 (w t)),
    ((L 0).continuous.comp ((sm 0).continuous.comp w.continuous)).add
    ((L 1).continuous.comp ((sm 1).continuous.comp w.continuous))⟩
  exact Volterra.intervalIntegrable A u

variable [CompleteSpace E]

/-- For smooth autonomous frame extensions, the actual lifted integral flow
agrees on a neighborhood, at every time, with the spatial tangent map
of the original flow. Both flows are driven by the same rough control. -/
theorem local_tangent_flow (X : Fin 2 → E → E) (sm : ∀ i, ContDiff ℝ ∞ (X i)) (q h : E) :
    ∃ S : E × Controls → C(Time,E), S 0 = ContinuousMap.const Time q ∧ ContDiffAt ℝ 2 S 0 ∧
      ∀ᶠ p : (E × E) × Controls in 𝓝 0,
        let z := S (p.1.1,p.2)
        let v := fun t : Time => fderiv ℝ (fun a => S (a,p.2) t) p.1.1 (h+p.1.2)
        (autonomousColumns X sm).Path (q+p.1.1) p.2 (fun t => z (clamp t)) ∧
        let B := autonomousColumns (fun i => tangentLift (X i)) (fun i => smooth_tangentLift _ (sm i))
        B.Path ((q,h)+p.1) p.2 (fun t => (z (clamp t),v (clamp t))) ∧
        ∀ w, B.Path ((q,h)+p.1) p.2 w → ∀ t : Time, w t = (z t,v t) := by
  let Y (i : Fin 2) := tangentLift (X i)
  have sy : ∀ i, ContDiff ℝ ∞ (Y i) := fun i => smooth_tangentLift _ (sm i)
  let B := autonomousColumns Y sy
  obtain ⟨S,cs,near⟩ := column_flow_variation (autonomousColumns X sm) q (first_jets X sm)
  obtain ⟨W,_,_,lifted⟩ := joint_path_family B 1 (by norm_num) (first_jets Y sy) (q,h)
  have push : Tendsto (fun p : (E × E) × Controls => (p.1.1,p.2)) (𝓝 0) (𝓝 0) :=
    ((continuous_fst.comp continuous_fst).prodMk continuous_snd).tendsto 0
  obtain ⟨A,a0,ca,refFlow⟩ := joint_path_family (autonomousColumns X sm) 2 (by norm_num) (second_jets X sm) q
  have agree : S =ᶠ[𝓝 0] (fun p => ContinuousMap.const Time q + A p) := by
    filter_upwards [near,refFlow] with p hp hr
    apply ContinuousMap.ext
    intro t
    simpa only [show clamp (t:ℝ) = t from projIcc_of_mem _ t.2] using hr.2 _ hp.1 t
  have sm2 : ContDiffAt ℝ 2 (fun p => ContinuousMap.const Time q + A p) 0 := contDiffAt_const.add ca
  refine ⟨S,by simpa only [a0,add_zero] using agree.self_of_nhds,sm2.congr_of_eventuallyEq agree,?_⟩
  filter_upwards [push near,lifted,push (cs.eventually (by simp))] with p hp lp ds
  let z := S (p.1.1,p.2)
  let v := fderiv ℝ (fun a => S (a,p.2)) p.1.1 (h+p.1.2)
  let w : C(Time,E × E) := ⟨fun t => (z t,v t),z.continuous.prodMk v.continuous⟩
  let f := fun t => B.velocity t (w (clamp t)) (p.2 t)
  have hi : IntervalIntegrable f volume 0 1 := velocity_integrable Y sy w p.2
  have path : B.Path ((q,h)+p.1) p.2 (fun t => w (clamp t)) := by
    refine ⟨(w.continuous.comp continuous_projIcc).continuousOn,hi,?_⟩
    intro t ht
    have sub : IntervalIntegrable f volume 0 t := hi.mono_set (by
      rw [uIcc_of_le ht.1,uIcc_of_le zero_le_one]; exact Icc_subset_Icc le_rfl ht.2)
    have ct : clamp t = ⟨t,ht⟩ := projIcc_of_mem _ ht
    apply Prod.ext
    · change z (clamp t) = (q+p.1.1) + (ContinuousLinearMap.fst ℝ E E) (∫ r in (0:ℝ)..t, f r)
      rw [← ContinuousLinearMap.intervalIntegral_comp_comm _ sub]
      exact hp.1.2.2 t ht
    · change v (clamp t) = (h+p.1.2) + (ContinuousLinearMap.snd ℝ E E) (∫ r in (0:ℝ)..t, f r)
      rw [← ContinuousLinearMap.intervalIntegral_comp_comm _ sub,ct]
      exact hp.2.2 (h+p.1.2) ⟨t,ht⟩
  have val (t : Time) : fderiv ℝ (fun a => S (a,p.2) t) p.1.1 (h+p.1.2) = v t := by
    change ContDiffAt ℝ 1 S (p.1.1,p.2) at ds
    have incl : DifferentiableAt ℝ (fun a : E => (a,p.2)) p.1.1 :=
      differentiableAt_id.prodMk (differentiableAt_const p.2)
    have d : DifferentiableAt ℝ (fun a => S (a,p.2)) p.1.1 := (ds.differentiableAt (by norm_num)).comp p.1.1 incl
    rw [show (fun a => S (a,p.2) t) = (ContinuousMap.evalCLM ℝ t) ∘ (fun a => S (a,p.2)) from rfl,
      ((ContinuousMap.evalCLM ℝ t).hasFDerivAt.comp p.1.1 d.hasFDerivAt).fderiv]
    rfl
  dsimp only
  simp_rw [val]
  refine ⟨hp.1,path,fun a ha t => ?_⟩
  have same := (lp.2 a ha t).trans (lp.2 _ path t).symm
  simpa only [show clamp (t:ℝ) = t from projIcc_of_mem _ t.2] using same

#print axioms local_tangent_flow
end MinimizingSard.Five
