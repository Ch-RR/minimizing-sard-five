import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue

/-! Spatial C² regularity on the space of continuous paths. The time
variable is a compact parameter with no differentiability requirement. -/
noncomputable section
open Set Filter Metric ContinuousMap
open scoped Topology
namespace MinimizingSard.PathCalculus
variable {I E G : Type*} [TopologicalSpace I] [CompactSpace I]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]

def subst (f : C(I × E,G)) (z : C(I,E)) : C(I,G) :=
  ⟨fun t => f (t,z t), f.continuous.comp (continuous_id.prodMk z.continuous)⟩

omit [NormedSpace ℝ E] [NormedSpace ℝ G] in
theorem continuous_subst (f : C(I × E,G)) : Continuous (subst f) :=
  ContinuousMap.continuous_of_continuous_uncurry _ (f.continuous.comp
    (continuous_snd.prodMk continuous_eval))

private def applyPath (A : C(I,E →L[ℝ] G)) (z : C(I,E)) : C(I,G) :=
  ⟨fun t => A t (z t), A.continuous.clm_apply z.continuous⟩

def multiplier (I E G : Type*) [TopologicalSpace I] [CompactSpace I]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] :
    C(I,E →L[ℝ] G) →L[ℝ] C(I,E) →L[ℝ] C(I,G) := by
  let m : C(I,E →L[ℝ] G) →ₗ[ℝ] C(I,E) →ₗ[ℝ] C(I,G) :=
    LinearMap.mk₂ ℝ (applyPath (I := I) (E := E) (G := G)) (fun _ _ _ => by ext t; simp [applyPath])
    (fun _ _ _ => by ext t; simp [applyPath]) (fun _ _ _ => by ext t; simp [applyPath])
    (fun _ _ _ => by ext t; simp [applyPath])
  have bound (A : C(I,E →L[ℝ] G)) (z : C(I,E)) :
      ‖m A z‖ ≤ 1 * ‖A‖ * ‖z‖ := by
      rw [one_mul]
      change ‖applyPath A z‖ ≤ ‖A‖ * ‖z‖
      apply (ContinuousMap.norm_le (applyPath A z) (mul_nonneg (norm_nonneg A) (norm_nonneg z))).mpr
      intro t
      exact ((A t).le_opNorm (z t)).trans (mul_le_mul
        (A.norm_coe_le_norm t) (z.norm_coe_le_norm t) (norm_nonneg _) (norm_nonneg _))
  exact LinearMap.mkContinuous₂ (σ₁₃ := RingHom.id ℝ) (σ₂₃ := RingHom.id ℝ)
    (E := C(I,E →L[ℝ] G)) (F := C(I,E)) (G := C(I,G)) m 1 bound

theorem hasFDerivAt_subst (f : C(I × E,G)) (D : C(I × E,E →L[ℝ] G))
    (der : ∀ t x, HasFDerivAt (fun y => f (t,y)) (D (t,x)) x) (z : C(I,E)) :
    HasFDerivAt (subst f) (multiplier I E G (subst D z)) z := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε he
  let shift (v : E) : C(I,E) := z + ContinuousMap.const I v
  have cs : Continuous shift := continuous_const.add continuous_const'
  have cont : ContinuousAt (fun v => subst D (shift v)) 0 := ((continuous_subst D).comp cs).continuousAt
  obtain ⟨δ,hδ,osc⟩ := Metric.continuousAt_iff.mp cont ε he
  filter_upwards [Metric.ball_mem_nhds (0 : C(I,E)) hδ] with h hh
  have small : ‖h‖ < δ := by simpa [Metric.mem_ball] using hh
  apply (ContinuousMap.norm_le _ (mul_nonneg he.le (norm_nonneg _))).mpr
  intro t
  have bound (y : E) (hy : y ∈ ball (z t) δ) : ‖D (t,y) - D (t,z t)‖ ≤ ε := by
    have hosc := osc (x := y-z t) (by simpa [dist_eq_norm] using hy)
    rw [dist_eq_norm] at hosc
    have hp := ((subst D (shift (y-z t)) - subst D (shift 0)).norm_coe_le_norm t).trans hosc.le
    simpa [subst, shift] using hp
  have close : z t + h t ∈ ball (z t) δ := by
    simpa [Metric.mem_ball,dist_eq_norm] using (h.norm_coe_le_norm t).trans_lt small
  have est := (convex_ball (z t) δ).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun y _ => (der t y).hasFDerivWithinAt) bound (mem_ball_self hδ) close
  change ‖f (t,z t + h t) - f (t,z t) - D (t,z t) (h t)‖ ≤ ε * ‖h‖
  simpa only [add_sub_cancel_left] using
    est.trans (mul_le_mul_of_nonneg_left (show ‖z t + h t - z t‖ ≤ ‖h‖ by
      simpa using h.norm_coe_le_norm t) he.le)

theorem contDiff_two_subst (f : C(I × E,G)) (D : C(I × E,E →L[ℝ] G))
    (DD : C(I × E,E →L[ℝ] E →L[ℝ] G))
    (der : ∀ t x, HasFDerivAt (fun y => f (t,y)) (D (t,x)) x)
    (der₂ : ∀ t x, HasFDerivAt (fun y => D (t,y)) (DD (t,x)) x) :
    ContDiff ℝ 2 (subst f) := by
  have c1 : ContDiff ℝ 1 (subst D) := contDiff_one_iff_hasFDerivAt.mpr
    ⟨fun z => multiplier I E (E →L[ℝ] G) (subst DD z),
      (multiplier I E (E →L[ℝ] G)).continuous.comp (continuous_subst (I := I) (E := E) (G := E →L[ℝ] E →L[ℝ] G) DD),hasFDerivAt_subst D DD der₂⟩
  let M : C(I,E →L[ℝ] G) →L[ℝ] C(I,E) →L[ℝ] C(I,G) := multiplier I E G
  have cm : ContDiff ℝ 1 (fun a => M a) := by
    exact @ContinuousLinearMap.contDiff ℝ _ C(I,E →L[ℝ] G) _ _
      (C(I,E) →L[ℝ] C(I,G)) _ _ 1 M
  have c : ContDiff ℝ 1 (fun z => M (subst D z)) :=
    ContDiff.comp (g := fun a => M a) (f := subst D) cm c1
  exact (contDiff_succ_iff_hasFDerivAt (n := 1)).mpr
    ⟨fun z => multiplier I E G (subst D z),c,hasFDerivAt_subst f D der⟩

#print axioms contDiff_two_subst

universe u
section FiniteOrder
variable {E G : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A finite tower of continuous spatial derivatives, with time only a parameter. -/
def SpatialOrder {G : Type u} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (n : ℕ) (f : C(I × E,G)) : Prop :=
  match n with
  | 0 => True
  | k + 1 => ∃ D : C(I × E,E →L[ℝ] G),
      (∀ t x, HasFDerivAt (fun y => f (t,y)) (D (t,x)) x) ∧ SpatialOrder (G := E →L[ℝ] G) k D

theorem contDiff_subst_of_spatialOrder (n : ℕ) (f : C(I × E,G)) (hf : SpatialOrder n f) :
    ContDiff ℝ n (subst f) := by
  induction n generalizing G with
  | zero => exact contDiff_zero.mpr (continuous_subst (I := I) (G := G) (E := E) f)
  | succ n ih =>
    obtain ⟨D,d,hd⟩ := hf
    let M := multiplier I E G
    have cm := @ContinuousLinearMap.contDiff ℝ _ C(I,E →L[ℝ] G) _ _
      (C(I,E) →L[ℝ] C(I,G)) _ _ n M
    apply (contDiff_succ_iff_hasFDerivAt (n := n)).mpr
    exact ⟨fun z => M (subst D z),cm.comp (ih D hd),hasFDerivAt_subst f D d⟩

#print axioms contDiff_subst_of_spatialOrder
end FiniteOrder
end MinimizingSard.PathCalculus
