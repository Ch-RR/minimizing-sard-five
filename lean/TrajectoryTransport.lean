import ChartTrajectoryDerivative
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace MinimizingSard.Five

/-- Differentiate a transported vector field at a Lebesgue time.
The instantaneous vector field and its spatial derivative enter the
variational equation; no time derivative of the control occurs. -/
theorem pulled_field_derivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (z : ℝ → E) (J : ℝ → E →L[ℝ] E) (V X : E → E) (t : ℝ)
    (hz : HasDerivAt z (V (z t)) t)
    (hJ : HasDerivAt J ((fderiv ℝ V (z t)).comp (J t)) t)
    (inv : (J t).IsInvertible) (hX : DifferentiableAt ℝ X (z t)) :
    HasDerivAt (fun s => (J s).inverse (X (z s)))
      ((J t).inverse (VectorField.lieBracket ℝ V X (z t))) t := by
  obtain ⟨e,he⟩ := inv
  let g := (ContinuousLinearEquiv.unitsEquiv ℝ E).symm e
  have eg : (g : E →L[ℝ] E) = J t := he
  have d := hasFDerivAt_ringInverse (𝕜 := ℝ) g
  rw [eg] at d
  have di := d.comp_hasDerivAt t hJ
  have dx := hX.hasFDerivAt.comp_hasDerivAt t hz
  have result := di.clm_apply dx
  rw [ContinuousLinearMap.ringInverse_eq_inverse] at result
  convert result using 1
  change (J t).inverse ((fderiv ℝ X (z t)) (V (z t)) - (fderiv ℝ V (z t)) (X (z t))) =
    ((-ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E) (↑g⁻¹) (↑g⁻¹))
      ((fderiv ℝ V (z t)).comp (J t))) (X (z t)) + (J t).inverse ((fderiv ℝ X (z t)) (V (z t)))
  rw [← he,ContinuousLinearMap.inverse_equiv]
  change e.symm (_ - _) = -(e.symm ((fderiv ℝ V (z t)) (e (e.symm (X (z t)))))) + e.symm _
  rw [e.apply_symm_apply,map_sub]; abel

#print axioms pulled_field_derivative

/-- The two transported frame values along an arbitrary original reference.
Only the state Jacobian's variational ODE and its invertibility remain as
inputs. The signs, bracket and control factors follow from the actual fields. -/
theorem transported_frame_values {M : Type*} [TopologicalSpace M] [ChartedSpace State M]
    (e : Frame M 2) (u : Control 2) (z : ℝ → State) (J : ℝ → State →L[ℝ] State)
    (mz : MapsTo z (Icc 0 1) e.chart.target)
    (hi : IntervalIntegrable (fun t => e.velocity (z t) (u t)) volume 0 1)
    (eq : ∀ t ∈ Icc (0:ℝ) 1, z t = z 0 + ∫ s in (0:ℝ)..t, e.velocity (z s) (u s))
    (variation : ∀ᵐ t ∂volume.restrict (Ioo (0:ℝ) 1),
      (J t).IsInvertible ∧ HasDerivAt J ((fderiv ℝ (fun x => e.velocity x (u t)) (z t)).comp (J t)) t) :
    let Y := fun (i : Fin 2) (s : ℝ) => (J s).inverse (e.X i (z s))
    let B := fun s => (J s).inverse (VectorField.lieBracket ℝ (e.X 0) (e.X 1) (z s))
    ∀ᵐ t ∂volume.restrict (Ioo (0:ℝ) 1),
      HasDerivAt (Y 0) (-(u t 1) • B t) t ∧ HasDerivAt (Y 1) (u t 0 • B t) t := by
  dsimp only
  filter_upwards [chart_ae_velocity e u z hi eq,variation,ae_restrict_mem measurableSet_Ioo] with t dz jac ht
  have hx := mz (show t ∈ Icc (0:ℝ) 1 from ⟨ht.1.le,ht.2.le⟩)
  have diff (i : Fin 2) : DifferentiableAt ℝ (e.X i) (z t) :=
    ((e.smooth i _ hx).contDiffAt (e.chart.open_target.mem_nhds hx)).differentiableAt (by simp)
  let V (x : State) := e.velocity x (u t)
  have vel : V = u t 0 • e.X 0 + u t 1 • e.X 1 := by
    funext x
    simp [V,Frame.velocity,Fin.sum_univ_two]
  have bracket (i : Fin 2) : VectorField.lieBracket ℝ V (e.X i) (z t) =
      u t 0 • VectorField.lieBracket ℝ (e.X 0) (e.X i) (z t) +
      u t 1 • VectorField.lieBracket ℝ (e.X 1) (e.X i) (z t) := by
    rw [vel,VectorField.lieBracket_add_left ((diff 0).const_smul _) ((diff 1).const_smul _),
      VectorField.lieBracket_const_smul_left (diff 0),VectorField.lieBracket_const_smul_left (diff 1)]
  have d (i : Fin 2) := pulled_field_derivative z J V (e.X i) t dz jac.2 jac.1 (diff i)
  constructor
  · have dx := d 0
    rw [bracket,VectorField.lieBracket_swap (V := e.X 1) (W := e.X 0)] at dx
    simpa using dx
  · have dx := d 1
    rw [bracket] at dx
    simpa using dx

#print axioms transported_frame_values

section Tangent
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def tangentLift (X : E → E) (p : E × E) : E × E := (X p.1,fderiv ℝ X p.1 p.2)

theorem tangent_derivative (X : E → E) (x v : E) (hX : ContDiffAt ℝ 2 X x) (a b : E) :
    fderiv ℝ (tangentLift X) (x,v) (a,b) =
      (fderiv ℝ X x a, fderiv ℝ X x b + fderiv ℝ (fderiv ℝ X) x a v) := by
  have d := (hX.differentiableAt (by norm_num)).hasFDerivAt.comp (x,v) (hasFDerivAt_fst (𝕜 := ℝ))
  have d2 := ((hX.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have c := ((d2.comp (x,v) (hasFDerivAt_fst (𝕜 := ℝ))).clm_apply (hasFDerivAt_snd (𝕜 := ℝ)))
  exact congrArg (fun L : E × E →L[ℝ] E × E => L (a,b)) (d.prodMk c).fderiv

/-- The Lie bracket of the tangent lifts is the lift of the actual bracket.
Thus the transported-value computation on the tangent bundle also handles
the first spatial derivative, once the tangent flow has been identified. -/
theorem tangentLift_bracket (X Y : E → E) (x v : E) (hX : ContDiffAt ℝ 2 X x) (hY : ContDiffAt ℝ 2 Y x) :
    VectorField.lieBracket ℝ (tangentLift X) (tangentLift Y) (x,v) =
      tangentLift (VectorField.lieBracket ℝ X Y) (x,v) := by
  have dx := (hX.differentiableAt (by norm_num)).hasFDerivAt
  have dy := (hY.differentiableAt (by norm_num)).hasFDerivAt
  have d2x := ((hX.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have d2y := ((hY.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have db := (d2y.clm_apply dx).sub (d2x.clm_apply dy)
  change fderiv ℝ (tangentLift Y) (x,v) (X x,fderiv ℝ X x v) -
    fderiv ℝ (tangentLift X) (x,v) (Y x,fderiv ℝ Y x v) = _
  rw [tangent_derivative Y x v hY,tangent_derivative X x v hX]
  apply Prod.ext
  · rfl
  · change _ = fderiv ℝ ((fun y => fderiv ℝ Y y (X y)) - fun y => fderiv ℝ X y (Y y)) x v
    rw [db.fderiv]
    simp only [Prod.snd_sub,ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply]
    rw [hY.isSymmSndFDerivAt (by norm_num) (X x) v,hX.isSymmSndFDerivAt (by norm_num) (Y x) v]

#print axioms tangentLift_bracket

/-- The tangent map of a twice differentiable local coordinate change
sends the lift of the pulled-back field to the lift of the original field.
This identifies the spatial first derivative, as well as the field value. -/
theorem tangentLift_pullback [CompleteSpace E] (φ X : E → E) (x v : E)
    (smooth : ContDiffAt ℝ 2 φ x) (inv : (fderiv ℝ φ x).IsInvertible)
    (dx : DifferentiableAt ℝ X (φ x)) :
    fderiv ℝ (tangentLift φ) (x,v) (tangentLift (VectorField.pullback ℝ φ X) (x,v)) =
      tangentLift X (tangentLift φ (x,v)) := by
  let Y := VectorField.pullback ℝ φ X
  have dφ := smooth.differentiableAt (by norm_num)
  obtain ⟨N,_,ci,near,_⟩ := exists_continuousLinearEquiv_fderiv_symm_eq smooth inv
  have dY : DifferentiableAt ℝ Y x := by
    apply ((ci.differentiableAt (by norm_num)).clm_apply (dx.comp x dφ)).congr_of_eventuallyEq
    filter_upwards [near] with y hy
    change (fderiv ℝ φ y).inverse (X (φ y)) = (N y).symm (X (φ y))
    rw [← hy,ContinuousLinearMap.inverse_equiv]; rfl
  have id : (fun y => fderiv ℝ φ y (Y y)) =ᶠ[𝓝 x] X ∘ φ := by
    filter_upwards [near] with y hy
    exact VectorField.fderiv_pullback φ X y ⟨N y,hy⟩
  have d := ((smooth.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt.clm_apply dY.hasFDerivAt
  have d2 := dx.hasFDerivAt.comp x dφ.hasFDerivAt
  have eq := congrArg (fun A : E →L[ℝ] E => A v) ((d.congr_of_eventuallyEq id.symm).unique d2)
  change fderiv ℝ (tangentLift φ) (x,v) (Y x,fderiv ℝ Y x v) = _
  rw [tangent_derivative φ x v smooth]
  apply Prod.ext
  · exact VectorField.fderiv_pullback φ X x inv
  · change _ + _ = fderiv ℝ X (φ x) (fderiv ℝ φ x v)
    rw [smooth.isSymmSndFDerivAt (by norm_num) (Y x) v]
    exact eq

#print axioms tangentLift_pullback
end Tangent
end MinimizingSard.Five
