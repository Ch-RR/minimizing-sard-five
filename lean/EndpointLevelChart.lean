import ReducedEndpointNull
import IntrinsicHessianTransport
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Fix the regular endpoint coordinates while retaining every first-order
kernel variation and the true restricted second derivatives. -/
noncomputable section
open Set Filter
open scoped Topology
namespace MinimizingSard.Reduced
variable {U W : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- Local coordinates for the observable level set, with a prescribed
derivative equal to the inclusion of the entire kernel of the observation. -/
theorem level_chart (F : U → W) (smooth : ContDiffAt ℝ 4 F 0)
    (onto : Function.Surjective (fderiv ℝ F 0)) :
    let K := LinearMap.ker (fderiv ℝ F 0).toLinearMap
    ∃ S : K → U, S 0 = 0 ∧ ContDiffAt ℝ 4 S 0 ∧
      HasFDerivAt S K.subtypeL 0 ∧ ∀ᶠ v in 𝓝 0, F (S v) = F 0 := by
  let A := fderiv ℝ F 0
  let K := LinearMap.ker A.toLinearMap
  obtain ⟨R,hR⟩ := A.exists_right_inverse_of_surjective (LinearMap.range_eq_top.mpr onto)
  have right (y : W) : A (R y) = y := DFunLike.congr_fun hR y
  let H (u : U) := u + R (F u-F 0-A u)
  have H0 : H 0 = 0 := by simp [H]
  have df : HasFDerivAt F A 0 := (smooth.differentiableAt (by decide)).hasFDerivAt
  let I := ContinuousLinearEquiv.refl ℝ U
  have dh : HasFDerivAt H (I : U →L[ℝ] U) 0 := by
    have dg := (df.sub_const (F 0)).sub (A.hasFDerivAt (x := 0))
    convert (hasFDerivAt_id (0:U)).add (R.hasFDerivAt.comp 0 dg) using 1
    ext v
    simp [I]
  have ch : ContDiffAt ℝ 4 H 0 := contDiffAt_id.add (R.contDiff.contDiffAt.comp 0 ((smooth.sub contDiffAt_const).sub A.contDiff.contDiffAt))
  let T := ch.toOpenPartialHomeomorph H dh (by decide)
  have src : (0:U) ∈ T.source := ch.mem_toOpenPartialHomeomorph_source dh (by decide)
  have inv : ContDiffAt ℝ 4 T.symm (H 0) := ch.to_localInverse dh (by decide)
  have dinv : HasFDerivAt T.symm (I.symm : U →L[ℝ] U) (H 0) :=
    (ch.hasStrictFDerivAt' dh (by decide)).to_localInverse.hasFDerivAt
  have left : T.symm (H 0) = 0 := T.left_inv src
  rw [H0] at inv dinv left
  let S := T.symm ∘ K.subtypeL
  refine ⟨S,by simp [S,left],inv.comp 0 K.subtypeL.contDiff.contDiffAt,
    dinv.comp 0 K.subtypeL.hasFDerivAt,?_⟩
  have zero : (0:U) ∈ T.target := H0 ▸ T.map_source src
  have near : ∀ᶠ v : K in 𝓝 0, (v:U) ∈ T.target :=
    K.subtypeL.continuous.continuousAt (T.open_target.mem_nhds zero)
  filter_upwards [near] with v hv
  have hit : H (S v) = (v:U) := T.right_inv hv
  have eq := congrArg A hit
  change A (S v+R (F (S v)-F 0-A (S v))) = A v at eq
  have vanish : A v = 0 := v.property
  rw [map_add,right,vanish] at eq
  exact sub_eq_zero.mp (by linear_combination (norm := abel) eq)

omit [CompleteSpace U] in
/-- Scalar Hessians on the new level chart agree with the corresponding
restrictions of the full endpoint Hessians when the first scalar row vanishes. -/
theorem restricted_hessian {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    (S : K → U) (P : U → ℝ) (s0 : S 0 = 0) (cs : ContDiffAt ℝ 2 S 0)
    (cp : ContDiffAt ℝ 2 P 0) (p1 : fderiv ℝ P 0 = 0) (v w : K) :
    fderiv ℝ (fderiv ℝ (P ∘ S)) 0 v w =
      fderiv ℝ (fderiv ℝ P) 0 (fderiv ℝ S 0 v) (fderiv ℝ S 0 w) := by
  have cp' : ContDiffAt ℝ 2 P (S 0) := s0.symm ▸ cp
  simpa [s0] using Transport.intrinsic_second_variation S P id 0 v w
    (ContinuousLinearMap.id ℝ ℝ) cs cp' contDiffAt_id (by simp [s0,p1]) (by simp [s0,p1])

#print axioms level_chart
#print axioms restricted_hessian

set_option maxHeartbeats 500000 in
/-- Construct the reduced model from an unreduced endpoint in adapted
coordinates. The Hessian and the strict descent test are evaluated on the
original controls, and the competitor comparison is pulled back to the level set. -/
theorem germ_of_endpoint (F : U → W) (P Q J : U → ℝ) (V : Ambient → ℝ) (p : Ambient)
    (smooth : ContDiffAt ℝ 4 F 0) (onto : Function.Surjective (fderiv ℝ F 0))
    (hp : ContDiffAt ℝ 2 P 0) (hq : ContDiffAt ℝ 4 Q 0) (hj : ContDiffAt ℝ 1 J 0)
    (p0 : P 0 = 0) (q0 : Q 0 = 0) (j0 : J 0 = 0)
    (p1 : fderiv ℝ P 0 = 0) (q1 : fderiv ℝ Q 0 = 0)
    (qker : ∀ v w : LinearMap.ker (fderiv ℝ F 0).toLinearMap, fderiv ℝ (fderiv ℝ Q) 0 v w = 0)
    (prank : ∃ a b c d : LinearMap.ker (fderiv ℝ F 0).toLinearMap,
      fderiv ℝ (fderiv ℝ P) 0 a c * fderiv ℝ (fderiv ℝ P) 0 b d ≠
      fderiv ℝ (fderiv ℝ P) 0 a d * fderiv ℝ (fderiv ℝ P) 0 b c)
    (strict : ∃ v : LinearMap.ker (fderiv ℝ F 0).toLinearMap, fderiv ℝ J 0 v ≠ 0)
    (competitors : ∀ᶠ x in 𝓝 0, F x = F 0 →
        localValue V p (P x,Q x) ≤ localValue V p 0 + J x)
    (C : ℝ) (holder : ∀ᶠ z : ℝ × ℝ × ℝ in 𝓝 0,
      localValue V p (z.1,z.2.1) ≤ localValue V p (z.1,z.2.2) + C * |z.2.1-z.2.2|^(1/4:ℝ)) :
    Nonempty (Germ (LinearMap.ker (fderiv ℝ F 0).toLinearMap) V p) := by
  let K := LinearMap.ker (fderiv ℝ F 0).toLinearMap
  obtain ⟨S,s0,cs,ds,level⟩ := level_chart F smooth onto
  have dS : fderiv ℝ S 0 = K.subtypeL := ds.fderiv
  have comp1 (R : U → ℝ) (hs : DifferentiableAt ℝ R 0) :
      fderiv ℝ (R ∘ S) 0 = (fderiv ℝ R 0).comp K.subtypeL := by
    rw [fderiv_comp 0 (s0.symm ▸ hs) ds.differentiableAt,s0,dS]
  have hess (R : U → ℝ) (hs : ContDiffAt ℝ 2 R 0) (hz : fderiv ℝ R 0 = 0) (v w : K) :
      fderiv ℝ (fderiv ℝ (R ∘ S)) 0 v w = fderiv ℝ (fderiv ℝ R) 0 v w := by
    simpa only [dS,Submodule.subtypeL_apply] using restricted_hessian S R s0 (cs.of_le (by decide)) hs hz v w
  have js : fderiv ℝ (J ∘ S) 0 ≠ 0 := by
    obtain ⟨v,hv⟩ := strict
    intro eq
    have ident := comp1 J (hj.differentiableAt (by decide))
    exact hv (DFunLike.congr_fun (ident.symm.trans eq) v)
  refine ⟨{
    f := P ∘ S, g := Q ∘ S, cost := J ∘ S
    hf := (s0.symm ▸ hp).comp 0 (cs.of_le (by decide))
    hg := (s0.symm ▸ hq).comp 0 cs
    hc := (s0.symm ▸ hj).comp 0 (cs.of_le (by decide))
    f0 := by simp [s0,p0]
    f1 := by rw [comp1 P (hp.differentiableAt (by decide)),p1]; rfl
    g0 := by simp [s0,q0]
    g1 := by rw [comp1 Q (hq.differentiableAt (by decide)),q1]; rfl
    g2 := by ext v w; exact (hess Q (hq.of_le (by decide)) q1 v w).trans (qker v w)
    rank := ?_, cz := by simp [s0,j0]
    strict := js, competitors := ?_, K := C, holder := holder }⟩
  · obtain ⟨a,b,c,d,ne⟩ := prank
    have ident (v w : K) : Return.polarRow (P ∘ S) 1 v w = fderiv ℝ (fderiv ℝ P) 0 v w := by
      simpa [Return.polarRow] using hess P hp p1 v w
    exact ⟨a,b,c,d,by simpa only [ident] using ne⟩
  · have near : Tendsto S (𝓝 0) (𝓝 0) := by simpa only [s0] using cs.continuousAt.tendsto
    filter_upwards [near competitors,level] with x hx eq using hx eq

#print axioms germ_of_endpoint

/-- Exclude a surjective quadratic polar on the full observable kernel
at almost every ambient point. The exceptional set is independent of
the chosen observable, endpoint rows, cost and test vector. -/
theorem ae_no_regular_endpoint_polar (V : Ambient → ℝ) (hV : Continuous V) :
    ∀ᵐ p : Ambient, ∀ (F : U → W) (P Q J : U → ℝ),
      ContDiffAt ℝ 4 F 0 → Function.Surjective (fderiv ℝ F 0) →
      ContDiffAt ℝ 2 P 0 → ContDiffAt ℝ 2 Q 0 → ContDiffAt ℝ 1 J 0 →
      P 0 = 0 → Q 0 = 0 → J 0 = 0 → fderiv ℝ P 0 = 0 → fderiv ℝ Q 0 = 0 →
      (∃ v : LinearMap.ker (fderiv ℝ F 0).toLinearMap, fderiv ℝ J 0 v ≠ 0) →
      (∀ᶠ x in 𝓝 0, F x = F 0 → localValue V p (P x,Q x) ≤ localValue V p 0+J x) →
      ∀ h : LinearMap.ker (fderiv ℝ F 0).toLinearMap,
        ¬ Function.Surjective (fun a : LinearMap.ker (fderiv ℝ F 0).toLinearMap =>
          (fderiv ℝ (fderiv ℝ P) 0 h a,fderiv ℝ (fderiv ℝ Q) 0 h a)) := by
  filter_upwards [ae_no_regular_polar (fun L : Submodule ℝ U => ↥L) V hV] with p except
  intro F P Q J cf onto hp hq hj p0 q0 j0 p1 q1 strict competitors h sur
  let K := LinearMap.ker (fderiv ℝ F 0).toLinearMap
  obtain ⟨S,s0,cs,ds,level⟩ := level_chart F cf onto
  have dS : fderiv ℝ S 0 = K.subtypeL := ds.fderiv
  have comp1 (R : U → ℝ) (hs : DifferentiableAt ℝ R 0) :
      fderiv ℝ (R ∘ S) 0 = (fderiv ℝ R 0).comp K.subtypeL := by
    rw [fderiv_comp 0 (s0.symm ▸ hs) ds.differentiableAt,s0,dS]
  have hess (R : U → ℝ) (hs : ContDiffAt ℝ 2 R 0) (hz : fderiv ℝ R 0 = 0) (v w : K) :
      fderiv ℝ (fderiv ℝ (R ∘ S)) 0 v w = fderiv ℝ (fderiv ℝ R) 0 v w := by
    simpa only [dS,Submodule.subtypeL_apply] using restricted_hessian S R s0 (cs.of_le (by decide)) hs hz v w
  apply except K (P ∘ S) (Q ∘ S) (J ∘ S)
    ((s0.symm ▸ hp).comp 0 (cs.of_le (by decide))) ((s0.symm ▸ hq).comp 0 (cs.of_le (by decide)))
    ((s0.symm ▸ hj).comp 0 (cs.of_le (by decide))) (by simp [s0,p0])
    (by rw [comp1 P (hp.differentiableAt (by decide)),p1]; rfl) (by simp [s0,q0])
    (by rw [comp1 Q (hq.differentiableAt (by decide)),q1]; rfl) (by simp [s0,j0]) _ _ h
  · intro y
    obtain ⟨v,hv⟩ := sur y
    exact ⟨v,(congrArg₂ Prod.mk (hess P hp p1 h v) (hess Q hq q1 h v)).trans hv⟩
  · obtain ⟨v,hv⟩ := strict
    intro eq
    exact hv (DFunLike.congr_fun ((comp1 J (hj.differentiableAt (by decide))).symm.trans eq) v)
  · have near : Tendsto S (𝓝 0) (𝓝 0) := by simpa only [s0] using cs.continuousAt.tendsto
    filter_upwards [near competitors,level] with x hx eq using hx eq

#print axioms ae_no_regular_endpoint_polar
end MinimizingSard.Reduced
