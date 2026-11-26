import FrameGeneratorWord
import Mathlib.Analysis.ODE.PicardLindelof

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff
namespace MinimizingSard.Five
open Volterra

/-- A smooth map with invertible derivative has a local inverse smooth on
a neighborhood, with a single neighborhood valid for every derivative order. -/
theorem smooth_inverse_neighborhood {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : E → E) (x : E) (e : E ≃L[ℝ] E)
    (smooth : ∀ᶠ z in 𝓝 x, ContDiffAt ℝ ∞ f z) (df : HasFDerivAt f e.toContinuousLinearMap x) :
    ∃ T : OpenPartialHomeomorph E E, (T : E → E) = f ∧ x ∈ T.source ∧
      ∀ᶠ z in 𝓝 (f x), ContDiffAt ℝ ∞ T.symm z := by
  have cf := smooth.self_of_nhds
  let T := cf.toOpenPartialHomeomorph f df (by decide)
  have mem := cf.mem_toOpenPartialHomeomorph_source df (by decide)
  have unit : IsUnit (fderiv ℝ f x) := by
    rw [df.fderiv]
    exact ⟨⟨e,e.symm,ContinuousLinearMap.ext fun z => e.apply_symm_apply z,
      ContinuousLinearMap.ext fun z => e.symm_apply_apply z⟩,rfl⟩
  have near := (cf.fderiv_right (m := 0) (by decide)).continuousAt.tendsto (Units.isOpen.mem_nhds unit)
  have lim : Tendsto T.symm (𝓝 (f x)) (𝓝 x) := by
    simpa only [T.left_inv (show x ∈ T.source from mem)] using T.symm.continuousAt (T.map_source mem) |>.tendsto
  refine ⟨T,rfl,mem,?_⟩
  filter_upwards [lim near,lim smooth,T.open_target.mem_nhds (T.map_source mem)] with z hz sm inside
  obtain ⟨a,eq⟩ := hz
  have inv : (fderiv ℝ f (T.symm z)).IsInvertible := eq ▸ ContinuousLinearMap.IsInvertible.of_inverse a.mul_inv a.inv_mul
  obtain ⟨A,hA⟩ := inv
  change ContDiffAt ℝ ∞ f (T.symm z) at sm
  exact T.contDiffAt_symm inside (hA.symm ▸ (sm.differentiableAt (by decide)).hasFDerivAt) sm

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

abbrev ClockPath (F : Type) [TopologicalSpace F] := C(Time,F)
def integralPath : (ClockPath F) →L[ℝ] (ClockPath F) := by
  let m : (ClockPath F) →ₗ[ℝ] (ClockPath F) := {
    toFun := fun p => ⟨fun t => ∫ s in (0:ℝ)..(t:ℝ), p (clamp s),
      (intervalIntegral.continuous_primitive (fun a b => (p.continuous.comp continuous_projIcc).intervalIntegrable a b) 0).comp continuous_subtype_val⟩
    map_add' := fun p q => by
      ext t : 1
      exact intervalIntegral.integral_add ((p.continuous.comp continuous_projIcc).intervalIntegrable ..)
        ((q.continuous.comp continuous_projIcc).intervalIntegrable ..)
    map_smul' := fun c p => by ext t : 1; exact intervalIntegral.integral_smul c _
  }
  apply m.mkContinuous 1
  intro p
  rw [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro t
  change ‖∫ s in (0:ℝ)..(t:ℝ), p (clamp s)‖ ≤ _
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := (t:ℝ))
    (fun s _ => p.norm_coe_le_norm (clamp s))
  simpa [abs_of_nonneg t.2.1] using h.trans (by
    rw [sub_zero,abs_of_nonneg t.2.1]; exact mul_le_of_le_one_right (norm_nonneg _) t.2.2)

private def trajectoryIntegral (V : F → F) (hV : ContDiff ℝ ∞ V) (q : F) (z : (ClockPath F)) : (ClockPath F) :=
  integralPath (PathCalculus.subst (liftField V hV.continuous) (ContinuousMap.const Time q + z))

omit [CompleteSpace F] in
private theorem integral_smooth (V : F → F) (hV : ContDiff ℝ ∞ V) (q : F) :
    ContDiff ℝ ∞ (trajectoryIntegral V hV q) := by
  apply contDiff_infty.mpr
  intro n
  have N := PathCalculus.contDiff_subst_of_spatialOrder n _
    (field_order n V (contDiff_infty.mp hV n))
  exact integralPath.contDiff.comp (N.comp (contDiff_const.add contDiff_id))

omit [NormedSpace ℝ F] [CompleteSpace F] in
/-- Uniformly shrink a time interval to the unit interval on the original
clock, allowing both signs of the elapsed time. -/
private theorem uniform_rescale {q : F} {P : F × ℝ → Prop} (near : ∀ᶠ p in 𝓝 (q,0), P p) :
    ∀ᶠ p : F × ℝ in 𝓝 (q,0), ∀ s ∈ Icc (0:ℝ) 1, P (p.1,s*p.2) := by
  obtain ⟨r,hr,ball⟩ := Metric.mem_nhds_iff.mp near
  filter_upwards [Metric.ball_mem_nhds (q,(0:ℝ)) hr] with p hp
  intro s hs
  apply ball
  simp only [Metric.mem_ball,Prod.dist_eq,Real.dist_eq,sub_zero,max_lt_iff] at hp ⊢
  exact ⟨hp.1,(by rw [abs_mul,abs_of_nonneg hs.1]; exact (mul_le_of_le_one_left (abs_nonneg _) hs.2).trans_lt hp.2)⟩


/-- A single path-space solution operator is smooth throughout a neighborhood,
and identifies every sufficiently small solution of the integral equation. -/
private theorem implicit_clock {U Z : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z] (A : Z → U →L[ℝ] Z)
    (ca : ContDiff ℝ ∞ A) :
    ∃ S : U → Z, (∀ᶠ u in 𝓝 0, ContDiffAt ℝ ∞ S u) ∧
      ∃ r > 0, ∀ᶠ u in 𝓝 0, ∀ z, ‖z‖ < r → z = A z u → z = S u := by
  let H (p : U × Z) := (p.1,p.2 - (A p.2 - A 0) p.1)
  have hz : H 0 = 0 := by simp [H]
  have reg : ContDiff ℝ ∞ (fun p : U × Z => A p.2 - A 0) := (ca.comp contDiff_snd).sub contDiff_const
  have ch : ContDiff ℝ ∞ H := contDiff_fst.prodMk (contDiff_snd.sub (reg.clm_apply contDiff_fst))
  let e := ContinuousLinearEquiv.refl ℝ (U × Z)
  have dh : HasFDerivAt H (e : (U × Z) →L[ℝ] (U × Z)) 0 := by
    have a := ((reg.differentiable (by decide)) 0).hasFDerivAt.clm_apply (hasFDerivAt_fst (𝕜 := ℝ) (p := (0 : U × Z)))
    have b := (hasFDerivAt_fst (𝕜 := ℝ) (p := (0 : U × Z))).prodMk
      ((hasFDerivAt_snd (𝕜 := ℝ) (p := (0 : U × Z))).sub a)
    convert b using 1
    ext v <;> simp [e]
  obtain ⟨T,te,src,smooth⟩ := smooth_inverse_neighborhood H 0 e (.of_forall fun _ => ch.contDiffAt) dh
  let g (u : U) := (u,A 0 u)
  have cg : ContDiff ℝ ∞ g := contDiff_id.prodMk (A 0).contDiff
  have push : Tendsto g (𝓝 0) (𝓝 (H 0)) := by simpa [g,hz] using cg.continuous.tendsto (0:U)
  obtain ⟨r,rp,ball⟩ := Metric.mem_nhds_iff.mp (T.open_source.mem_nhds src)
  refine ⟨fun u => (T.symm (g u)).2,?_,r,rp,?_⟩
  · filter_upwards [push smooth] with u hu
    change ContDiffAt ℝ ∞ T.symm (g u) at hu
    exact contDiffAt_snd.comp u (hu.comp u cg.contDiffAt)
  · filter_upwards [Metric.ball_mem_nhds (0:U) rp] with u hu
    intro z small eq
    have mem : (u,z) ∈ T.source := ball (by
      simpa [Metric.mem_ball,Prod.dist_eq] using And.intro (show ‖u‖ < r by simpa [Metric.mem_ball] using hu) small)
    have hit : T (u,z) = g u := by
      rw [te]
      simp [H,g,ContinuousLinearMap.sub_apply,← eq]
    exact (congrArg Prod.snd ((congrArg T.symm hit).symm.trans (T.left_inv mem))).symm

private theorem continuous_clock (V : F → F) (hV : ContDiff ℝ ∞ V) (q : F) :
    ∃ f : F × ℝ → F, f (q,0) = q ∧ ContinuousAt f (q,0) ∧
      ∀ᶠ p : F × ℝ in 𝓝 (q,0), f (p.1,0) = p.1 ∧
        HasDerivAt (fun s => f (p.1,s)) (V (f p)) p.2 := by
  obtain ⟨ε,hε,a,r,L,K,hr,pl⟩ := IsPicardLindelof.of_contDiffAt_one
    (hV.contDiffAt.of_le (by decide) : ContDiffAt ℝ 1 V q) (0:ℝ)
  obtain ⟨f,ode,cont⟩ := pl.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  have openN : closedBall q (r:ℝ) ×ˢ Ioo (0-ε) (0+ε) ∈ 𝓝 (q,0) :=
    prod_mem_nhds (Metric.closedBall_mem_nhds _ (by exact_mod_cast hr)) (Ioo_mem_nhds (by linarith) (by linarith))
  have closedN : closedBall q (r:ℝ) ×ˢ Icc (0-ε) (0+ε) ∈ 𝓝 (q,0) :=
    mem_of_superset openN (Set.prod_mono Subset.rfl Ioo_subset_Icc_self)
  refine ⟨f,(ode q (mem_closedBall_self r.coe_nonneg)).1,cont.continuousAt closedN,?_⟩
  filter_upwards [openN] with p hp
  exact ⟨(ode _ hp.1).1,((ode _ hp.1).2 _ (Ioo_subset_Icc_self hp.2)).hasDerivAt
    (Icc_mem_nhds hp.2.1 hp.2.2)⟩


/-- Jointly smooth local flow for a smooth autonomous Euclidean field. Both
the ODE and the smoothness hold near the initial point on a common domain. -/
theorem smooth_short_flow (V : F → F) (hV : ContDiff ℝ ∞ V) (q : F) :
    ∃ f : F × ℝ → F, ∀ᶠ p : F × ℝ in 𝓝 (q,0),
      ContDiffAt ℝ ∞ f p ∧ f (p.1,0) = p.1 ∧ HasDerivAt (fun s => f (p.1,s)) (V (f p)) p.2 := by
  obtain ⟨f,f0,cf,ode⟩ := continuous_clock V hV q
  let N := trajectoryIntegral V hV q
  let ins : F →L[ℝ] (ClockPath F) := ContinuousLinearMap.const ℝ Time
  let A (w : (ClockPath F)) := (ins.comp (ContinuousLinearMap.fst ℝ F ℝ)) +
    (ContinuousLinearMap.snd ℝ F ℝ).smulRight (N w)
  have cA : ContDiff ℝ ∞ A := contDiff_const.add (contDiff_const.smulRight (integral_smooth V hV q))
  obtain ⟨S,smooth,r,rp,unique⟩ := implicit_clock A cA
  let tr (p : F × ℝ) := (p.1-q,p.2)
  have t0 : tr (q,0) = 0 := by simp [tr]
  have ct : ContDiff ℝ ∞ tr := (contDiff_fst.sub contDiff_const).prodMk contDiff_snd
  have push : Tendsto tr (𝓝 (q,0)) (𝓝 0) := t0 ▸ ct.continuous.tendsto (q,0)
  let evalEnd : (ClockPath F) →L[ℝ] F := ContinuousMap.evalCLM ℝ (clamp 1)
  let model (p : F × ℝ) := q + evalEnd (S (tr p))
  have small : ∀ᶠ p in 𝓝 (q,(0:ℝ)), ‖f p - q‖ < r :=
    (cf.sub continuousAt_const).norm.eventually_lt_const (by simpa [f0] using rp)
  have agrees : f =ᶠ[𝓝 (q,0)] model := by
    filter_upwards [uniform_rescale ode,uniform_rescale small,push unique] with p hp close onlySmall
    let z (s : ℝ) := f (p.1,s*p.2)
    have dz (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : HasDerivAt z (p.2 • V (z s)) s := by
      simpa [z] using (hp s hs).2.scomp s ((hasDerivAt_id s).mul_const p.2)
    have cz : ContinuousOn z (Icc (0:ℝ) 1) := fun s hs => (dz s hs).continuousAt.continuousWithinAt
    let w : (ClockPath F) := ⟨fun s => z s-q, (continuousOn_iff_continuous_restrict.mp cz).sub continuous_const⟩
    have tiny : ‖w‖ < r := (ContinuousMap.norm_lt_iff w rp).mpr (fun s => close _ s.property)
    have fp : w = A w (tr p) := by
      ext s : 1
      change z s-q = (p.1-q) + p.2 • ∫ t in (0:ℝ)..(s:ℝ), V (q + w (clamp t))
      have replace : (∫ t in (0:ℝ)..(s:ℝ), V (q + w (clamp t))) = ∫ t in (0:ℝ)..(s:ℝ), V (z t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le s.2.1] at ht
        have ht' : t ∈ Icc (0:ℝ) 1 := ⟨ht.1,ht.2.trans s.2.2⟩
        change V (q + (z (clamp t) - q)) = V (z t)
        rw [show clamp t = ⟨t,ht'⟩ from projIcc_of_mem _ ht']
        simp
      have z0 : z 0 = p.1 := by simpa [z] using (hp 0 (by constructor <;> norm_num)).1
      have sub : uIcc (0:ℝ) (s:ℝ) ⊆ Icc 0 1 := by rw [uIcc_of_le s.2.1]; exact Icc_subset_Icc_right s.2.2
      have it : IntervalIntegrable (fun t => p.2 • V (z t)) volume 0 s :=
        (((hV.continuous.comp_continuousOn cz).const_smul p.2).mono sub).intervalIntegrable
      have ft := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => dz t (sub ht)) it
      rw [replace,← intervalIntegral.integral_smul,ft,z0]
      abel
    have hw := onlySmall w tiny fp
    change f p = q + (S (tr p)) (clamp 1)
    rw [← hw]
    change f p = q + (f (p.1,(clamp 1:ℝ)*p.2)-q)
    simp [clamp]
  refine ⟨f,?_⟩
  filter_upwards [agrees.eventuallyEq_nhds,push smooth,ode] with p eq sm od
  change ContDiffAt ℝ ∞ S (tr p) at sm
  have cs : ContDiffAt ℝ ∞ model p := contDiffAt_const.add (evalEnd.contDiff.contDiffAt.comp p (sm.comp p ct.contDiffAt))
  exact ⟨cs.congr_of_eventuallyEq eq,od⟩

#print axioms smooth_short_flow

end MinimizingSard.Five
