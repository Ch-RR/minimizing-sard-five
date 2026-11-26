import PathSuperposition
import VolterraLocalization
import BanachControlEquation
import PulseEndpointGraph

/-! Dependence of the paths of the two-column moving-frame ODE on all
square-integrable controls. Only spatial derivatives of the fields are used. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology Interval
open MinimizingSard.Volterra
namespace MinimizingSard.PulseGeometry
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The two spatial derivatives on the closed time window. -/
structure SpatialJets (X : Columns E) where
  J : Fin 2 → C(Time × E,E →L[ℝ] E)
  H : Fin 2 → C(Time × E,E →L[ℝ] E →L[ℝ] E)
  first : ∀ i (t : Time) x, HasFDerivAt (X.Y i t) (J i (t,x)) x
  second : ∀ i (t : Time) x, HasFDerivAt (fun y => J i (t,y)) (H i (t,x)) x

private abbrev Input := Fin 2 → ℝ
def Columns.spatialField (X : Columns E) (i : Fin 2) : C(Time × E,E) :=
  ⟨fun p => X.Y i p.1 p.2, (X.continuous i).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)⟩

private def channel (i : Fin 2) : E →L[ℝ] Input →L[ℝ] E :=
  ContinuousLinearMap.smulRightL ℝ Input E (ContinuousLinearMap.proj i)

private def coefficient (X : Columns E) (q : E) (w : C(Time,E)) : C(Time,Input →L[ℝ] E) :=
  let z := ContinuousMap.const Time q + w
  (channel (E := E) 0).compLeftContinuous ℝ Time (PathCalculus.subst (X.spatialField 0) z) +
  (channel (E := E) 1).compLeftContinuous ℝ Time (PathCalculus.subst (X.spatialField 1) z)

private theorem coefficient_apply (X : Columns E) (q : E) (w : C(Time,E)) (t : Time) (a : Input) :
    coefficient X q w t a = X.velocity t (q + w t) a := rfl

private theorem smooth_coefficient (X : Columns E) (n : ℕ)
    (jets : ∀ i, PathCalculus.SpatialOrder n (X.spatialField i)) (q : E) :
    ContDiff ℝ n (coefficient X q) := by
  have shift : ContDiff ℝ n (fun w : C(Time,E) => ContinuousMap.const Time q + w) :=
    contDiff_const.add contDiff_id
  have each (i : Fin 2) : ContDiff ℝ n (fun w : C(Time,E) =>
      ((channel (E := E) i).compLeftContinuous ℝ Time)
        (PathCalculus.subst (X.spatialField i) (ContinuousMap.const Time q + w))) := by
    have c := PathCalculus.contDiff_subst_of_spatialOrder n (X.spatialField i) (jets i)
    have cm := @ContinuousLinearMap.contDiff ℝ _ C(Time,E) _ _ C(Time,Input →L[ℝ] E) _ _ n
      ((channel (E := E) i).compLeftContinuous ℝ Time)
    exact cm.comp (c.comp shift)
  exact (each 0).add (each 1)

/-- Every integral trajectory gives a fixed point in the sup-norm path space. -/
private theorem path_fixed (X : Columns E) (q : E) (u : Controls) (z : ℝ → E) (hz : X.Path q u z) :
    ∃ w : C(Time,E), (∀ t : Time, q + w t = z t) ∧
      w = operator Input E (coefficient X q w) u := by
  let zc : C(Time,E) := ⟨fun t => z t, continuousOn_iff_continuous_restrict.mp hz.1⟩
  let w := zc - ContinuousMap.const Time q
  have val (t : Time) : q + w t = z t := by change q + (z t - q) = z t; abel
  refine ⟨w,val,?_⟩
  ext t
  rw [operator_eq_interval]
  have same : (∫ s in (0 : ℝ)..(t : ℝ), (coefficient X q w (clamp s)) (u s)) =
      ∫ s in (0 : ℝ)..(t : ℝ), X.velocity s (z s) (u s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le t.2.1] at hs
    have hi : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1,hs.2.trans t.2.2⟩
    change (coefficient X q w (clamp s)) (u s) = X.velocity s (z s) (u s)
    rw [show clamp s = ⟨s,hi⟩ from projIcc_of_mem _ hi,coefficient_apply,val]
  rw [same]
  exact add_left_cancel ((val t).trans (hz.2.2 t t.2))

variable [CompleteSpace E]

/-- A finite-order differentiable selection of actual integral trajectories on a full L²
neighborhood of zero. Evaluation of these paths realizes any representative
of the ODE endpoint there. -/
theorem path_family_of_spatialOrder (X : Columns E) (n : ℕ) (hn : 1 ≤ (n : WithTop ℕ∞))
    (jets : ∀ i, PathCalculus.SpatialOrder n (X.spatialField i)) (q : E) :
    ∃ S : Controls → C(Time,E), S 0 = 0 ∧ ContDiffAt ℝ n S 0 ∧
      ∀ᶠ u in 𝓝 0, X.Path q u (fun t => q + S u (clamp t)) ∧
        ∀ z : ℝ → E, X.Path q u z → ∀ t : Time, z t = q + S u t := by
  let A (w : C(Time,E)) := Volterra.operator Input E (coefficient X q w)
  have cm := @ContinuousLinearMap.contDiff ℝ _ C(Time,Input →L[ℝ] E) _ _ (Controls →L[ℝ] C(Time,E)) _ _ n
    (Volterra.operator Input E)
  have ca : ContDiff ℝ n A := cm.comp (smooth_coefficient X n jets q)
  obtain ⟨S,h0,cs,eq,r,hr,unique⟩ := ImplicitControl.local_solution A
    hn ca.contDiffAt
  have localC (w z : C(Time,E)) (t : Time) (same : w t = z t) :
      coefficient X q w t = coefficient X q z t := by
    ext a
    rw [coefficient_apply,coefficient_apply,same]
  have trap := Volterra.fixed_paths_small (coefficient X q) (smooth_coefficient X n jets q).continuous.continuousAt
    localC hr
  refine ⟨S,h0,cs,?_⟩
  filter_upwards [eq,unique,trap] with u hu onlyFixed small
  have uniquePath (z : ℝ → E) (hz : X.Path q u z) (t : Time) : z t = q + S u t := by
    obtain ⟨w,val,fixed⟩ := path_fixed X q u z hz
    exact (val t).symm.trans (congrArg (fun v : C(Time,E) => q + v t) (onlyFixed w (small w fixed) fixed))
  refine ⟨?_,uniquePath⟩
  let B := coefficient X q (S u)
  have agrees (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      B (clamp s) (u s) = X.velocity s (q + S u (clamp s)) (u s) := by
    rw [show clamp s = ⟨s,hs⟩ from projIcc_of_mem _ hs]
    rfl
  refine ⟨(continuous_const.add ((S u).continuous.comp continuous_projIcc)).continuousOn,?_,?_⟩
  · apply (intervalIntegrable_congr (f := fun s => B (clamp s) (u s)) ?_).mp (Volterra.intervalIntegrable B u)
    intro s hs
    rw [uIoc_of_le zero_le_one] at hs
    exact agrees s ⟨hs.1.le,hs.2⟩
  · intro t ht
    have h := congrArg (fun w : C(Time,E) => w ⟨t,ht⟩) hu
    change S u ⟨t,ht⟩ = Volterra.operator Input E B u ⟨t,ht⟩ at h
    rw [operator_eq_interval] at h
    apply congrArg (q + ·)
    rw [show clamp t = ⟨t,ht⟩ from projIcc_of_mem _ ht,h]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    exact agrees s ⟨hs.1,hs.2.trans ht.2⟩

theorem smooth_path_family (X : Columns E) (jets : SpatialJets X) (q : E) :
    ∃ S : Controls → C(Time,E), S 0 = 0 ∧ ContDiffAt ℝ 2 S 0 ∧
      ∀ᶠ u in 𝓝 0, X.Path q u (fun t => q + S u (clamp t)) ∧
        ∀ z : ℝ → E, X.Path q u z → ∀ t : Time, z t = q + S u t :=
  path_family_of_spatialOrder X 2 (by norm_num)
    (fun i => ⟨jets.J i,jets.first i,jets.H i,jets.second i,trivial⟩) q

theorem endpoint_of_spatialOrder (X : Columns E) (n : ℕ) (hn : 1 ≤ (n : WithTop ℕ∞))
    (jets : ∀ i, PathCalculus.SpatialOrder n (X.spatialField i)) (q : E)
    (F : Controls → E) (endpoint : X.Endpoint q F) : ContDiffAt ℝ n F 0 := by
  obtain ⟨S,_,cs,paths⟩ := path_family_of_spatialOrder X n hn jets q
  have eval : ContDiffAt ℝ n (fun u => q + S u (clamp 1)) 0 :=
    contDiffAt_const.add ((@ContinuousLinearMap.contDiff ℝ _ C(Time,E) _ _ E _ _ n
      (ContinuousMap.evalCLM ℝ (clamp 1))).contDiffAt.comp 0 cs)
  apply eval.congr_of_eventuallyEq
  filter_upwards [endpoint,paths] with u hu hp
  exact hu _ hp.1

#print axioms path_family_of_spatialOrder
#print axioms endpoint_of_spatialOrder

theorem exists_smooth_integral_endpoint (X : Columns E) (jets : SpatialJets X) (q : E) :
    ∃ F : Controls → E, F 0 = q ∧ X.Endpoint q F ∧ ContDiffAt ℝ 2 F 0 := by
  obtain ⟨S,h0,cs,paths⟩ := smooth_path_family X jets q
  let t : Time := ⟨1,zero_le_one,le_rfl⟩
  refine ⟨fun u => q + S u t,by simp [h0],?_,?_⟩
  · filter_upwards [paths] with u hu
    exact fun z hz => (hu.2 z hz t).symm
  · exact contDiffAt_const.add ((@ContinuousLinearMap.contDiff ℝ _ C(Time,E) _ _ E _ _ 2
      (ContinuousMap.evalCLM ℝ t)).contDiffAt.comp 0 cs)

theorem smooth_integral_endpoint (X : Columns E) (jets : SpatialJets X) (q : E)
    (F : Controls → E) (endpoint : X.Endpoint q F) : ContDiffAt ℝ 2 F 0 := by
  obtain ⟨S,_,cs,paths⟩ := smooth_path_family X jets q
  have eval : ContDiffAt ℝ 2 (fun u => q + S u (clamp 1)) 0 :=
    contDiffAt_const.add ((@ContinuousLinearMap.contDiff ℝ _ C(Time,E) _ _ E _ _ 2
      (ContinuousMap.evalCLM ℝ (clamp 1))).contDiffAt.comp 0 cs)
  apply eval.congr_of_eventuallyEq
  filter_upwards [endpoint,paths] with u hu hp
  exact hu _ hp.1

#print axioms smooth_path_family
#print axioms exists_smooth_integral_endpoint
#print axioms smooth_integral_endpoint

/-- The initial state and every L² control channel vary jointly. At
small references this gives spatial derivatives of the actual time
dependent flow as a sup-norm path, uniformly on the whole time interval. -/
theorem joint_path_family (X : Columns E) (n : ℕ) (hn : 1 ≤ (n : WithTop ℕ∞))
    (jets : ∀ i, PathCalculus.SpatialOrder n (X.spatialField i)) (q : E) :
    ∃ S : E × Controls → C(Time,E), S 0 = 0 ∧ ContDiffAt ℝ n S 0 ∧
      ∀ᶠ p : E × Controls in 𝓝 0,
        X.Path (q+p.1) p.2 (fun t => q+S p (clamp t)) ∧
        ∀ z : ℝ → E, X.Path (q+p.1) p.2 z → ∀ t : Time, z t = q+S p t := by
  let ins : E →L[ℝ] C(Time,E) := ContinuousLinearMap.const ℝ Time
  let fst := ContinuousLinearMap.fst ℝ E Controls
  let snd := ContinuousLinearMap.snd ℝ E Controls
  let A (w : C(Time,E)) := (ins.comp fst) +
    ((Volterra.operator Input E (coefficient X q w)).comp snd)
  have cm := @ContinuousLinearMap.contDiff ℝ _ C(Time,Input →L[ℝ] E) _ _ (Controls →L[ℝ] C(Time,E)) _ _ n
    (Volterra.operator Input E)
  have ca : ContDiff ℝ n A :=
    contDiff_const.add ((cm.comp (smooth_coefficient X n jets q)).clm_comp contDiff_const)
  obtain ⟨S,s0,cs,eq,R,hR,unique⟩ := ImplicitControl.local_solution A hn ca.contDiffAt
  let C (a : E) (w : C(Time,E)) := coefficient X q (ins a+w)
  have cC : ContDiff ℝ n (fun p : E × C(Time,E) => C p.1 p.2) :=
    (smooth_coefficient X n jets q).comp ((ins.contDiff.comp contDiff_fst).add contDiff_snd)
  have pt (a : E) (w z : C(Time,E)) (t : Time) (same : w t = z t) : C a w t = C a z t := by
    ext v
    simp only [C,coefficient_apply,ContinuousMap.add_apply,same]
  have trap := Volterra.fixed_paths_small_with_parameter C cC.continuous.continuousAt pt (half_pos hR)
  have transfer (a : E) (w : C(Time,E)) : coefficient X (q+a) w = C a w := by
    ext t v
    simp only [C,coefficient_apply,ContinuousMap.add_apply,add_assoc]
    rfl
  have small : ∀ᶠ p : E × Controls in 𝓝 0, ‖ins p.1‖ < R/2 :=
    (ins.continuous.comp continuous_fst).continuousAt.norm.eventually_lt continuousAt_const (by simpa using half_pos hR)
  refine ⟨S,s0,cs,?_⟩
  filter_upwards [eq,unique,trap,small] with p fp onlyFixed stay tiny
  change S p = ins p.1 + Volterra.operator Input E (coefficient X q (S p)) p.2 at fp
  let B := coefficient X q (S p)
  have agrees (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      B (clamp s) (p.2 s) = X.velocity s (q+S p (clamp s)) (p.2 s) := by
    rw [show clamp s = ⟨s,hs⟩ from projIcc_of_mem _ hs]
    rfl
  constructor
  · refine ⟨(continuous_const.add ((S p).continuous.comp continuous_projIcc)).continuousOn,?_,?_⟩
    · apply (intervalIntegrable_congr (f := fun s => B (clamp s) (p.2 s)) ?_).mp (Volterra.intervalIntegrable B p.2)
      intro s hs
      rw [uIoc_of_le zero_le_one] at hs
      exact agrees s ⟨hs.1.le,hs.2⟩
    · intro t ht
      have heq := congrArg (fun v : C(Time,E) => v ⟨t,ht⟩) fp
      change S p ⟨t,ht⟩ = p.1 + Volterra.operator Input E B p.2 ⟨t,ht⟩ at heq
      rw [operator_eq_interval] at heq
      change q + S p (clamp t) = _
      rw [show clamp t = ⟨t,ht⟩ from projIcc_of_mem _ ht,heq,← add_assoc]
      apply congrArg ((q+p.1)+ ·)
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le ht.1] at hs
      exact agrees s ⟨hs.1,hs.2.trans ht.2⟩
  · intro z hz t
    obtain ⟨w,val,fixed⟩ := path_fixed X (q+p.1) p.2 z hz
    rw [transfer] at fixed
    have bound := stay w fixed
    have smallW : ‖ins p.1+w‖ < R :=
      (norm_add_le _ _).trans_lt (by linarith only [tiny,bound])
    have fixed' : ins p.1+w = A (ins p.1+w) p := congrArg (ins p.1+ ·) fixed
    have same := congrArg (fun W : C(Time,E) => q+W t) (onlyFixed _ smallW fixed')
    exact (val t).symm.trans (by simpa only [add_assoc] using same)

#print axioms joint_path_family

set_option maxHeartbeats 800000 in
private theorem hessian_apply_at_zero {U V : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : U → V) (B : U → U →L[ℝ] V) (q : V) (cb : ContDiffAt ℝ 2 B 0) (cf : ContDiffAt ℝ 2 F 0)
    (graph : F =ᶠ[𝓝 0] fun u => q + B u u) (h k : U) :
    fderiv ℝ (fderiv ℝ F) 0 h k = fderiv ℝ B 0 h k + fderiv ℝ B 0 k h := by
  have eq : (fun u => fderiv ℝ F u k) =ᶠ[𝓝 0] fun u => B u k + fderiv ℝ B u k u := by
    filter_upwards [eventually_eventually_nhds.mpr graph,cb.eventually (by decide)] with u gu cu
    change F =ᶠ[𝓝 u] (fun x => q+B x x) at gu
    have d := (((cu.differentiableAt (by decide)).hasFDerivAt.clm_apply (hasFDerivAt_id u)).const_add q).congr_of_eventuallyEq gu
    rw [d.fderiv]; rfl
  let ev := ContinuousLinearMap.apply ℝ V k
  let ev2 := ContinuousLinearMap.apply ℝ (U →L[ℝ] V) k
  have da := (cb.differentiableAt (by decide)).hasFDerivAt
  have d2 := ((cb.fderiv_right (m := 1) (by decide)).differentiableAt (by decide)).hasFDerivAt
  have df := ((cf.fderiv_right (m := 1) (by decide)).differentiableAt (by decide)).hasFDerivAt
  have le : HasFDerivAt ev ev (fderiv ℝ F 0) := ev.hasFDerivAt
  have re : HasFDerivAt ev ev (B 0) := ev.hasFDerivAt
  have re2 : HasFDerivAt ev2 ev2 (fderiv ℝ B 0) := @ContinuousLinearMap.hasFDerivAt ℝ _ (U →L[ℝ] U →L[ℝ] V) _ _ (U →L[ℝ] V) _ _ ev2 _
  have lhs := le.comp 0 df
  have rhs := (re.comp 0 da).add ((re2.comp 0 d2).clm_apply (hasFDerivAt_id (0:U)))
  have ident := congrArg (fun D : U →L[ℝ] V => D h) (lhs.unique (rhs.congr_of_eventuallyEq eq))
  simpa [ev,ev2] using ident

/-- The first path variation, the primitive of the control against the
two unperturbed fields at the reference point. -/
def linearResponse (X : Columns E) (q : E) (h : Controls) : C(Time,E) :=
  operator Input E (coefficient X q 0) h

private def fieldJac {X : Columns E} (jets : SpatialJets X) :
    C(Time × E,E →L[ℝ] Input →L[ℝ] E) :=
  ⟨fun p => (channel 0).comp (jets.J 0 p) + (channel 1).comp (jets.J 1 p),
   (continuous_const.clm_comp (jets.J 0).continuous).add (continuous_const.clm_comp (jets.J 1).continuous)⟩

omit [CompleteSpace E] in
private theorem coefficientDerivative (X : Columns E) (jets : SpatialJets X) (q : E) (w : C(Time,E)) :
    let z := ContinuousMap.const Time q + w
    HasFDerivAt (coefficient X q)
      (PathCalculus.multiplier Time E (Input →L[ℝ] E) (PathCalculus.subst (fieldJac jets) z)) w := by
  let f : C(Time × E,Input →L[ℝ] E) := ⟨fun p => channel 0 (X.Y 0 p.1 p.2) + channel 1 (X.Y 1 p.1 p.2),
    ((channel 0).continuous.comp (X.spatialField 0).continuous).add
    ((channel 1).continuous.comp (X.spatialField 1).continuous)⟩
  let L (i : Fin 2) : E →L[ℝ] Input →L[ℝ] E := channel i
  have each (i : Fin 2) (t : Time) (x : E) :
      HasFDerivAt (fun y => L i (X.Y i t y)) ((L i).comp (jets.J i (t,x))) x :=
    HasFDerivAt.comp (𝕜 := ℝ) (E := E) (F := E) (G := Input →L[ℝ] E) (g := L i) (f := X.Y i t)
      x (@ContinuousLinearMap.hasFDerivAt ℝ _ E _ _ (Input →L[ℝ] E) _ _ (L i) _) (jets.first i t x)
  have der (t : Time) (x : E) : HasFDerivAt (fun y => f (t,y)) (fieldJac jets (t,x)) x := by
    change HasFDerivAt (fun y => L 0 (X.Y 0 t y) + L 1 (X.Y 1 t y))
      ((L 0).comp (jets.J 0 (t,x)) + (L 1).comp (jets.J 1 (t,x))) x
    exact HasFDerivAt.add (𝕜 := ℝ) (E := E) (F := Input →L[ℝ] E)
      (f := fun y => L 0 (X.Y 0 t y)) (g := fun y => L 1 (X.Y 1 t y)) (each 0 t x) (each 1 t x)
  have cf : coefficient X q = fun v => PathCalculus.subst f (ContinuousMap.const Time q + v) := by
    funext v
    apply ContinuousMap.ext
    intro t
    apply ContinuousLinearMap.ext
    intro a
    rfl
  rw [cf]
  exact (hasFDerivAt_comp_add_left (f := PathCalculus.subst f) _).mpr
    (PathCalculus.hasFDerivAt_subst f (fieldJac jets) der _)

set_option maxHeartbeats 900000 in
/-- The Hessian of any representative of the actual integral endpoint
in the two-channel moving equation. The two inputs range over all L²
controls, and the time ordering is carried by the inner primitives. -/
theorem integral_endpoint_hessian (X : Columns E) (jets : SpatialJets X) (q : E)
    (F : Controls → E) (endpoint : X.Endpoint q F) (h k : Controls) :
    let term := fun (a b : Controls) (s : ℝ) =>
      b s 0 • jets.J 0 (clamp s,q) (linearResponse X q a (clamp s)) +
      b s 1 • jets.J 1 (clamp s,q) (linearResponse X q a (clamp s))
    fderiv ℝ (fderiv ℝ F) 0 h k =
      (∫ s in (0:ℝ)..1, term h k s) + ∫ s in (0:ℝ)..1, term k h s := by
  obtain ⟨S,s0,cs,paths⟩ := smooth_path_family X jets q
  let V := C(Time,E)
  let A := fun w : V => operator Input E (coefficient X q w)
  have cm : ContDiff ℝ 2 (operator Input E) := ContinuousLinearMap.contDiff _
  have ca : ContDiff ℝ 2 A := cm.comp (smooth_coefficient X 2
    (fun i => ⟨jets.J i,jets.first i,jets.H i,jets.second i,trivial⟩) q)
  have fix : S =ᶠ[𝓝 0] fun u => A (S u) u := by
    filter_upwards [paths] with u hu
    obtain ⟨w,val,fw⟩ := path_fixed _ _ _ _ hu.1
    have eq : w = S u := by
      apply ContinuousMap.ext
      intro t
      exact add_left_cancel (by simpa only [show clamp (t:ℝ) = t from projIcc_of_mem _ t.2] using val t : q+w t = q+S u t)
    exact eq ▸ fw
  have dS : fderiv ℝ S 0 = A 0 := by
    have d := (((ca.comp_contDiffAt 0 cs).differentiableAt (by decide)).hasFDerivAt.clm_apply (hasFDerivAt_id (0:Controls)))
    rw [(d.congr_of_eventuallyEq fix).fderiv]
    simp [s0]
  let t1 : Time := ⟨1,zero_le_one,le_rfl⟩
  let L := (ContinuousLinearMap.compL ℝ Controls V E) (ContinuousMap.evalCLM ℝ t1)
  let B := fun u => L (A (S u))
  have cL : ContDiff ℝ 2 L := ContinuousLinearMap.contDiff _
  have cb : ContDiffAt ℝ 2 B 0 := cL.comp_contDiffAt 0 (ca.comp_contDiffAt 0 cs)
  have graph : F =ᶠ[𝓝 0] fun u => q + B u u := by
    filter_upwards [endpoint,paths,fix] with u eu pu fu
    have e := eu _ pu.1
    rw [show clamp 1 = t1 from projIcc_of_mem _ t1.2] at e
    exact e.trans (congrArg (fun w : V => q+w t1) fu)
  rw [hessian_apply_at_zero F B q cb (smooth_integral_endpoint X jets q F endpoint) graph]
  let z := ContinuousMap.const Time q + S 0
  let D := PathCalculus.multiplier Time E (Input →L[ℝ] E) (PathCalculus.subst (fieldJac jets) z)
  have coeffD : HasFDerivAt (fun u => coefficient X q (S u)) (D.comp (fderiv ℝ S 0)) (0:Controls) :=
    HasFDerivAt.comp (E := Controls) (F := V) (G := C(Time,Input →L[ℝ] E)) (f := S) (g := coefficient X q)
      0 (coefficientDerivative X jets q (S 0)) (cs.differentiableAt (by decide)).hasFDerivAt
  have dL : HasFDerivAt L L (A (S 0)) := @ContinuousLinearMap.hasFDerivAt ℝ _ (Controls →L[ℝ] V) _ _ (Controls →L[ℝ] E) _ _ L _
  have dop : HasFDerivAt (operator Input E) (operator Input E) (coefficient X q (S 0)) :=
    @ContinuousLinearMap.hasFDerivAt ℝ _ C(Time,Input →L[ℝ] E) _ _ (Controls →L[ℝ] V) _ _ (operator Input E) _
  have da := HasFDerivAt.comp (𝕜 := ℝ) (E := Controls) (F := C(Time,Input →L[ℝ] E)) (G := Controls →L[ℝ] V) (f := fun u => coefficient X q (S u)) (g := operator Input E) (0:Controls) dop coeffD
  have db := HasFDerivAt.comp (𝕜 := ℝ) (E := Controls) (F := Controls →L[ℝ] V) (G := Controls →L[ℝ] E) (f := fun u => A (S u)) (g := L) (0:Controls) dL da
  have db' := db.fderiv
  change fderiv ℝ B 0 = _ at db'
  rw [db']
  dsimp only
  have atTime (a b : Controls) :
      (L ((operator Input E) (D (fderiv ℝ S 0 a)))) b =
        ∫ s in (0:ℝ)..1, b s 0 • jets.J 0 (clamp s,q) (linearResponse X q a (clamp s)) +
          b s 1 • jets.J 1 (clamp s,q) (linearResponse X q a (clamp s)) := by
    change operator Input E (D (fderiv ℝ S 0 a)) b t1 = _
    rw [operator_eq_interval,dS]
    apply intervalIntegral.integral_congr
    intro s _
    change b s 0 • jets.J 0 (clamp s,z (clamp s)) (linearResponse X q a (clamp s)) +
      b s 1 • jets.J 1 (clamp s,z (clamp s)) (linearResponse X q a (clamp s)) = _
    simp only [z,s0,add_zero]; rfl
  exact congrArg₂ (· + ·) (atTime h k) (atTime k h)

#print axioms integral_endpoint_hessian

/-- First variation of the actual moving-frame endpoint on the full control
space. The time-varying columns are evaluated along the stationary base. -/
theorem integral_endpoint_first (X : Columns E) (jets : SpatialJets X) (q : E)
    (F : Controls → E) (endpoint : X.Endpoint q F) (h : Controls) :
    fderiv ℝ F 0 h = ∫ s in (0:ℝ)..1, X.velocity (clamp s) q (h s) := by
  obtain ⟨S,s0,cs,paths⟩ := smooth_path_family X jets q
  let V := C(Time,E)
  let A := fun w : V => operator Input E (coefficient X q w)
  have cm : ContDiff ℝ 2 (operator Input E) := ContinuousLinearMap.contDiff _
  have ca : ContDiff ℝ 2 A := cm.comp (smooth_coefficient X 2
    (fun i => ⟨jets.J i,jets.first i,jets.H i,jets.second i,trivial⟩) q)
  have fix : S =ᶠ[𝓝 0] fun u => A (S u) u := by
    filter_upwards [paths] with u hu
    obtain ⟨w,val,fw⟩ := path_fixed _ _ _ _ hu.1
    have eq : w = S u := by
      apply ContinuousMap.ext
      intro t
      exact add_left_cancel (by simpa only [show clamp (t:ℝ) = t from projIcc_of_mem _ t.2] using val t : q+w t = q+S u t)
    exact eq ▸ fw
  have dS : fderiv ℝ S 0 = A 0 := by
    have d := (((ca.comp_contDiffAt 0 cs).differentiableAt (by decide)).hasFDerivAt.clm_apply (hasFDerivAt_id (0:Controls)))
    rw [(d.congr_of_eventuallyEq fix).fderiv]
    simp [s0]
  let t1 : Time := ⟨1,zero_le_one,le_rfl⟩
  let ev := (ContinuousMap.evalCLM ℝ t1 : V →L[ℝ] E)
  have same : F =ᶠ[𝓝 0] fun u => q + ev (S u) := by
    filter_upwards [endpoint,paths] with u hu pu
    simpa only [ev,show clamp 1 = t1 from projIcc_of_mem _ t1.2] using hu _ pu.1
  have der := ((ev.hasFDerivAt.comp 0 (cs.differentiableAt (by decide)).hasFDerivAt).const_add q).congr_of_eventuallyEq same
  rw [der.fderiv,dS]
  change operator Input E (coefficient X q 0) h t1 = _
  rw [operator_eq_interval]
  apply intervalIntegral.integral_congr
  intro s _
  simpa using coefficient_apply X q 0 (clamp s) (h s)

#print axioms integral_endpoint_first

end MinimizingSard.PulseGeometry
