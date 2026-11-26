import OrderedPulseVariation
import CausalTail
import MixedTimeJets
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.LinearAlgebra.Projection

/-! A finite-rank scalar Hessian gives a vanishing mixed-time bracket
on a terminal interval. Work with ordered interval pulses directly, so
there is no hypothesis representing that Hessian by a Volterra kernel. -/
noncomputable section
open Set Filter MeasureTheory Module
open scoped Topology
open MinimizingSard.Pulse
namespace MinimizingSard.PulseGeometry

structure Label where
  channel : Fin 2
  a : ℝ
  b : ℝ
  left_pos : 0 < a
  nonempty : a < b
  right_lt : b < 1

abbrev Controls := Causal.Signals (Fin 2 → ℝ)
def Label.control (i : Label) : Controls := Causal.pulse i.a i.b (Pi.single i.channel 1)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure Columns (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  Y : Fin 2 → ℝ → E → E
  continuous : ∀ i, Continuous (Y i).uncurry
  differentiable : ∀ i t, t ∈ Ioo (0 : ℝ) 1 → Differentiable ℝ (Y i t)
  jacobian : ∀ i, Continuous (fun z : ℝ × E => fderiv ℝ (Y i z.1) z.2)

def Columns.window (X : Columns E) (i : Label) : Window E where
  a := i.a
  b := i.b
  ordered := i.nonempty.le
  Y := X.Y i.channel
  value_cont := X.continuous _
  jac_cont := X.jacobian _
  space_diff := fun t ht => X.differentiable _ t ⟨i.left_pos.trans_le ht.1,ht.2.trans_lt i.right_lt⟩

def hessianRow (F : Controls → E) (p : E →L[ℝ] ℝ) : Controls →ₗ[ℝ] (Controls →L[ℝ] ℝ) :=
  (((ContinuousLinearMap.compL ℝ Controls E ℝ p).comp (fderiv ℝ (fderiv ℝ F) 0))).toLinearMap

private def restrictFunctional {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K : Submodule ℝ V) : (V →L[ℝ] ℝ) →ₗ[ℝ] (K →ₗ[ℝ] ℝ) where
  toFun f := f.toLinearMap.comp K.subtype
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def restrictedHessianRow (F : Controls → E) (p : E →L[ℝ] ℝ) :
    let K := LinearMap.ker (fderiv ℝ F 0).toLinearMap
    K →ₗ[ℝ] (K →ₗ[ℝ] ℝ) :=
  let K := LinearMap.ker (fderiv ℝ F 0).toLinearMap
  (restrictFunctional K).comp ((hessianRow F p).comp K.subtype)

/-- Restrict both slots to the actual kernel of the endpoint
differential. Its finite codimension controls all the omitted rows
and columns, even when the control space is infinite-dimensional. -/
theorem full_rank_finite_of_restricted (F : Controls → E) (p : E →L[ℝ] ℝ) [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ (LinearMap.range (restrictedHessianRow F p))] :
    FiniteDimensional ℝ (LinearMap.range (hessianRow F p)) := by
  let D := (fderiv ℝ F 0).toLinearMap
  let K := LinearMap.ker D
  let H := hessianRow F p
  let A := H.comp K.subtype
  let B := restrictedHessianRow F p
  obtain ⟨S,hS⟩ := K.exists_isCompl
  haveI : FiniteDimensional ℝ (Controls ⧸ K) := D.quotKerEquivRange.symm.finiteDimensional
  haveI : FiniteDimensional ℝ S := (K.quotientEquivOfIsCompl S hS).finiteDimensional
  haveI : FiniteDimensional ℝ (LinearMap.range A) := by
    let first : LinearMap.range A →ₗ[ℝ] LinearMap.range B :=
      ((restrictFunctional K).comp (LinearMap.range A).subtype).codRestrict _ (by
        rintro ⟨_,v,rfl⟩
        exact ⟨v,rfl⟩)
    let second := (restrictFunctional S).comp (LinearMap.range A).subtype
    apply FiniteDimensional.of_injective (first.prod second)
    intro a b hab
    have hk := congrArg Prod.fst hab
    have hs := congrArg Prod.snd hab
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    have hx : x ∈ K ⊔ S := by rw [hS.sup_eq_top]; trivial
    obtain ⟨k,hk',s,hs',rfl⟩ := Submodule.mem_sup.mp hx
    have ek : a.val k = b.val k := congrArg (fun y : LinearMap.range B => y.val ⟨k,hk'⟩) hk
    have es : a.val s = b.val s := congrArg (fun y : S →ₗ[ℝ] ℝ => y ⟨s,hs'⟩) hs
    exact (map_add a.val k s).trans ((congrArg₂ (· + ·) ek es).trans (map_add b.val k s).symm)
  have small (N : Submodule ℝ Controls) [FiniteDimensional ℝ (LinearMap.range (H.comp N.subtype))] :
      (N.map H).FG := by
    have fg := Module.Finite.iff_fg.mp (inferInstance :
      FiniteDimensional ℝ (LinearMap.range (H.comp N.subtype)))
    rwa [LinearMap.range_comp, Submodule.range_subtype] at fg
  apply Module.Finite.iff_fg.mpr
  change (LinearMap.range H).FG
  rw [← Submodule.map_top, ← hS.sup_eq_top, Submodule.map_sup]
  exact (small K).sup (small S)

#print axioms full_rank_finite_of_restricted

/-- A decreasing family of late-pulse spans in a finite-dimensional
space stabilizes before 1. Every later readout then vanishes on the
stable span if it vanishes on inputs following its own right endpoint. -/
private theorem late_features {J : Type*} [AddCommGroup J] [Module ℝ J] [FiniteDimensional ℝ J]
    (col : Label → J) (readout : Label → J →ₗ[ℝ] ℝ)
    (causal : ∀ i j : Label, j.b ≤ i.a → readout j (col i) = 0) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ i j : Label, r < i.a → readout j (col i) = 0 := by
  classical
  let span (r : ℝ) := Submodule.span ℝ (col '' {i | r < i.a})
  have anti : Antitone span := fun _ _ h => Submodule.span_mono
    (image_mono (fun _ hi => h.trans_lt hi))
  let P (k : ℕ) := ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ finrank ℝ (span r) = k
  have ex : ∃ k, P k := ⟨_,0,le_rfl,zero_lt_one,rfl⟩
  obtain ⟨r,hr,hr1,hd⟩ := Nat.find_spec ex
  refine ⟨r,hr,hr1,?_⟩
  intro i j hi
  let cut := max r j.b
  have eq : span cut = span r := Submodule.eq_of_le_of_finrank_le (anti (le_max_left _ _)) (by
    rw [hd]
    exact Nat.find_min' ex ⟨cut,hr.trans (le_max_left _ _),max_lt hr1 j.right_lt,rfl⟩)
  have van : span cut ≤ LinearMap.ker (readout j) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k,hk,rfl⟩
    exact causal k j ((le_max_right r j.b).trans (le_of_lt hk))
  rw [eq] at van
  exact van (Submodule.subset_span ⟨i,hi,rfl⟩)

def Columns.Graph (X : Columns E) (F : Controls → E) (q : E)
    (Z : Label → E → ℝ → ℝ → E) : Prop :=
  ∀ i j : Label, i.b ≤ j.a → ∀ᶠ h in 𝓝 (0 : ℝ),
    orderedEndpoint (X.window i) (X.window j) (Z i) (Z j) q h =ᶠ[𝓝 0]
      fun k => F (h • i.control + k • j.control)

section
variable [FiniteDimensional ℝ E]

theorem late_bracket_rectangles (X : Columns E) (F : Controls → E) (q : E) (p : E →L[ℝ] ℝ)
    (smooth : ContDiffAt ℝ 2 F 0) [FiniteDimensional ℝ (LinearMap.range (hessianRow F p))]
    (Z : Label → E → ℝ → ℝ → E) (sol : ∀ i, (X.window i).FamilyNear q (Z i))
    (graph : X.Graph F q Z) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ i j : Label, r < i.a → i.b ≤ j.a →
      p (∫ t in j.a..j.b, ∫ s in i.a..i.b,
        VectorField.lieBracket ℝ (X.Y i.channel s) (X.Y j.channel t) q) = 0 := by
  let H := hessianRow F p
  let J := (LinearMap.range H) × (E →L[ℝ] E)
  let col (i : Label) : J :=
    (⟨H i.control,i.control,rfl⟩, ∫ s in i.a..i.b, fderiv ℝ (X.Y i.channel s) q)
  let readout (j : Label) : J →ₗ[ℝ] ℝ :=
    (((ContinuousLinearMap.apply ℝ ℝ j.control).toLinearMap.comp (LinearMap.range H).subtype).comp
      (LinearMap.fst ℝ _ _)) -
    ((p.toLinearMap.comp (ContinuousLinearMap.apply ℝ E ((X.window j).average q)).toLinearMap).comp
      (LinearMap.snd ℝ _ _))
  have applyRow (i j : Label) : readout j (col i) =
      p ((fderiv ℝ (fderiv ℝ F) 0 i.control) j.control -
        (∫ s in i.a..i.b, fderiv ℝ (X.Y i.channel s) q) ((X.window j).average q)) := by
    rw [map_sub]; rfl
  have causal (i j : Label) (later : j.b ≤ i.a) : readout j (col i) = 0 := by
    rw [applyRow, smooth.isSymmSndFDerivAt (by simp) i.control j.control]
    have h1 := hessian_on_amplitude_plane F smooth j.control i.control _ (graph j i later)
    have h2 := ordered_mixed_derivative (X.window j) (X.window i) q (Z j) (Z i) (sol j) (sol i)
    have eq := h1.unique h2
    rw [eq, ((X.window i).average_derivative q).fderiv]
    simp only [Columns.window,sub_self,map_zero]
  obtain ⟨r,hr,hr1,allZero⟩ := late_features col readout causal
  refine ⟨r,hr,hr1,?_⟩
  intro i j hi hij
  have h := allZero i j hi
  rw [applyRow] at h
  exact (congrArg p (corrected_endpoint_hessian_on_pulses F smooth i.control j.control
    (X.window i) (X.window j) q (Z i) (Z j) (sol i) (sol j) (graph i j hij))).symm.trans h

#print axioms late_bracket_rectangles

theorem zero_of_interval_integrals (f : ℝ → ℝ) (hf : Continuous f) {a b : ℝ}
    (allZero : ∀ l u, a < l → l < u → u < b → (∫ t in l..u, f t) = 0)
    (x : ℝ) (hx : x ∈ Ioo a b) : f x = 0 := by
  obtain ⟨l,hal,hlx⟩ := exists_between hx.1
  have loc : (fun u => ∫ t in l..u, f t) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) :=
    eventually_of_mem (Ioo_mem_nhds hlx hx.2) (fun u hu => allZero l u hal hu.1 hu.2)
  have hd := intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable l x)
    (hf.stronglyMeasurableAtFilter volume (𝓝 x)) hf.continuousAt
  exact hd.unique ((hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq loc)

/-- Test the actual first derivative on a pulse. A covector annihilating
its image annihilates both moved horizontal columns at every time,
including the two ends of the patch. -/
theorem annihilates_columns (X : Columns E) (F : Controls → E) (q : E) (p : E →L[ℝ] ℝ)
    (df : DifferentiableAt ℝ F 0) (row : ∀ v, p (fderiv ℝ F 0 v) = 0)
    (Z : Label → E → ℝ → ℝ → E) (sol : ∀ i, (X.window i).FamilyNear q (Z i))
    (graph : X.Graph F q Z) :
    ∀ n t, t ∈ Icc (0 : ℝ) 1 → p (X.Y n t q) = 0 := by
  intro n
  have c : Continuous (fun t => X.Y n t q) :=
    (X.continuous n).comp (continuous_id.prodMk continuous_const)
  have interior : EqOn (fun t => p (X.Y n t q)) (fun _ => 0) (Ioo (0 : ℝ) 1) := by
    intro t ht
    apply zero_of_interval_integrals _ (p.continuous.comp c) _ t ht
    intro l u hl hlu hu
    let i : Label := ⟨n,l,u,hl,hlu,hu⟩
    obtain ⟨b,hb,hbl⟩ := exists_between hl
    obtain ⟨a,ha,hab⟩ := exists_between hb
    let j : Label := ⟨n,a,b,ha,hab,(hbl.trans hlu).trans hu⟩
    have g := (graph j i hbl.le).self_of_nhds
    have zj := ((sol j).self_of_nhds.self_of_nhds).2 j.b (right_mem_Icc.mpr j.nonempty.le)
    change Z j q 0 j.b = q + (0 : ℝ) • _ at zj
    simp only [zero_smul,add_zero] at zj
    have eq : (fun k => Z i q k i.b) =ᶠ[𝓝 (0 : ℝ)] fun k => F (k • i.control) := by
      change (fun k => Z i (Z j q 0 j.b) k i.b) =ᶠ[𝓝 (0 : ℝ)]
        fun k => F ((0 : ℝ) • j.control + k • i.control) at g
      simpa only [zj,zero_smul,zero_add] using g
    have line : HasDerivAt (fun k : ℝ => k • i.control) i.control 0 := by
      simpa only [one_smul] using (hasDerivAt_id' (0 : ℝ)).smul_const i.control
    have df' : DifferentiableAt ℝ F ((0 : ℝ) • i.control) := by simpa
    have calcDer := (df'.hasFDerivAt.comp_hasDerivAt 0 line).congr_of_eventuallyEq eq
    have refDer := amplitude_derivative (X.Y n) (X.continuous n) q hlu.le (Z i q)
      (sol i).self_of_nhds
    have matchDer : (∫ t in l..u, X.Y n t q) = fderiv ℝ F 0 i.control := by
      simpa only [zero_smul] using refDer.unique calcDer
    exact (p.intervalIntegral_comp_comm (c.intervalIntegrable l u)).trans
      ((congrArg p matchDer).trans (row i.control))
  intro t ht
  apply interior.closure (p.continuous.comp c) continuous_const
  rwa [closure_Ioo (zero_ne_one : (0 : ℝ) ≠ 1)]

#print axioms annihilates_columns

/-- Both endpoint times can approach 1. The terminal interval follows
from the finite rank of the actual scalar Hessian, with no operator or
kernel representation supplied as an additional hypothesis. -/
theorem mixed_time_zero (X : Columns E) (F : Controls → E) (q : E) (p : E →L[ℝ] ℝ)
    (smooth : ContDiffAt ℝ 2 F 0) [FiniteDimensional ℝ (LinearMap.range (hessianRow F p))]
    (Z : Label → E → ℝ → ℝ → E) (sol : ∀ i, (X.window i).FamilyNear q (Z i))
    (graph : X.Graph F q Z) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ i j s t, r < s → s < t → t ≤ 1 →
      p (VectorField.lieBracket ℝ (X.Y i s) (X.Y j t) q) = 0 := by
  obtain ⟨r,hr,hr1,rect⟩ := late_bracket_rectangles X F q p smooth Z sol graph
  refine ⟨r,hr,hr1,?_⟩
  intro i j s t hrs hst ht
  let B (t s : ℝ) := VectorField.lieBracket ℝ (X.Y i s) (X.Y j t) q
  let K (t s : ℝ) := p (B t s)
  have cB : Continuous B.uncurry := by
    change Continuous (fun z : ℝ × ℝ =>
      fderiv ℝ (X.Y j z.1) q (X.Y i z.2 q) - fderiv ℝ (X.Y i z.2) q (X.Y j z.1 q))
    exact (((X.jacobian j).comp (continuous_fst.prodMk continuous_const)).clm_apply
      ((X.continuous i).comp (continuous_snd.prodMk continuous_const))).sub
      (((X.jacobian i).comp (continuous_snd.prodMk continuous_const)).clm_apply
        ((X.continuous j).comp (continuous_fst.prodMk continuous_const)))
  have cK : Continuous K.uncurry := p.continuous.comp cB
  have interior : EqOn (fun v => K v s) (fun _ => 0) (Ioo s 1) := by
    intro v hv
    obtain ⟨m,hsm,hmv⟩ := exists_between hv.1
    apply zero_of_interval_integrals (K v) (cK.comp (continuous_const.prodMk continuous_id))
      (a := r) (b := m) _ s ⟨hrs,hsm⟩
    intro a b hra hab hbm
    let earlier : Label := ⟨i,a,b,hr.trans_lt hra,hab,(hbm.trans hmv).trans hv.2⟩
    have cInn := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) cK a b
    apply zero_of_interval_integrals (fun t => ∫ z in a..b, K t z) cInn
      (a := m) (b := 1) _ v ⟨hmv,hv.2⟩
    intro l u hml hlu hu
    let later : Label := ⟨j,l,u,((hr.trans_lt hra).trans hab).trans (hbm.trans hml),hlu,hu⟩
    have z := rect earlier later hra (hbm.trans hml).le
    change p (∫ t in l..u, ∫ z in a..b, B t z) = 0 at z
    have cont := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) cB a b
    rw [← p.intervalIntegral_comp_comm (cont.intervalIntegrable l u)] at z
    convert z using 1
    apply intervalIntegral.integral_congr
    intro t _
    exact p.intervalIntegral_comp_comm
      ((cB.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b)
  have cont := cK.comp (continuous_id.prodMk (continuous_const (y := s)))
  apply interior.closure cont continuous_const
  rw [closure_Ioo (hst.trans_le ht).ne]
  exact ⟨hst.le,ht⟩

theorem finite_hessian_kills_triples (X : Columns E) (F : Controls → E) (q : E) (p : E →L[ℝ] ℝ)
    (smooth : ContDiffAt ℝ 2 F 0) [FiniteDimensional ℝ (LinearMap.range (restrictedHessianRow F p))]
    (Z : Label → E → ℝ → ℝ → E) (sol : ∀ i, (X.window i).FamilyNear q (Z i))
    (graph : X.Graph F q Z)
    (B : ℝ → E → E) (u v : ℝ → ℝ) (hend : B 1 = VectorField.lieBracket ℝ (X.Y 0 1) (X.Y 1 1))
    (hB : ContinuousOn (fun t => MixedTime.jet (B t) q) (Icc 0 1))
    (flow : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1),
      HasDerivAt (fun s => MixedTime.jet (X.Y 0 s) q) (-(v t) • MixedTime.jet (B t) q) t ∧
      HasDerivAt (fun s => MixedTime.jet (X.Y 1 s) q) (u t • MixedTime.jet (B t) q) t ∧
      (u t ≠ 0 ∨ v t ≠ 0)) :
    ∀ i, p (VectorField.lieBracket ℝ (X.Y i 1)
      (VectorField.lieBracket ℝ (X.Y 0 1) (X.Y 1 1)) q) = 0 := by
  haveI := full_rank_finite_of_restricted F p
  obtain ⟨r,hr,h1,zero⟩ := mixed_time_zero X F q p smooth Z sol graph
  intro i
  have mixed (s : ℝ) (hs : s ∈ Ioo r 1) (j : Fin 2) :
      p (VectorField.lieBracket ℝ (X.Y i 1) (X.Y j s) q) = 0 := by
    rw [VectorField.lieBracket_swap,map_neg,zero j i s 1 hs.1 hs.2 le_rfl,neg_zero]
  exact MixedTime.terminal_triple_bracket p q (X.Y 0) (X.Y 1) B (X.Y i 1) u v h1
    hend (hB.mono (Icc_subset_Icc_left hr)) (fun s hs => ⟨mixed s hs 0,mixed s hs 1⟩)
    (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_left hr) flow)

#print axioms mixed_time_zero
#print axioms finite_hessian_kills_triples
end
end MinimizingSard.PulseGeometry
