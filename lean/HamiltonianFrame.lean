import SmoothShortFlow
import FrameChangeLayers

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five

abbrev Phase := State × (State →L[ℝ] ℝ)

/-- Horizontal coefficients of a covector in the local orthonormal frame. -/
def normalCoefficients {m : ℕ} (X : Fin m → State → State) (z : Phase) : Fiber m := fun i => z.2 (X i z.1)

def frameHamiltonian {m : ℕ} (X : Fin m → State → State) (z : Phase) : ℝ :=
  speedSq (normalCoefficients X z) / 2

/-- Hamilton's two equations in a frame chart. -/
def hamiltonianField {m : ℕ} (X : Fin m → State → State) (z : Phase) : Phase :=
  (∑ i, (normalCoefficients X z i) • X i z.1,
   -∑ i, (normalCoefficients X z i) • z.2.comp (fderiv ℝ (X i) z.1))

theorem hamiltonianField_smooth {m : ℕ} (X : Fin m → State → State) (sm : ∀ i, ContDiff ℝ ∞ (X i)) :
    ContDiff ℝ ∞ (hamiltonianField X) := by
  have coeff (i) : ContDiff ℝ ∞ (fun z : Phase => normalCoefficients X z i) :=
    contDiff_snd.clm_apply ((sm i).comp contDiff_fst)
  apply ContDiff.prodMk
  · exact ContDiff.sum fun i _ => (coeff i).smul ((sm i).comp contDiff_fst)
  · apply ContDiff.neg
    exact ContDiff.sum fun i _ => (coeff i).smul (contDiff_snd.clm_comp
      (((sm i).fderiv_right (m := ∞) (by simp)).comp contDiff_fst))

private theorem hamiltonian_max {M : Type*} [TopologicalSpace M] [ChartedSpace State M] {m : ℕ}
    (e : Frame M m) (q : State) (p : State →L[ℝ] ℝ) :
    (∀ v : Fiber m, p (e.velocity q v) - speedSq v/2 ≤ frameHamiltonian e.X (q,p)) ∧
    p (e.velocity q (normalCoefficients e.X (q,p))) - speedSq (normalCoefficients e.X (q,p))/2 =
      frameHamiltonian e.X (q,p) := by
  let a := normalCoefficients e.X (q,p)
  have pairing (v : Fiber m) : p (e.velocity q v) = ∑ i, v i*a i := by simp [Frame.velocity,a,normalCoefficients]
  constructor
  · intro v
    rw [pairing]
    change (∑ i, v i*a i) - (∑ i, v i^2)/2 ≤ (∑ i, a i^2)/2
    have h : (∑ i, (2*(v i*a i)-v i^2)) ≤ ∑ i, a i^2 := Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (v i-a i)]
    rw [Finset.sum_sub_distrib,← Finset.mul_sum] at h
    linarith
  · change p (e.velocity q a)-speedSq a/2 = speedSq a/2
    rw [pairing]
    simp only [speedSq,pow_two]
    ring

/-- The scalar Hamiltonian on cotangent coordinates agrees on every frame
overlap. The proof uses only the given horizontal isometry and its inverse. -/
theorem hamiltonian_overlap {M : Type*} [TopologicalSpace M] [ChartedSpace State M] {m : ℕ}
    (Γ : Geometry M m) (e d : Frame M m) (he : e ∈ Γ.frames) (hd : d ∈ Γ.frames) (y : M)
    (hy : y ∈ e.chart.source ∩ d.chart.source) (p : State →L[ℝ] ℝ) :
    let J := fderiv ℝ (d.chart ∘ e.chart.symm) (e.chart y)
    frameHamiltonian e.X (e.chart y,p.comp J) = frameHamiltonian d.X (d.chart y,p) := by
  intro J
  obtain ⟨T,iso⟩ := Γ.overlap e he d hd y hy
  let a := normalCoefficients e.X (e.chart y,p.comp J)
  let b := normalCoefficients d.X (d.chart y,p)
  have eq (v : Fiber m) : (p.comp J) (e.velocity (e.chart y) v)-speedSq v/2 =
      p (d.velocity (d.chart y) (T v))-speedSq (T v)/2 := by
    rw [ContinuousLinearMap.comp_apply,← (iso v).2,(iso v).1]
  obtain ⟨left,exactL⟩ := hamiltonian_max e (e.chart y) (p.comp J)
  obtain ⟨right,exactR⟩ := hamiltonian_max d (d.chart y) p
  apply le_antisymm
  · exact exactL.symm.trans_le ((eq a).trans_le (right _))
  · have h := (eq (T.symm b)).symm.trans_le (left _)
    rw [T.apply_symm_apply] at h
    exact exactR.symm.trans_le h

/-- Scale the covector of a lifted curve while rescaling its Hamiltonian
clock. This identity also permits a zero instantaneous clock rate. -/
theorem hamiltonian_scale {m : ℕ} (X : Fin m → State → State) (z : Phase) (L : ℝ) :
    hamiltonianField X (z.1,L • z.2) =
      (L • (hamiltonianField X z).1, (L*L) • (hamiltonianField X z).2) := by
  have coef (i) : normalCoefficients X (z.1,L • z.2) i = L * normalCoefficients X z i := rfl
  ext1
  · simp only [hamiltonianField,coef,Finset.smul_sum,mul_smul]
  · simp only [hamiltonianField,coef,smul_neg,Finset.smul_sum,ContinuousLinearMap.smul_comp,mul_smul]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_comm (normalCoefficients X z i) L]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M]

/-- The Hamilton ODE has a smooth local solution jointly in both phase
variables and time for an original chart, with no completeness assumption on the geometry. -/
theorem local_hamiltonian_flow {m : ℕ} (e : Frame M m) (z : Phase) (inside : z.1 ∈ e.chart.target) :
    ∃ f : Phase × ℝ → Phase, ∀ᶠ s : Phase × ℝ in 𝓝 (z,0),
      ContDiffAt ℝ ∞ f s ∧ f (s.1,0) = s.1 ∧ (f s).1 ∈ e.chart.target ∧
      HasDerivAt (fun t => f (s.1,t)) (hamiltonianField e.X (f s)) s.2 := by
  choose X sm agree using fun i => smooth_germ_extension e.chart.open_target inside (e.X i) (e.smooth i)
  obtain ⟨f,flow⟩ := smooth_short_flow (hamiltonianField X) (hamiltonianField_smooth X sm) z
  have at0 := flow.self_of_nhds
  have push : Tendsto (fun s : Phase × ℝ => (f s).1) (𝓝 (z,0)) (𝓝 z.1) := by
    have f0 : f (z,0) = z := at0.2.1
    simpa only [Function.comp_apply,f0] using (continuous_fst.continuousAt.comp (x := (z,(0:ℝ))) at0.1.continuousAt).tendsto
  have fields : ∀ᶠ q in 𝓝 z.1, ∀ i, X i =ᶠ[𝓝 q] e.X i := eventually_all.mpr fun i => (agree i).eventuallyEq_nhds
  refine ⟨f,?_⟩
  filter_upwards [flow,push fields,push (e.chart.open_target.mem_nhds inside)] with s sf same mem
  refine ⟨sf.1,sf.2.1,mem,?_⟩
  have eq : hamiltonianField X (f s) = hamiltonianField e.X (f s) := by
    simp only [hamiltonianField,normalCoefficients,fun i => (same i).self_of_nhds,fun i => (same i).fderiv_eq (𝕜 := ℝ)]
  exact eq ▸ sf.2.2

#print axioms hamiltonianField_smooth
#print axioms hamiltonian_overlap
#print axioms hamiltonian_scale
#print axioms local_hamiltonian_flow

/-- A phase velocity defines the differential of its Hamiltonian by the
canonical cotangent pairing. -/
def canonicalRow (v : Phase) : Phase →L[ℝ] ℝ :=
  ((ContinuousLinearMap.apply ℝ ℝ v.1).comp (ContinuousLinearMap.snd ℝ State (State →L[ℝ] ℝ))) -
    v.2.comp (ContinuousLinearMap.fst ℝ State (State →L[ℝ] ℝ))

theorem frameHamiltonian_derivative {m : ℕ} (X : Fin m → State → State) (z : Phase)
    (sm : ∀ i, DifferentiableAt ℝ (X i) z.1) :
    HasFDerivAt (frameHamiltonian X) (canonicalRow (hamiltonianField X z)) z := by
  let c := normalCoefficients X
  let a (i : Fin m) (p : Phase) := c p i
  let g (i : Fin m) := fderiv ℝ (a i) z
  have da (i : Fin m) := (hasFDerivAt_snd (𝕜 := ℝ) (p := z)).clm_apply
    ((sm i).hasFDerivAt.comp z (hasFDerivAt_fst (𝕜 := ℝ) (p := z)))
  have ag (i) : HasFDerivAt (a i) (g i) z := (da i).differentiableAt.hasFDerivAt
  have formula (i) (v : Phase) : g i v = v.2 (X i z.1)+z.2 (fderiv ℝ (X i) z.1 v.1) := by
    rw [show g i = _ from (da i).fderiv]
    exact add_comm _ _
  have square (i) : HasFDerivAt (fun p => a i p*a i p) (a i z • g i+a i z • g i) z :=
    (ag i).mul (ag i)
  have total := (HasFDerivAt.sum (u := Finset.univ) (fun i _ => square i)).const_smul (2:ℝ)⁻¹
  have funEq : frameHamiltonian X = (2:ℝ)⁻¹ • ∑ i, (fun p => a i p*a i p) := by
    ext p
    simp only [frameHamiltonian,speedSq,pow_two,a,c,Pi.smul_apply,Finset.sum_apply,smul_eq_mul,div_eq_inv_mul]
  have rowEq : canonicalRow (hamiltonianField X z) = (2:ℝ)⁻¹ • ∑ i, (a i z • g i+a i z • g i) := by
    apply ContinuousLinearMap.ext
    intro v
    change v.2 (∑ i, a i z • X i z.1) - (-(∑ i, a i z • z.2.comp (fderiv ℝ (X i) z.1))) v.1 =
      ((2:ℝ)⁻¹ • ∑ i, (a i z • g i+a i z • g i)) v
    simp only [map_sum,map_smul,ContinuousLinearMap.neg_apply,ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,smul_eq_mul,ContinuousLinearMap.add_apply,
      formula,sub_neg_eq_add,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rwa [← funEq,← rowEq] at total

#print axioms frameHamiltonian_derivative


/-- Compatibility of the Hamilton vector fields, including the derivative
of the covector coordinate change in the base direction. -/
theorem hamiltonian_field_overlap {m : ℕ} [IsManifold 𝓘(ℝ,State) ∞ M]
    (Γ : Geometry M m) (e d : Frame M m) (he : e ∈ Γ.frames) (hd : d ∈ Γ.frames) (y : M)
    (hy : y ∈ e.chart.source ∩ d.chart.source) (p : State →L[ℝ] ℝ) :
    let F := d.chart ∘ e.chart.symm
    let q := e.chart y
    let J := fderiv ℝ F q
    let v := hamiltonianField e.X (q,p.comp J)
    let w := hamiltonianField d.X (F q,p)
    J v.1 = w.1 ∧ ∀ h, v.2 h = w.2 (J h) + p (fderiv ℝ (fderiv ℝ F) q v.1 h) := by
  intro F q J v w
  have mem : q ∈ (e.chart.symm.trans d.chart).source := ⟨e.chart.map_source hy.1,by simpa [q,e.chart.left_inv hy.1] using hy.2⟩
  have cf : ContDiffAt ℝ 2 F q := transition_smooth e.chart d.chart e.compatible d.compatible y hy.1 hy.2
  have jf : HasFDerivAt F J q := (cf.differentiableAt (by decide)).hasFDerivAt
  let J' := fderiv ℝ (fderiv ℝ F) q
  have dj : HasFDerivAt (fderiv ℝ F) J' q :=
    ((cf.fderiv_right (m := 1) (by decide)).differentiableAt (by decide)).hasFDerivAt
  let z : Phase := (q,p)
  let A (s : Phase) : Phase := (s.1,s.2.comp (fderiv ℝ F s.1))
  let B (s : Phase) : Phase := (F s.1,s.2)
  have fstD := hasFDerivAt_fst (𝕜 := ℝ) (p := z)
  have sndD := hasFDerivAt_snd (𝕜 := ℝ) (p := z)
  have da := fstD.prodMk (sndD.clm_comp (dj.comp z fstD))
  have db := (jf.comp z fstD).prodMk sndD
  have su (i) : DifferentiableAt ℝ (e.X i) q :=
    ((e.smooth i).contDiffAt (e.chart.open_target.mem_nhds (e.chart.map_source hy.1))).differentiableAt (by simp)
  have qd : F q = d.chart y := congrArg d.chart (e.chart.left_inv hy.1)
  have sv (i) : DifferentiableAt ℝ (d.X i) (F q) := qd.symm ▸
    ((d.smooth i).contDiffAt (d.chart.open_target.mem_nhds (d.chart.map_source hy.2))).differentiableAt (by simp)
  have du := (frameHamiltonian_derivative e.X (A z) su).comp z da
  have dv := (frameHamiltonian_derivative d.X (B z) sv).comp z db
  have same : frameHamiltonian e.X ∘ A =ᶠ[𝓝 z] frameHamiltonian d.X ∘ B := by
    filter_upwards [continuous_fst.continuousAt.tendsto ((e.chart.symm.trans d.chart).open_source.mem_nhds mem)] with s hs
    have r := e.chart.right_inv hs.1
    have hit := hamiltonian_overlap Γ e d he hd (e.chart.symm s.1) ⟨e.chart.map_target hs.1,hs.2⟩ s.2
    simpa only [r,A,B,F,Function.comp_apply] using hit
  have row := du.unique (dv.congr_of_eventuallyEq same)
  have pair (h : State) (l : State →L[ℝ] ℝ) :
      l (J v.1) + p (J' h v.1) - v.2 h = l w.1 - w.2 (J h) := by
    have eq := congrArg (fun D : Phase →L[ℝ] ℝ => D (h,l)) row
    change (p (J' h v.1) + l (J v.1)) - v.2 h = l w.1 - w.2 (J h) at eq
    linarith
  constructor
  · ext i
    have eq := pair 0 (ContinuousLinearMap.proj i)
    simpa [J'] using eq
  · intro h
    have eq := pair h 0
    simp only [ContinuousLinearMap.zero_apply,zero_add,zero_sub] at eq
    rw [cf.isSymmSndFDerivAt (by simp) v.1 h]
    change v.2 h = w.2 (J h)+p (J' h v.1)
    linarith

#print axioms hamiltonian_field_overlap

end MinimizingSard.Five
