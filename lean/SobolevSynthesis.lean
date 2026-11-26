import ArbitraryFrameEndpoint
import PrimitivePairing
import SupportedControlDensity

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology ContDiff
namespace MinimizingSard.Five
open Volterra
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] {m : ℕ}

private def coanalysis (e : Frame M m) (z : State) : State →L[ℝ] Fiber m :=
  ∑ i : Fin m, ∑ j : Fin 5, (e.X i z j) •
    (ContinuousLinearMap.proj j : State →L[ℝ] ℝ).smulRight (Pi.single i 1)

private theorem coanalysis_apply (e : Frame M m) (z v : State) (i : Fin m) :
    coanalysis e z v i = ∑ j, (e.X i z j)*v j := by
  classical
  simp [coanalysis,ContinuousLinearMap.sum_apply,Finset.sum_apply,Pi.single_apply,Pi.smul_apply]

private theorem gram_pairing (e : Frame M m) (z : State) (a : Fiber m) :
    ∑ i, a i*(coanalysis e z (e.coefficient z a) i) = ∑ j, (e.coefficient z a j)^2 := by
  simp only [coanalysis_apply,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [← mul_assoc,← Finset.sum_mul,pow_two]
  congr 1
  simp [Frame.coefficient_apply,Frame.velocity,Finset.sum_apply]

theorem Frame.coefficient_injective (e : Frame M m) {z : State} (hz : z ∈ e.chart.target) :
    Function.Injective (e.coefficient z) := by
  intro a b eq
  apply (e.independent z hz).fintypeLinearCombination_injective
  simpa only [Fintype.linearCombination_apply,e.coefficient_apply,Frame.velocity] using eq

private def gram (e : Frame M m) (z : State) := (coanalysis e z).comp (e.coefficient z)

private theorem gram_unit (e : Frame M m) {z : State} (hz : z ∈ e.chart.target) : IsUnit (gram e z) := by
  have inj : Function.Injective (gram e z) := by
    apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro a ha
    change coanalysis e z (e.coefficient z a) = 0 at ha
    have sum := gram_pairing e z a
    rw [ha] at sum
    simp only [Pi.zero_apply,mul_zero,Finset.sum_const_zero] at sum
    have vel : e.coefficient z a = 0 := by
      ext j
      exact sq_eq_zero_iff.mp ((Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp sum.symm j (Finset.mem_univ _))
    exact e.coefficient_injective hz (vel.trans (map_zero _).symm)
  let B := (LinearEquiv.ofBijective (gram e z).toLinearMap ⟨inj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp inj⟩).toContinuousLinearEquiv
  exact ⟨⟨gram e z,B.symm.toContinuousLinearMap,ContinuousLinearMap.ext B.apply_symm_apply,
    ContinuousLinearMap.ext B.symm_apply_apply⟩,rfl⟩

/-- A smooth left inverse on the entire independent-frame chart. It
recovers local control coordinates from the actual ambient Sobolev velocity. -/
def Frame.recover (e : Frame M m) (z : State) : State →L[ℝ] Fiber m :=
  (Ring.inverse (gram e z)).comp (coanalysis e z)

theorem Frame.recover_smooth (e : Frame M m) : ContDiffOn ℝ ∞ e.recover e.chart.target := by
  intro z hz
  have col : ContDiffAt ℝ ∞ (coanalysis e) z := by
    unfold coanalysis
    apply ContDiffAt.sum
    intro i _
    apply ContDiffAt.sum
    intro j _
    have h : ContDiffAt ℝ ∞ (fun p => e.X i p j) z :=
      (ContinuousLinearMap.proj j : State →L[ℝ] ℝ).contDiff.contDiffAt.comp z
        ((e.smooth i z hz).contDiffAt (e.chart.open_target.mem_nhds hz))
    exact h.smul contDiffAt_const
  have g : ContDiffAt ℝ ∞ (gram e) z := col.clm_comp
    ((e.coefficient_smooth z hz).contDiffAt (e.chart.open_target.mem_nhds hz))
  obtain ⟨b,hb⟩ := gram_unit e hz
  have inv : ContDiffAt ℝ ∞ Ring.inverse (gram e z) := hb ▸ contDiffAt_ringInverse ℝ b
  exact ((inv.comp z g).clm_comp col).contDiffWithinAt

theorem Frame.recover_coefficient (e : Frame M m) {z : State} (hz : z ∈ e.chart.target) (a : Fiber m) :
    e.recover z (e.coefficient z a) = a := DFunLike.congr_fun (Ring.inverse_mul_cancel _ (gram_unit e hz)) a

#print axioms Frame.recover_smooth
#print axioms Frame.recover_coefficient
end MinimizingSard.Five
