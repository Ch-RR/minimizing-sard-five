import FiveDimensionalStatement
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace MinimizingSard.Five

/-- Lebesgue time differentiation of a vector primitive on the chart interval. -/
theorem path_ae_velocity (z f : ℝ → State) (hi : IntervalIntegrable f volume 0 1)
    (eq : ∀ t ∈ Icc (0:ℝ) 1, z t = z 0 + ∫ s in (0:ℝ)..t, f s) :
    ∀ᵐ t ∂volume.restrict (Ioo (0:ℝ) 1), HasDerivAt z (f t) t := by
  let L (i : Fin 5) := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 5 => ℝ) i
  have h (i : Fin 5) : IntervalIntegrable (fun t => L i (f t)) volume 0 1 :=
    ⟨(L i).integrable_comp hi.1,(L i).integrable_comp hi.2⟩
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [ae_all_iff.mpr (fun i : Fin 5 => (h i).ae_hasDerivAt_integral)] with t dif ht
  apply hasDerivAt_pi.mpr
  intro i
  have d := (dif i (by rw [uIcc_of_le zero_le_one]; exact ⟨ht.1.le,ht.2.le⟩) 0
    (by rw [uIcc_of_le zero_le_one]; exact ⟨le_rfl,zero_le_one⟩)).const_add (z 0 i)
  apply d.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  have hb : IntervalIntegrable f volume 0 s := hi.mono_set (by
    rw [uIcc_of_le hs.1.le,uIcc_of_le zero_le_one]; exact Icc_subset_Icc le_rfl hs.2.le)
  change z s i = z 0 i + ∫ x in (0:ℝ)..s, L i (f x)
  rw [(L i).intervalIntegral_comp_comm hb]
  exact congrArg (fun v : State => v i) (eq s ⟨hs.1.le,hs.2.le⟩)

/-- Lebesgue time differentiation for every actual chart trajectory,
including nonconstant references of arbitrary L² norm. -/
theorem chart_ae_velocity {M : Type*} [TopologicalSpace M] [ChartedSpace State M]
    {m : ℕ} (e : Frame M m) (u : Control m) (z : ℝ → State)
    (hi : IntervalIntegrable (fun t => e.velocity (z t) (u t)) volume 0 1)
    (eq : ∀ t ∈ Icc (0:ℝ) 1, z t = z 0 + ∫ s in (0:ℝ)..t, e.velocity (z s) (u s)) :
    ∀ᵐ t ∂volume.restrict (Ioo (0:ℝ) 1), HasDerivAt z (e.velocity (z t) (u t)) t :=
  path_ae_velocity z _ hi eq

#print axioms chart_ae_velocity
end MinimizingSard.Five
