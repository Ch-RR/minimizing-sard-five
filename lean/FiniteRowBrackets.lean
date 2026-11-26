import CausalTail
import MixedTimeJets

/-! From a finite-rank causal representation of the scalar endpoint
Hessian correction to the two terminal third-order bracket identities. -/
noncomputable section
open Set MeasureTheory
open MinimizingSard.Causal MinimizingSard.MixedTime
namespace MinimizingSard.Geometry

variable {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup U] [NormedSpace ℝ U]

theorem finite_causal_row_kills_triples
    (T : Signals U →ₗ[ℝ] Signals U) [FiniteDimensional ℝ (LinearMap.range T)]
    (causal : ∀ r : ℝ, Submodule.map T (tail r) ≤ tail r)
    (p : E →L[ℝ] ℝ) (q : E) (Y : Fin 2 → ℝ → E → E) (B : ℝ → E → E)
    (c : Fin 2 → U) (readout : Fin 2 → U →ₗ[ℝ] ℝ)
    (K : Fin 2 → Fin 2 → ℝ → ℝ → ℝ) (hK : ∀ i j, Continuous (K i j).uncurry)
    (bracket : ∀ i j t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
      K i j t s = p (VectorField.lieBracket ℝ (Y j s) (Y i t) q))
    (response : ∀ i j a b, 0 < a → a < b → b < 1 →
      ∀ᵐ t ∂volume.restrict (Ioo b 1),
        readout i (T (pulse a b (c j)) t) = ∫ s in a..b, K i j t s)
    (u v : ℝ → ℝ) (hend : B 1 = VectorField.lieBracket ℝ (Y 0 1) (Y 1 1))
    (hB : ContinuousOn (fun t => jet (B t) q) (Icc 0 1))
    (flow : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1),
      HasDerivAt (fun s => jet (Y 0 s) q) (-(v t) • jet (B t) q) t ∧
      HasDerivAt (fun s => jet (Y 1 s) q) (u t • jet (B t) q) t ∧
      (u t ≠ 0 ∨ v t ≠ 0)) :
    ∀ i, p (VectorField.lieBracket ℝ (Y i 1)
      (VectorField.lieBracket ℝ (Y 0 1) (Y 1 1)) q) = 0 := by
  obtain ⟨r,hr,hr1,zero⟩ := terminal_kernel_zero T causal
  intro i
  have mixed (s : ℝ) (hs : s ∈ Ioo r 1) (j : Fin 2) :
      p (VectorField.lieBracket ℝ (Y i 1) (Y j s) q) = 0 := by
    have interior : EqOn (fun t => K i j t s) (fun _ => 0) (Ioo s 1) :=
      fun t ht => zero (c j) (readout i) (K i j) (hK i j) (response i j)
        s t hs.1 ht.1 ht.2
    have cont : Continuous (fun t => K i j t s) :=
      (hK i j).comp (continuous_id.prodMk continuous_const)
    have boundary : (1 : ℝ) ∈ closure (Ioo s 1) := by
      rw [closure_Ioo hs.2.ne]
      exact ⟨hs.2.le,le_rfl⟩
    have value := interior.closure cont continuous_const boundary
    change K i j 1 s = 0 at value
    rw [bracket i j 1 s ⟨zero_le_one,le_rfl⟩ ⟨hr.trans hs.1.le,hs.2.le⟩,
      VectorField.lieBracket_swap, map_neg, neg_eq_zero] at value
    exact value
  exact terminal_triple_bracket p q (Y 0) (Y 1) B (Y i 1) u v hr1 hend
    (hB.mono (Icc_subset_Icc_left hr)) (fun s hs => ⟨mixed s hs 0,mixed s hs 1⟩)
    (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_left hr) flow)

#print axioms finite_causal_row_kills_triples
end MinimizingSard.Geometry
