import GlobalSobolevCurves

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
open Volterra
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] {m n : ℕ}

/-- In physical time, the chart derivative along each open piece is
the horizontal velocity of the reassembled control. -/
theorem chart_derivative_on_block {P : TimePartition n} {e : Fin n → Frame M m}
    {p : Fin n → SobolevData} {γ : C(Time,M)} {u : Fin n → Control m} {U : Control m}
    (rep : RepresentsPath P e p γ) (sol : FrameCodes e p u) (i : Fin n)
    (back : ∀ᵐ t ∂volume.restrict (P.block i), U t = (P.duration i)⁻¹ • u i ((t-P.left i)/P.duration i)) :
    ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo (P.left i) (P.cut i.succ) →
      γ (clamp t) ∈ (e i).chart.source ∧ HasDerivAt (fun s => (e i).chart (γ (clamp s)))
        ((e i).coefficient ((e i).chart (γ (clamp t))) (U t)) t := by
  let a := P.left i
  let d := P.duration i
  let g (s : ℝ) := (s-a)/d
  let w := ambientPath (p i)
  have hd : 0 < d := P.duration_pos i
  have endpoint : a+d = P.cut i.succ := P.end_eq i
  have qmp : Measure.QuasiMeasurePreserving g (volume : Measure ℝ) volume := by
    simpa only [g,div_eq_inv_mul,sub_eq_add_neg,add_comm,Function.comp_def,smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) (inv_ne_zero hd.ne')).comp
        (measurePreserving_add_left volume (-a)).quasiMeasurePreserving
  have der := ((e i).solve_primitive (sol i)).ae_derivative
  rw [ae_restrict_iff' measurableSet_Ioo] at der
  rw [TimePartition.block,ae_restrict_iff' measurableSet_Ioc] at back
  have loc (t : ℝ) (ht : t ∈ Ioo a (P.cut i.succ)) :
      γ (clamp t) ∈ (e i).chart.source ∧ (e i).chart (γ (clamp t)) = w (clamp (g t)) := by
    have unit : t ∈ Icc (0:ℝ) 1 := ⟨(P.cut_mem i.castSucc).1.trans ht.1.le,ht.2.le.trans (P.cut_mem i.succ).2⟩
    have clock : ((clamp t:Time):ℝ) = t := by unfold clamp; rw [projIcc_of_mem _ unit]
    have h := rep i (clamp t) (clock.symm ▸ ⟨ht.1.le,ht.2.le⟩)
    have eq : P.localClock i (clamp t) = clamp (g t) := by simp only [TimePartition.localClock,clock,g,a,d]
    rw [eq] at h
    rw [h]
    exact ⟨(e i).chart.map_target ((sol i).1 _),(e i).chart.right_inv ((sol i).1 _)⟩
  filter_upwards [qmp.ae der,back] with t h htBack
  intro ht
  have gmem : g t ∈ Ioo (0:ℝ) 1 := ⟨div_pos (sub_pos.mpr ht.1) hd,(div_lt_one hd).mpr (by linarith [ht.2])⟩
  have dg : HasDerivAt g d⁻¹ t := by
    simpa [g,one_div] using ((hasDerivAt_id t).sub_const a).div_const d
  have dw := (h gmem).scomp t dg
  have same : (fun s => (e i).chart (γ (clamp s))) =ᶠ[𝓝 t] (fun s => w (clamp (g s))) :=
    by filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs using (loc s hs).2
  refine ⟨(loc t ht).1,?_⟩
  apply (dw.congr_of_eventuallyEq same).congr_deriv
  rw [(loc t ht).2,htBack ⟨ht.1,ht.2.le⟩,map_smul]

#print axioms chart_derivative_on_block
end MinimizingSard.Five
