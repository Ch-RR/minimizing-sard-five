import GlobalSobolevCurves

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
open Volterra
variable {n : ℕ}

theorem ambientPath_injective : Function.Injective ambientPath := by
  intro p z h
  have g := ambient_primitive p
  have b := ambient_primitive z
  rw [h] at g
  have ini := g.at_zero.symm.trans b.at_zero
  exact Prod.ext ini (g.velocity_unique (ini.symm ▸ b))

def TimePartition.atTime (P : TimePartition n) (i : Fin n) (t : Time) : Time :=
  ⟨P.left i+P.duration i*t,add_nonneg (P.cut_mem i.castSucc).1 (mul_nonneg (P.duration_pos i).le t.2.1),
    (add_le_add_left (mul_le_of_le_one_right (P.duration_pos i).le t.2.2) _).trans ((P.end_eq i).symm ▸ (P.cut_mem i.succ).2)⟩

theorem TimePartition.atTime_mem (P : TimePartition n) (i : Fin n) (t : Time) :
    ((P.atTime i t):ℝ) ∈ Icc (P.left i) (P.cut i.succ) := by
  exact ⟨le_add_of_nonneg_right (mul_nonneg (P.duration_pos i).le t.2.1),
    (add_le_add_left (mul_le_of_le_one_right (P.duration_pos i).le t.2.2) _).trans_eq (P.end_eq i)⟩

theorem TimePartition.clock_atTime (P : TimePartition n) (i : Fin n) (t : Time) :
    P.localClock i (P.atTime i t) = t := by
  unfold TimePartition.localClock
  change clamp ((P.left i+P.duration i*(t:ℝ)-P.left i)/P.duration i) = t
  rw [add_sub_cancel_left,mul_div_cancel_left₀ _ (P.duration_pos i).ne']
  exact projIcc_val _ _

theorem TimePartition.atTime_clock (P : TimePartition n) (i : Fin n) (t : Time)
    (ht : (t:ℝ) ∈ Icc (P.left i) (P.cut i.succ)) : P.atTime i (P.localClock i t) = t := by
  have d := P.duration_pos i
  have good : ((t:ℝ)-P.left i)/P.duration i ∈ Icc (0:ℝ) 1 :=
    ⟨div_nonneg (sub_nonneg.mpr ht.1) d.le,(div_le_one d).mpr (by linarith [ht.2,P.end_eq i])⟩
  apply Subtype.ext
  change P.left i+P.duration i*((clamp (((t:ℝ)-P.left i)/P.duration i)):ℝ) = t
  unfold clamp
  rw [projIcc_of_mem _ good]
  change P.left i+P.duration i*(((t:ℝ)-P.left i)/P.duration i) = _
  field_simp
  ring

/-- The same geometric curve determines the entire ambient Sobolev
coordinate uniquely for a fixed frame sequence and physical partition. -/
theorem RepresentsPath.unique_data {M : Type*} [TopologicalSpace M] [ChartedSpace State M] {m : ℕ}
    {P : TimePartition n} {e : Fin n → Frame M m} {p z : Fin n → SobolevData} {γ : C(Time,M)}
    (a : RepresentsPath P e p γ) (b : RepresentsPath P e z γ)
    (hp : ∀ i t, ambientPath (p i) t ∈ (e i).chart.target)
    (hz : ∀ i t, ambientPath (z i) t ∈ (e i).chart.target) : p = z := by
  funext i
  apply ambientPath_injective
  apply ContinuousMap.ext
  intro t
  have h := (a i _ (P.atTime_mem i t)).symm.trans (b i _ (P.atTime_mem i t))
  rw [P.clock_atTime] at h
  exact (e i).chart.symm.injOn (hp i t) (hz i t) h

theorem ambient_restrict {a d : ℝ} (ha : 0 ≤ a) (hd : 0 < d) (he : a+d ≤ 1)
    (U v : Control 5) (rep : ∀ᵐ s ∂controlMeasure, v s = d • U (a+d*s))
    (x : State) (s : Time) :
    ambientPath (ambientPath (x,U) (clamp a),v) s = ambientPath (x,U) (clamp (a+d*s)) := by
  have ha1 : a ≤ 1 := (le_add_of_nonneg_right hd.le).trans he
  have low : a ≤ a+d*s := le_add_of_nonneg_right (mul_nonneg hd.le s.2.1)
  have high : a+d*s ≤ 1 := (add_le_add_left (mul_le_of_le_one_right hd.le s.2.2) a).trans he
  have ac : ((clamp a):ℝ) = a := by unfold clamp; rw [projIcc_of_mem _ ⟨ha,ha1⟩]
  have bc : ((clamp (a+d*s)):ℝ) = a+d*s := by unfold clamp; rw [projIcc_of_mem _ ⟨ha.trans low,high⟩]
  have ig := (ambient_primitive (x,U)).1
  have sub (b c : ℝ) (hb : 0 ≤ b) (hbc : b ≤ c) (hc : c ≤ 1) : IntervalIntegrable (fun t => U t) volume b c :=
    ig.mono_set (by rw [uIcc_of_le hbc,uIcc_of_le zero_le_one]; exact Icc_subset_Icc hb hc)
  have diff := intervalIntegral.integral_add_adjacent_intervals (sub 0 a le_rfl ha ha1) (sub _ _ ha low high)
  have same : (fun t => v t) =ᵐ[volume.restrict (uIoc 0 (s:ℝ))] (fun t => d • U (a+d*t)) := by
    rw [uIoc_of_le s.2.1]
    exact ae_mono (Measure.restrict_mono (fun t ht => ⟨ht.1.le,ht.2.trans s.2.2⟩ : Ioc (0:ℝ) s ⊆ Icc 0 1) le_rfl) rep
  rw [(ambient_primitive (_,v)).2 s,(ambient_primitive (x,U)).2 (clamp a),
    (ambient_primitive (x,U)).2 (clamp (a+d*s)),ac,bc,intervalIntegral.integral_congr_ae_restrict same,
    intervalIntegral.integral_smul,intervalIntegral.smul_integral_comp_add_mul]
  simp only [mul_zero,add_zero,add_assoc,diff]

#print axioms ambientPath_injective
#print axioms RepresentsPath.unique_data
#print axioms ambient_restrict
end MinimizingSard.Five
