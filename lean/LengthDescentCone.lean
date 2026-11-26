import LengthMultiplier

noncomputable section
open Set Filter
open scoped Topology

namespace MinimizingSard.Five

variable {m n : ℕ}

/-- Strict shortening at unit scale extends uniformly to an open cone of control directions. -/
theorem length_descent_cone (w h : Fin n → Control m) (down : length (w+h) < length w) :
    ∃ c > 0, ∀ᶠ d in 𝓝 h, ∀ t ∈ Icc (0:ℝ) 1, length (w+t • d) ≤ length w - c*t := by
  let c := (length w - length (w+h))/2
  have pos : 0 < c := by dsimp [c]; linarith
  have mid : length (w+h) < length w - c := by dsimp [c]; linarith
  have cont : Continuous (fun d => length (w+d)) :=
    continuous_control_length.comp (continuous_const.add continuous_id)
  refine ⟨c,pos,?_⟩
  filter_upwards [cont.continuousAt.eventually_lt_const mid] with d hd
  change length (w+d) < length w-c at hd
  rintro t ⟨ht,ht'⟩
  have est := convex_control_length.2 (Set.mem_univ w) (Set.mem_univ (w+d))
    (sub_nonneg.mpr ht') ht (sub_add_cancel 1 t)
  rw [smul_add,← add_assoc,← add_smul,sub_add_cancel,one_smul] at est
  change length (w+t • d) ≤ (1-t)*length w + t*length (w+d) at est
  linarith [mul_le_mul_of_nonneg_left hd.le ht]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M]
  {Γ : Geometry M m} {x y : M} {e : Fin (n+1) → Frame M m}
  {w : Fin (n+1) → Control m}

/-- For the original endpoint graph the pointed value decreases at least linearly,
uniformly near a direction in the true derivative kernel. -/
theorem actual_value_descent_cone (he : ∀ i, e i ∈ Γ.frames) (hw : Joins e w x y)
    (hmin : ∀ (k : ℕ) (d : Fin (k+1) → Frame M m) (v : Fin (k+1) → Control m),
      (∀ i, d i ∈ Γ.frames) → Joins d v x y → length w ≤ length v)
    (chart : OpenPartialHomeomorph M State) (G : (Fin (n+1) → Control m) → State)
    (graph : ∀ᶠ v in 𝓝 w, ∀ z, Joins e v x z ↔ z = chart.symm (G v))
    (absent : ¬ HasCostMultiplier length (fderiv ℝ G w) w) :
    ∃ h, fderiv ℝ G w h = 0 ∧ ∃ c > 0,
      ∀ᶠ p : ℝ × (Fin (n+1) → Control m) in 𝓝 (0,h), 0 < p.1 →
        pointedLengthValue Γ x (chart.symm (G (w+p.1 • p.2))) ≤ pointedLengthValue Γ x y - c*p.1 := by
  obtain ⟨h,ker,lt⟩ := (no_length_multiplier_iff_shorter _ _).mp absent
  obtain ⟨c,pos,cone⟩ := length_descent_cone w h lt
  have gt : Tendsto (fun p : ℝ × (Fin (n+1) → Control m) => w+p.1 • p.2) (𝓝 (0,h)) (𝓝 w) := by
    simpa using (continuous_const.add (continuous_fst.smul continuous_snd)).tendsto
      ((0:ℝ),h)
  have small : ∀ᶠ p : ℝ × (Fin (n+1) → Control m) in 𝓝 (0,h), p.1 < 1 :=
    continuous_fst.continuousAt.eventually_lt_const zero_lt_one
  refine ⟨h,ker,c,pos,?_⟩
  filter_upwards [continuous_snd.continuousAt.tendsto cone, small,
    gt (pointedLengthValue_comparison he hw hmin chart G graph)] with p save ht value
  intro hp
  change pointedLengthValue Γ x (chart.symm (G (w+p.1 • p.2))) - pointedLengthValue Γ x y ≤
    length (w+p.1 • p.2) - length w at value
  linarith [save p.1 ⟨hp.le,ht.le⟩]

#print axioms length_descent_cone
#print axioms actual_value_descent_cone

/-- A differentiable control correction preserves the length saving uniformly
as both the positive scale and the input direction vary. -/
theorem length_cone_on_radial_chart {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    (w : Fin n → Control m) (S : K → (Fin n → Control m)) (D : K →L[ℝ] (Fin n → Control m))
    (s0 : S 0 = 0) (ds : HasFDerivAt S D 0) (h : K) (down : length (w+D h) < length w) :
    ∃ c > 0, ∀ᶠ p : ℝ × K in 𝓝 (0,h), 0 < p.1 →
      length (w+S (p.1 • p.2)) ≤ length w-c*p.1 := by
  obtain ⟨c,cp,cone⟩ := length_descent_cone w (D h) down
  refine ⟨c,cp,?_⟩
  let Z := {p : ℝ × K | 0 < p.1}
  let l := 𝓝[Z] ((0:ℝ),h)
  have hp : ∀ᶠ p in l, 0 < p.1 := self_mem_nhdsWithin
  have time : Tendsto (fun p : ℝ × K => p.1) l (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨continuous_fst.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,hp⟩
  have inv : Tendsto (fun p : ℝ × K => ‖p.1⁻¹‖) l atTop :=
    (tendsto_inv_nhdsGT_zero.comp time).congr' (hp.mono fun p ht => (abs_of_pos (inv_pos.mpr ht)).symm)
  let z (p : ℝ × K) := p.1 • p.2
  have dir : Tendsto (fun p : ℝ × K => p.1⁻¹ • z p) l (𝓝 h) := by
    have tend : Tendsto (fun p : ℝ × K => p.2) l (𝓝 h) := continuous_snd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact tend.congr' (hp.mono fun p ht => (inv_smul_smul₀ ht.ne' _).symm)
  have lim := ds.hasFDerivWithinAt.lim (s := univ) l (Eventually.of_forall fun _ => mem_univ _) inv dir
  simp only [zero_add,s0,sub_zero] at lim
  have small : ∀ᶠ p in l, p.1 < 1 := (tendsto_nhdsWithin_iff.mp time).1 (Iio_mem_nhds zero_lt_one)
  apply eventually_nhdsWithin_iff.mp (show ∀ᶠ p in l, _ from ?_)
  filter_upwards [lim cone,hp,small] with p save ht lt
  have use := save p.1 ⟨ht.le,lt.le⟩
  simpa only [smul_inv_smul₀ ht.ne',z] using use

/-- Specialize the radial saving to a two-column planar endpoint test. -/
theorem length_cone_on_level_chart {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    (w : Fin n → Control m) (S : K → (Fin n → Control m)) (D : K →L[ℝ] (Fin n → Control m))
    (s0 : S 0 = 0) (ds : HasFDerivAt S D 0) (h : K) (down : length (w+D h) < length w)
    (B : (ℝ × ℝ) →L[ℝ] K) :
    ∃ c > 0, ∀ᶠ p : ℝ × (ℝ × ℝ) in 𝓝 0, 0 < p.1 →
      length (w+S (p.1 • (h+B p.2))) ≤ length w-c*p.1 := by
  obtain ⟨c,cp,cone⟩ := length_cone_on_radial_chart w S D s0 ds h down
  let T (p : ℝ × (ℝ × ℝ)) := (p.1,h+B p.2)
  have tc : Continuous T := continuous_fst.prodMk (continuous_const.add (B.continuous.comp continuous_snd))
  have push : Tendsto T (𝓝 0) (𝓝 (0,h)) := by simpa [T] using tc.tendsto 0
  exact ⟨c,cp,push cone⟩

#print axioms length_cone_on_radial_chart
#print axioms length_cone_on_level_chart
end MinimizingSard.Five
