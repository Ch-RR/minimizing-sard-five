import QuarticReturn
import RightSlopeNull

/-! Exact one-coordinate descent, including an arbitrarily flat endpoint germ. -/
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology
namespace MinimizingSard.Return

theorem interval_return (f V : ℝ → ℝ) (T C c : ℝ) (hT : 0 < T) (hC : 0 < C) (hc : 0 < c)
    (reg : ContinuousOn f (Icc 0 T)) (f0 : f 0 = 0)
    (bound : ∀ t ∈ Ioc (0:ℝ) T, |f t| ≤ C*t^2)
    (save : ∀ t ∈ Ioc (0:ℝ) T, V (f t) ≤ V 0-c*t) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∃ d r : ℝ, 0 < d ∧ 0 < r ∧
      ∀ s ∈ Ioo (0:ℝ) r, V (s^2*σ) ≤ V 0-d*s := by
  have nz : f T ≠ 0 := by
    intro eq
    have h := save T ⟨hT,le_rfl⟩
    rw [eq] at h
    linarith only [h,mul_pos hc hT]
  let σ : ℝ := if 0 < f T then 1 else -1
  have sign : σ = 1 ∨ σ = -1 := by dsimp [σ]; split <;> simp
  have endpt : 0 < σ*f T := by
    dsimp [σ]
    split <;> simp_all [lt_of_le_of_ne]
  let r := Real.sqrt (σ*f T)
  have rp : 0 < r := Real.sqrt_pos.mpr endpt
  have root := Real.sq_sqrt endpt.le
  change r^2 = σ*f T at root
  refine ⟨σ,sign,c/Real.sqrt C,r,div_pos hc (Real.sqrt_pos.mpr hC),rp,?_⟩
  intro s hs
  have reaches := intermediate_value_Icc hT.le ((continuousOn_const (c := σ)).mul reg)
  have mem : s^2 ∈ Icc (σ*f 0) (σ*f T) := by
    rw [f0,mul_zero,← root]
    exact ⟨sq_nonneg _,pow_le_pow_left₀ hs.1.le hs.2.le _⟩
  obtain ⟨t,ht,eq⟩ := reaches mem
  change σ*f t = s^2 at eq
  have tpos : 0 < t := lt_of_le_of_ne ht.1 (by
    intro h
    rw [← h,f0,mul_zero] at eq
    exact (sq_pos_of_pos hs.1).ne eq)
  have ft : f t = s^2*σ := by rcases sign with h | h <;> rw [h] at eq ⊢ <;> linarith
  have upper := bound t ⟨tpos,ht.2⟩
  have absft : |f t| = s^2 := by rcases sign with h | h <;> simp [ft,h,abs_of_nonneg (sq_nonneg s)]
  rw [absft] at upper
  have cut : s ≤ Real.sqrt C*t := by
    apply le_of_sq_le_sq _ (mul_nonneg (Real.sqrt_nonneg _) ht.1)
    rwa [mul_pow,Real.sq_sqrt hC.le]
  have lower := (div_le_iff₀ (Real.sqrt_pos.mpr hC)).mpr (by linarith only [cut] : s ≤ t*Real.sqrt C)
  have value := save t ⟨tpos,ht.2⟩
  rw [ft] at value
  apply value.trans
  apply sub_le_sub_left
  simpa only [div_mul_eq_mul_div,mul_div_assoc] using mul_le_mul_of_nonneg_left lower hc.le

/-- With one missing scalar endpoint, a strictly decreasing cost on the
kernel produces a full one-sided interval of quadratic test endpoints. -/
theorem scalar_return {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f cost : E → ℝ) (V : ℝ → ℝ) (hf : ContDiffAt ℝ 2 f 0) (hc : ContDiffAt ℝ 1 cost 0)
    (f0 : f 0 = 0) (f1 : fderiv ℝ f 0 = 0) (cz : cost 0 = 0) (strict : fderiv ℝ cost 0 ≠ 0)
    (competitors : ∀ᶠ x in 𝓝 0, V (f x) ≤ V 0+cost x) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∃ d r : ℝ, 0 < d ∧ 0 < r ∧
      ∀ s ∈ Ioo (0:ℝ) r, V (s^2*σ) ≤ V 0-d*s := by
  obtain ⟨h,down⟩ : ∃ h, coeff cost 1 0 h < 0 := by
    by_contra! no
    apply strict
    ext v
    have a := no v
    have b := no (-v)
    simp [coeff] at a b
    exact le_antisymm b a
  have ff : ∀ j ≤ 1, ∀ v : E, iteratedFDeriv ℝ j f 0 (fun _ => v) = 0 := by
    intro j hj v
    interval_cases j <;> simp [f0,f1]
  let c := -(coeff cost 1 0 h)/2
  have cp : 0 < c := by dsimp [c]; linarith
  obtain ⟨δ₁,h₁,est₁⟩ := radial_profile f 1 h hf ff zero_lt_one
  obtain ⟨δ₂,h₂,est₂⟩ := radial_profile cost 0 h hc (by
    intro j hj v
    obtain rfl : j = 0 := by omega
    simp [cz]) cp
  have co : Continuous (fun t : ℝ => t • h) := continuous_id.smul continuous_const
  have near : Tendsto (fun t : ℝ => t • h) (𝓝 0) (𝓝 0) := by simpa using co.tendsto 0
  obtain ⟨R,hR,nb⟩ := Metric.mem_nhds_iff.mp (near ((hf.eventually (by decide)).and competitors))
  let T := min R (min δ₁ δ₂) / 2
  have all := lt_min hR (lt_min h₁ h₂)
  have tp : 0 < T := half_pos all
  have small (t : ℝ) (ht : t ∈ Icc 0 T) : t < R ∧ t < δ₁ ∧ t < δ₂ := by
    have := lt_min_iff.mp (ht.2.trans_lt (half_lt_self all))
    exact ⟨this.1,lt_min_iff.mp this.2⟩
  have valid (t : ℝ) (ht : t ∈ Icc 0 T) := nb (show t ∈ ball (0:ℝ) R by
    simpa [mem_ball,Real.dist_eq,abs_of_nonneg ht.1] using (small t ht).1)
  apply interval_return (fun t => f (t • h)) V T (|coeff f 2 0 h|+1) c tp (by positivity) cp
    (fun t ht => (ContinuousAt.comp (f := fun s : ℝ => s • h) (valid t ht).1.continuousAt (co.continuousAt (x := t))).continuousWithinAt) (by simpa using f0)
  · intro t ht
    have d := (small t ⟨ht.1.le,ht.2⟩).2.1
    have est := est₁ t ht.1 d h (by simpa using h₁)
    have tri := abs_sub_le (f (t • h)/t^2) (coeff f 2 0 h) 0
    simp only [sub_zero] at tri
    change |f (t • h)/t^2-coeff f 2 0 h| < 1 at est
    apply (div_le_iff₀ (sq_pos_of_pos ht.1)).mp
    rw [abs_div,abs_of_pos (sq_pos_of_pos ht.1)] at tri
    linarith
  · intro t ht
    have m : t ∈ Icc 0 T := ⟨ht.1.le,ht.2⟩
    have est := (abs_lt.mp (est₂ t ht.1 (small t m).2.2 h (by simpa using h₂))).2
    change cost (t • h)/t^1 - coeff cost 1 0 h < c at est
    rw [pow_one] at est
    have lim : cost (t • h)/t < -c := by dsimp [c] at *; linarith only [est]
    linarith only [(valid t m).2,(div_lt_iff₀ ht.1).mp lim]

#print axioms scalar_return

/-- A common outer-null exceptional set for witnesses with one missing
coordinate along a fixed ambient axis. Both signs of that axis are included. -/
theorem scalar_witnesses_null {d : ℕ} {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (V : (Fin d → ℝ) → ℝ) (cv : Continuous V) (w : Fin d → ℝ) (S : Set (Fin d → ℝ))
    (witness : ∀ p ∈ S, ∃ (i : I) (f c : E i → ℝ),
      ContDiffAt ℝ 2 f 0 ∧ ContDiffAt ℝ 1 c 0 ∧ f 0 = 0 ∧ fderiv ℝ f 0 = 0 ∧
      c 0 = 0 ∧ fderiv ℝ c 0 ≠ 0 ∧
      ∀ᶠ v in 𝓝 0, V (p + f v • w) ≤ V p+c v) :
    volume S = 0 := by
  let dirs (n : ℕ) := if n = 0 then w else -w
  apply measure_mono_null _ (MinimizingSard.Slicing.quadratic_ray_descent_null V cv dirs)
  intro p hp
  obtain ⟨i,f,c,hf,hc,f0,f1,c0,c1,comp⟩ := witness p hp
  have model := scalar_return f c (fun v : ℝ => V (p+v • w)) hf hc f0 f1 c0 c1 (by simpa using comp)
  obtain ⟨σ,sign,D,r,hD,hr,save⟩ := model
  rcases sign with rfl | rfl
  · exact ⟨0,D,r,hD,hr,by simpa [dirs] using save⟩
  · exact ⟨1,D,r,hD,hr,by simpa [dirs] using save⟩

#print axioms scalar_witnesses_null
end MinimizingSard.Return
