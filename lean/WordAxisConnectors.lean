import StepThreeRepair
import WordSpatialDifference

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] {m : ℕ} {Γ : Geometry M m}

abbrev ShortConnectors (Γ : Geometry M m) (c : OpenPartialHomeomorph M State) (q : State) (α : ℝ) :=
  ∃ K : ℝ, ∀ᶠ p : State × State in 𝓝 (q,q),
    ∃ b ∈ attainableLengths Γ (c.symm p.1) (c.symm p.2), b ≤ K*‖p.2-p.1‖^α

abbrev AxisConnectors (Γ : Geometry M m) (c : OpenPartialHomeomorph M State) (q u : State) :=
  ∃ L : ℝ, ∀ᶠ p : State × ℝ in 𝓝 (q,0),
    ∃ b ∈ attainableLengths Γ (c.symm p.1) (c.symm (p.1+p.2 • u)), b ≤ L*Real.sqrt |p.2|

/-- Transfer a two-point length estimate through an actual smooth chart transition. -/
theorem transfer_connectors (a b : OpenPartialHomeomorph M State)
    (ha : a ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (hb : b ∈ maximalAtlas 𝓘(ℝ,State) ∞ M)
    (y : M) (ay : y ∈ a.source) (by' : y ∈ b.source) (α : ℝ) (hα : 0 ≤ α)
    (repair : ShortConnectors Γ b (b y) α) : ShortConnectors Γ a (a y) α := by
  let T := b ∘ a.symm
  have eq : T (a y) = b y := by simp [T,a.left_inv ay]
  have ct : ContDiffAt ℝ 1 T (a y) := transition_smooth a b ha hb y ay by'
  obtain ⟨L,S,hs,lip⟩ := ct.exists_lipschitzOnWith
  have same : ∀ᶠ z in 𝓝 (a y), b.symm (T z) = a.symm z := by
    have near : ∀ᶠ z in 𝓝 (a y), a.symm z ∈ b.source :=
      (a.symm.continuousAt (a.map_source ay)).tendsto (b.open_source.mem_nhds (by rwa [a.left_inv ay]))
    exact near.mono fun z hz => b.left_inv hz
  have t := eq ▸ ct.continuousAt.tendsto
  have push : Tendsto (fun p : State × State => (T p.1,T p.2)) (𝓝 (a y,a y)) (𝓝 (b y,b y)) :=
    (t.comp continuous_fst.continuousAt.tendsto).prodMk_nhds (t.comp continuous_snd.continuousAt.tendsto)
  obtain ⟨K,bound⟩ := repair
  refine ⟨max 0 K*(L:ℝ)^α,?_⟩
  filter_upwards [push bound,continuous_fst.continuousAt.tendsto (same.and hs),
    continuous_snd.continuousAt.tendsto (same.and hs)] with p h h₁ h₂
  obtain ⟨s,walk,bd⟩ := h
  change s ∈ attainableLengths Γ (b.symm (T p.1)) (b.symm (T p.2)) at walk
  rw [h₁.1,h₂.1] at walk
  have d : ‖T p.2-T p.1‖ ≤ (L:ℝ)*‖p.2-p.1‖ := by simpa only [dist_eq_norm] using lip.dist_le_mul _ h₂.2 _ h₁.2
  refine ⟨s,walk,bd.trans ?_⟩
  calc
    K*‖T p.2-T p.1‖^α ≤ (max 0 K)*‖T p.2-T p.1‖^α := mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity)
    _ ≤ _ := by simpa only [Real.mul_rpow L.coe_nonneg (norm_nonneg _),mul_assoc] using
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) d hα) (le_max_left 0 K)

/-- A signed coordinate interval is realized by reversing a positive interval
when needed. The positive parameter measures the square root of the displacement. -/
private theorem signed_axis (a : OpenPartialHomeomorph M State) (q u : State) (L : ℝ)
    (forward : ∀ᶠ p : State × ℝ in 𝓝 (q,0), 0 ≤ p.2 →
      ∃ b ∈ attainableLengths Γ (a.symm p.1) (a.symm (p.1+p.2^2 • u)), b ≤ L*p.2) :
    AxisConnectors Γ a q u := by
  let r (p : State × ℝ) := Real.sqrt |p.2|
  have cr : Continuous r := Real.continuous_sqrt.comp continuous_snd.abs
  have cz : Continuous (fun p : State × ℝ => p.1+p.2 • u) := continuous_fst.add (continuous_snd.smul continuous_const)
  have up : Tendsto (fun p : State × ℝ => (p.1,r p)) (𝓝 (q,0)) (𝓝 (q,0)) := by
    simpa [r] using (continuous_fst.prodMk cr).tendsto (q,0)
  have dn : Tendsto (fun p : State × ℝ => (p.1+p.2 • u,r p)) (𝓝 (q,0)) (𝓝 (q,0)) := by
    simpa [r] using (cz.prodMk cr).tendsto (q,0)
  refine ⟨L,?_⟩
  filter_upwards [up forward,dn forward] with p h k
  have sq : (r p)^2 = |p.2| := Real.sq_sqrt (abs_nonneg _)
  by_cases pos : 0 ≤ p.2
  · obtain ⟨v,hv,bd⟩ := h (Real.sqrt_nonneg _)
    exact ⟨v,by simpa only [sq,abs_of_nonneg pos] using hv,bd⟩
  · obtain ⟨b,walk,bd⟩ := k (Real.sqrt_nonneg _)
    change b ∈ attainableLengths Γ (a.symm (p.1+p.2 • u)) (a.symm ((p.1+p.2 • u)+(r p)^2 • u)) at walk
    rw [sq,abs_of_neg (lt_of_not_ge pos),neg_smul,add_neg_cancel_right,attainableLengths_reverse Γ] at walk
    exact ⟨b,walk,bd⟩

/-- A genuine word of order one or two gives square-root length along
its straightened axis. A genuine cubic-root connector absorbs the
third-order difference between the word and the exact straight segment. -/
theorem word_axis_connectors (a b : OpenPartialHomeomorph M State)
    (ha : a ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (hb : b ∈ maximalAtlas 𝓘(ℝ,State) ∞ M)
    (y : M) (ay : y ∈ a.source) (by' : y ∈ b.source) (u : State)
    (W : RepairWord Γ b (b y)) (ord : W.order ≤ 2)
    (axis : ∀ᶠ z in 𝓝 (a y), fderiv ℝ (b ∘ a.symm) z u = W.profile ((b ∘ a.symm) z,0))
    (repair : ShortConnectors Γ b (b y) (1/3)) : AxisConnectors Γ a (a y) u := by
  let q := a y
  let T := b ∘ a.symm
  have t0 : T q = b y := by simp [T,q,a.left_inv ay]
  have ct : ContDiffAt ℝ 2 T q := transition_smooth a b ha hb y ay by'
  let time (t : ℝ) := if W.order = 1 then t^2 else t
  have tm : ContDiff ℝ 1 time := by by_cases h : W.order = 1 <;> simp [time,h] <;> fun_prop
  have zero : time 0 = 0 := by simp [time]
  have timePow (t : ℝ) : (time t)^W.order = t^2 := by
    have h := W.positive
    rcases (show W.order = 1 ∨ W.order = 2 by omega) with h | h <;> simp [time,h]
  have tpos {t : ℝ} (ht : 0 ≤ t) : 0 ≤ time t := by by_cases h : W.order = 1 <;> simp [time,h,ht]
  have tle {t : ℝ} (ht : 0 ≤ t) (lt : t < 1) : time t ≤ t := by
    by_cases h : W.order = 1 <;> simp [time,h]; nlinarith [mul_nonneg ht (sub_nonneg.mpr lt.le)]
  let I (p : State × ℝ) := (T p.1,time p.2)
  have ci : ContDiffAt ℝ 1 I (q,0) := by
    have c₁ : ContDiffAt ℝ 1 (fun p : State × ℝ => T p.1) (q,0) :=
      (ct.of_le (by decide : (1:WithTop ℕ∞) ≤ 2)).comp (f := Prod.fst) (q,(0:ℝ)) contDiffAt_fst
    exact c₁.prodMk (tm.comp contDiff_snd).contDiffAt
  have i0 : I (q,0) = (b y,0) := Prod.ext t0 zero
  have push : Tendsto I (𝓝 (q,0)) (𝓝 (b y,0)) := i0 ▸ ci.continuousAt.tendsto
  obtain ⟨J,cj,j0,changeJ⟩ := smooth_scaled_difference 1 T q ct
  let disp (p : State × ℝ) := p.2^2 • u
  let Z (p : State × ℝ) := J (p.1,disp p,u)-W.profile (I p)
  have cd : ContDiff ℝ 1 disp := (contDiff_snd.pow 2).smul contDiff_const
  have cz : ContDiffAt ℝ 1 Z (q,0) :=
    (cj.contDiffAt.comp _ (contDiffAt_fst.prodMk (cd.contDiffAt.prodMk contDiffAt_const))).sub
      ((i0.symm ▸ W.smoothProfile).comp _ ci)
  obtain ⟨C,S,hs,lip⟩ := cz.exists_lipschitzOnWith
  have van : ∀ᶠ z in 𝓝 q, Z (z,0) = 0 := by
    filter_upwards [axis,j0] with z hz hj
    simpa [Z,disp,I,zero,hj,T] using sub_eq_zero.mpr hz
  have td : Tendsto (fun p : State × ℝ => (p.1,disp p)) (𝓝 (q,0)) (𝓝 (q,0)) := by
    simpa [disp] using (continuous_fst.prodMk cd.continuous).tendsto (q,0)
  have geom : ∀ᶠ p : State × ℝ in 𝓝 (q,0), T (p.1+disp p)-W.forward (I p) = p.2^2 • Z p := by
    filter_upwards [td changeJ,push W.expansion] with p j w
    have a := j (p.2^2) u rfl
    change W.forward (I p) = T p.1+(time p.2)^W.order • W.profile (I p) at w
    rw [timePow] at w
    change T (p.1+disp p)-T p.1 = p.2^2 • J (p.1,disp p,u) at a
    rw [w,sub_add_eq_sub_sub,a,smul_sub]
  have base : Tendsto (fun p : State × ℝ => (p.1,(0:ℝ))) (𝓝 (q,0)) (𝓝 (q,0)) :=
    continuous_fst.continuousAt.tendsto.prodMk_nhds tendsto_const_nhds
  have near : ∀ᶠ z in 𝓝 q, b.symm (T z) = a.symm z := by
    have inside : ∀ᶠ z in 𝓝 q, a.symm z ∈ b.source :=
      (a.symm.continuousAt (a.map_source ay)).tendsto (b.open_source.mem_nhds (by rwa [a.left_inv ay]))
    exact inside.mono fun z hz => b.left_inv hz
  let dest (p : State × ℝ) := p.1+disp p
  have zd : Tendsto dest (𝓝 (q,0)) (𝓝 q) := by simpa [dest,disp] using (continuous_fst.add cd.continuous).tendsto (q,0)
  have cfwd : Tendsto (fun p : State × ℝ => T p.1+(time p.2)^W.order • W.profile (I p)) (𝓝 (q,0)) (𝓝 (b y)) := by
    have c : ContinuousAt (fun p : State × ℝ => T p.1+(time p.2)^W.order • W.profile (I p)) (q,0) :=
      (ct.continuousAt.comp (f := (Prod.fst : State × ℝ → State)) (x := (q,0)) continuousAt_fst).add (((tm.continuous.continuousAt.comp continuousAt_snd).pow W.order).smul
        ((i0.symm ▸ W.smoothProfile.continuousAt).comp ci.continuousAt))
    simpa [t0,zero,zero_pow W.positive.ne'] using c.tendsto
  have fw : Tendsto (fun p => W.forward (I p)) (𝓝 (q,0)) (𝓝 (b y)) :=
    cfwd.congr' (by filter_upwards [push W.expansion] with p h using h.symm)
  obtain ⟨K,connect⟩ := repair
  let L := W.cost+(max 0 K)*(C:ℝ)^(1/3:ℝ)
  apply signed_axis a q u L
  filter_upwards [push W.paths,hs,base hs,continuous_fst.continuousAt.tendsto van,geom,
    (fw.prodMk_nhds ((t0 ▸ ct.continuousAt.tendsto).comp zd)) connect,
    continuous_fst.continuousAt.tendsto near,zd near,
    (continuous_snd.continuousAt (x := (q,(0:ℝ)))).eventually_lt_const (by norm_num : (0:ℝ)<1)]
    with p path hp hbase hz diff link id₀ id₁ small
  intro ht
  obtain ⟨s,walk,bd⟩ := path (tpos ht)
  obtain ⟨v,fixer,vd⟩ := link
  have full := attainableLengths_add walk fixer
  change s+v ∈ attainableLengths Γ (b.symm (T p.1)) (b.symm (T (dest p))) at full
  rw [id₀,id₁] at full
  have normZ : ‖Z p‖ ≤ C*|p.2| := by
    have d := lip.dist_le_mul p hp (p.1,0) hbase
    rw [hz,dist_zero_right] at d
    simpa [Prod.dist_eq,Real.dist_eq] using d
  have err : ‖T (dest p)-W.forward (I p)‖ ≤ (C:ℝ)*p.2^3 := by
    rw [show T (dest p)-W.forward (I p) = _ from diff,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    rw [abs_of_nonneg ht] at normZ
    nlinarith only [mul_le_mul_of_nonneg_left normZ (sq_nonneg p.2)]
  have root := Real.rpow_le_rpow (norm_nonneg _) err (by norm_num : 0 ≤ (1/3:ℝ))
  rw [Real.mul_rpow C.coe_nonneg (pow_nonneg ht _),← Real.rpow_natCast p.2 3,← Real.rpow_mul ht] at root
  norm_num at root
  have cost : v ≤ max 0 K * ((C:ℝ)^(1/3:ℝ)*p.2) := le_trans vd ((mul_le_mul_of_nonneg_right
    (le_max_right 0 K) (Real.rpow_nonneg (norm_nonneg _) _)).trans (mul_le_mul_of_nonneg_left root (le_max_left ..)))
  refine ⟨s+v,full,?_⟩
  dsimp [L]
  have short := bd.trans (mul_le_mul_of_nonneg_left (tle ht small) W.nonneg)
  linarith only [cost,short]

#print axioms transfer_connectors
#print axioms word_axis_connectors
end MinimizingSard.Five
