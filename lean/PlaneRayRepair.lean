import WordAxisConnectors
import RayDescentBox
import AdaptedPlaneJets

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] {m n : ℕ}

/-- The original path gives a strictly shortened smooth ray in an exact
two-dimensional slice. The realized length at each time is retained. -/
theorem shortened_plane_ray (Γ : Geometry M m) (c : OpenPartialHomeomorph M State)
    (e : Fin (n+1) → Frame M m) (w : Fin (n+1) → Control m) (x : M)
    (he : ∀ i, e i ∈ Γ.frames) (G : (Fin (n+1) → Control m) → State) (cg : ContDiffAt ℝ 4 G w)
    (graph : ∀ᶠ b in 𝓝 w, ∀ z, Joins e b x z ↔ z = c.symm (G b))
    (absent : ¬ HasCostMultiplier length (fderiv ℝ G w) w)
    (π : State →L[ℝ] (ℝ × ℝ)) (u v : State) (hu : π u = (1,0)) (hv : π v = (0,1))
    (cok : LinearMap.ker π.toLinearMap = LinearMap.range (fderiv ℝ G w).toLinearMap) :
    ∃ f g : ℝ → ℝ, ContDiffAt ℝ 3 f 0 ∧ ContDiffAt ℝ 3 g 0 ∧ f 0 = 0 ∧ g 0 = 0 ∧
      fderiv ℝ f 0 = 0 ∧ fderiv ℝ g 0 = 0 ∧ ∃ σ > 0, ∀ᶠ t in 𝓝 (0:ℝ), 0 < t →
        ∃ b ∈ attainableLengths Γ x (c.symm (G w+f t • u+g t • v)), b ≤ length w-σ*t := by
  let K := LinearMap.ker (fderiv ℝ G w).toLinearMap
  obtain ⟨h,kh,down⟩ := (no_length_multiplier_iff_shorter _ w).mp absent
  let k : K := ⟨h,kh⟩
  obtain ⟨S,s₀,cs,ds,level⟩ := plane_level_family G w cg π u v hu hv cok
  let I := (ContinuousLinearMap.id ℝ ℝ).smulRight k
  let p := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp π
  let r := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp π
  have zero (h) : π (fderiv ℝ G w h) = 0 := by
    change fderiv ℝ G w h ∈ LinearMap.ker π.toLinearMap
    rw [cok]; exact ⟨h,rfl⟩
  let f (t : ℝ) := p (G (w+S (I t))-G w)
  let g (t : ℝ) := r (G (w+S (I t))-G w)
  have jet (l : State →L[ℝ] ℝ) (ann : ∀ d, l (fderiv ℝ G w d) = 0) :
      let f := fun t : ℝ => l (G (w+S (I t))-G w)
      ContDiffAt ℝ 3 f 0 ∧ f 0 = 0 ∧ fderiv ℝ f 0 = 0 := by
    let F (z : K) := l (G (w+S z)-G w)
    obtain ⟨cf,eq,dF,_⟩ := scalar_jet G w cg l ann S s₀ cs ds
    have at₀ : ContDiffAt ℝ 3 F (I 0) := by rw [map_zero]; exact cf.of_le (by decide)
    change ContDiffAt ℝ 3 (F ∘ I) 0 ∧ F (I 0) = 0 ∧ fderiv ℝ (F ∘ I) 0 = 0
    refine ⟨at₀.comp _ I.contDiff.contDiffAt,by rwa [map_zero],?_⟩
    rw [fderiv_comp 0 (at₀.differentiableAt (by decide)) I.differentiableAt,map_zero]
    change (fderiv ℝ F 0).comp _ = _
    change fderiv ℝ F 0 = 0 at dF
    rw [dF,ContinuousLinearMap.zero_comp]
  obtain ⟨cf,f0,df⟩ := jet p (fun d => congrArg Prod.fst (zero d))
  obtain ⟨cgg,g0,dg⟩ := jet r (fun d => congrArg Prod.snd (zero d))
  obtain ⟨σ,sp,saving⟩ := length_cone_on_radial_chart w S K.subtypeL s₀ ds k down
  have ci : Tendsto I (𝓝 0) (𝓝 0) := (map_zero I) ▸ I.continuous.tendsto 0
  have push : Tendsto (fun t => w+S (I t)) (𝓝 0) (𝓝 w) := by
    have lim : Tendsto (fun t => S (I t)) (𝓝 0) (𝓝 (S 0)) := cs.continuousAt.tendsto.comp ci
    simpa only [s₀,add_zero] using (tendsto_const_nhds (x := w)).add lim
  have fixK : Tendsto (fun t : ℝ => (t,k)) (𝓝 0) (𝓝 (0,k)) := tendsto_id.prodMk_nhds tendsto_const_nhds
  refine ⟨f,g,cf,cgg,f0,g0,df,dg,σ,sp,?_⟩
  filter_upwards [push graph,ci level,fixK saving] with t gr lv save
  intro ht
  let b := w+S (I t)
  have path : Joins e b x (c.symm (G w+f t • u+g t • v)) := (gr _).mpr (congrArg c.symm lv.symm)
  exact ⟨length b,⟨n,e,b,he,path,rfl⟩,save ht⟩

/-- First move along the chosen straightened axis, then repair the
remaining displacement using the cubic bracket layer. Both costs fit
inside a prescribed fraction of the linear saving. -/
theorem thicken_shortened_ray (Γ : Geometry M m) (c : OpenPartialHomeomorph M State) (x : M)
    (q u v : State) (f g : ℝ → ℝ) (cf : ContinuousAt f 0) (cg : ContinuousAt g 0)
    (f0 : f 0 = 0) (g0 : g 0 = 0) (length₀ σ : ℝ) (sp : 0 < σ)
    (ray : ∀ᶠ t in 𝓝 (0:ℝ), 0 < t → ∃ b ∈ attainableLengths Γ x (c.symm (q+f t • u+g t • v)), b ≤ length₀-σ*t)
    (axis : AxisConnectors Γ c q u) (repair : ShortConnectors Γ c q (1/3)) :
    ∀ᶠ p : ℝ × ℝ × ℝ in 𝓝 0, 0 < p.1 →
      pointedLengthValue Γ x (c.symm (q+(f p.1+p.1^2*p.2.1) • u+(g p.1+p.1^3*p.2.2) • v)) ≤ length₀-(σ/2)*p.1 := by
  obtain ⟨L,walk⟩ := axis
  obtain ⟨K,fixer⟩ := repair
  let z (t : ℝ) := q+f t • u+g t • v
  let A (p : ℝ × ℝ × ℝ) := (z p.1,p.1^2*p.2.1)
  let B (p : ℝ × ℝ × ℝ) := (A p).1+(A p).2 • u
  let C (p : ℝ × ℝ × ℝ) := B p+(p.1^3*p.2.2) • v
  have cz : ContinuousAt z 0 := (continuousAt_const.add (cf.smul continuousAt_const)).add (cg.smul continuousAt_const)
  have ca : ContinuousAt A 0 := (cz.comp (f := Prod.fst) (x := (0:ℝ × ℝ × ℝ)) continuousAt_fst).prodMk
    ((continuousAt_fst.pow 2).mul (continuous_fst.comp continuous_snd).continuousAt)
  have cb : ContinuousAt B 0 := ca.fst.add (ca.snd.smul continuousAt_const)
  have cc : ContinuousAt C 0 := cb.add (((continuousAt_fst.pow 3).mul (continuous_snd.comp continuous_snd).continuousAt).smul continuousAt_const)
  have pushA : Tendsto A (𝓝 0) (𝓝 (q,0)) := by simpa [A,z,f0,g0] using ca.tendsto
  have pushBC : Tendsto (fun p => (B p,C p)) (𝓝 0) (𝓝 (q,q)) := by
    simpa [B,C,A,z,f0,g0] using (cb.prodMk cc).tendsto
  let cost (a b : ℝ) := L*Real.sqrt |a|+K*(|b| * ‖v‖)^(1/3:ℝ)
  have cont : Continuous (fun p : ℝ × ℝ × ℝ => cost p.2.1 p.2.2) := by
    dsimp [cost]; fun_prop (disch := norm_num)
  have small : ∀ᶠ p : ℝ × ℝ × ℝ in 𝓝 0, cost p.2.1 p.2.2 < σ/2 := (cont.continuousAt (x := (0:ℝ × ℝ × ℝ))).eventually_lt_const (by simpa [cost,Real.zero_rpow] using half_pos sp)
  filter_upwards [(continuous_fst.continuousAt (x := (0:ℝ × ℝ × ℝ))).tendsto ray,pushA walk,pushBC fixer,small]
    with p r w k low
  intro ht
  obtain ⟨b,hb,bd⟩ := r ht
  obtain ⟨a,ha,ad⟩ := w
  obtain ⟨d,hd,dd⟩ := k
  obtain ⟨N,e,w,he,path,le⟩ := attainableLengths_add (attainableLengths_add hb ha) hd
  have value := (pointedLengthValue_le he path).trans_eq le
  change pointedLengthValue Γ x (c.symm (C p)) ≤ b+a+d at value
  have endEq : C p = q+(f p.1+p.1^2*p.2.1) • u+(g p.1+p.1^3*p.2.2) • v := by dsimp [C,B,A,z]; rw [add_smul,add_smul]; abel
  have root : Real.sqrt |p.1^2*p.2.1| = p.1*Real.sqrt |p.2.1| := by
    rw [abs_mul,abs_of_nonneg (sq_nonneg _),Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq ht.le]
  have pow : ‖C p-B p‖^(1/3:ℝ) = p.1*(|p.2.2| * ‖v‖)^(1/3:ℝ) := by
    rw [show C p-B p = (p.1^3*p.2.2) • v by dsimp [C]; abel,norm_smul,Real.norm_eq_abs,
      abs_mul,abs_of_nonneg (pow_nonneg ht.le 3),mul_assoc,Real.mul_rpow (pow_nonneg ht.le 3) (by positivity),
      ← Real.rpow_natCast p.1 3,← Real.rpow_mul ht.le]
    norm_num
  change a ≤ L*Real.sqrt |p.1^2*p.2.1| at ad
  change d ≤ K*‖C p-B p‖^(1/3:ℝ) at dd
  rw [root] at ad
  rw [pow] at dd
  rw [← endEq]
  apply value.trans
  change cost p.2.1 p.2.2 < σ/2 at low
  dsimp [cost] at low
  nlinarith only [bd,ad,dd,mul_lt_mul_of_pos_right low ht]

#print axioms shortened_plane_ray
#print axioms thicken_shortened_ray
end MinimizingSard.Five
