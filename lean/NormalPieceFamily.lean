import CompactArcFamily
import NormalFamilies
import ClockControls

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology ContDiff Manifold
namespace MinimizingSard.Five
open Volterra
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M]

private theorem coefficient_family {m : ℕ} (e : Frame M m) (S : Phase → C(Time,Phase)) (ξ : Phase)
    (ds : DifferentiableAt ℝ S ξ) (inside : ∀ t, (S ξ t).1 ∈ e.chart.target) (θ : C(Time,Time)) :
    ∃ B : Phase → C(Time,Fiber m), DifferentiableAt ℝ B ξ ∧ ∀ᶠ a in 𝓝 ξ, ∀ t,
      B a t = normalCoefficients e.X (S a (θ t)) := by
  let U : Set Phase := Prod.fst ⁻¹' e.chart.target
  have ou : IsOpen U := e.chart.open_target.preimage continuous_fst
  have cn : ContDiffOn ℝ 1 (normalCoefficients e.X) U := by
    intro p hp
    apply ContDiffAt.contDiffWithinAt
    apply contDiffAt_pi.mpr
    intro i
    have xi := (e.smooth i).contDiffAt (e.chart.open_target.mem_nhds (show p.1 ∈ e.chart.target from hp))
    exact contDiffAt_snd.clm_apply ((xi.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by decide)).comp p contDiffAt_fst)
  let A := reparamPath θ ∘ S
  have da : DifferentiableAt ℝ A ξ := (reparamPath (E := Phase) θ).differentiableAt.comp ξ ds
  obtain ⟨Y,V,cy,ov,sub,_,agree⟩ := compact_smooth_extension U (range (A ξ)) ou
    (isCompact_range (A ξ).continuous) (range_nonempty _) (range_subset_iff.mpr fun t => inside (θ t)) _ cn
  have ev := ContinuousMap.eventually_mapsTo isCompact_univ ov
    (show MapsTo (A ξ) univ V from fun t _ => sub (mem_range_self t))
  refine ⟨pathField Y cy.continuous ∘ A,((pathField_smooth Y cy).differentiable (by decide) _).comp ξ da,?_⟩
  filter_upwards [da.continuousAt.tendsto ev] with a ha using fun t => agree (ha (mem_univ t))

/-- Reconstruct a true horizontal segment on a prescribed clock from a
classical Hamiltonian arc and its measured L² coefficients. -/
theorem clocked_normal_segment {m : ℕ} (e : Frame M m) (ν : ℝ → ℝ) (iv : IntervalIntegrable ν volume 0 1)
    (nn : ∀ t, 0 ≤ ν t) (f : ℝ → Phase) (cf : Continuous f)
    (inside : ∀ t ∈ Icc 0 (arcClock ν 1), (f t).1 ∈ e.chart.target)
    (df : ∀ t ∈ Icc 0 (arcClock ν 1), HasDerivWithinAt f (hamiltonianField e.X (f t)) (Icc 0 (arcClock ν 1)) t)
    (v : Control m) (rep : ∀ᵐ t ∂controlMeasure, v t = ν t • normalCoefficients e.X (f (arcClock ν t))) :
    Segment e v (e.chart.symm (f 0).1) (e.chart.symm (f (arcClock ν 1)).1) := by
  let L := arcClock ν 1
  let σ := arcClock ν
  let z (t : ℝ) := (f (σ t)).1
  let H (s : ℝ) := (hamiltonianField e.X (f s)).1
  have pos : 0 ≤ L := intervalIntegral.integral_nonneg_of_forall zero_le_one nn
  have ch : ContinuousOn H (Icc 0 L) := fun t ht =>
    ((hamiltonianField_smoothAt e _ (inside t ht)).continuousAt.comp_continuousWithinAt (cf.continuousAt.continuousWithinAt)).fst
  have maps : MapsTo σ (Icc 0 1) (Icc 0 L) := image_subset_iff.mp (clock_range ν iv nn).2.subset
  have cσ := continuousOn_arcClock iv
  have vel : IntervalIntegrable (fun t => ν t • H (σ t)) volume 0 1 :=
    iv.smul_continuousOn (by simpa only [uIcc_of_le zero_le_one] using ch.comp cσ maps)
  have zero : σ 0 = 0 := by simp [σ,arcClock]
  have align : (fun t => e.velocity (z t) (v t)) =ᵐ[controlMeasure] (fun t => ν t • H (σ t)) := by
    filter_upwards [rep] with t ht
    change (∑ i, v t i • e.X i (z t)) = ν t • ∑ i, normalCoefficients e.X (f (σ t)) i • e.X i (z t)
    rw [ht,Finset.smul_sum]
    simp only [σ,Pi.smul_apply,smul_eq_mul,mul_smul]
  have ae (t) (ht : t ∈ Icc (0:ℝ) 1) :
      (fun r => e.velocity (z r) (v r)) =ᵐ[volume.restrict (uIoc 0 t)] (fun r => ν r • H (σ r)) := by
    rw [uIoc_of_le ht.1]
    have sub : Ioc (0:ℝ) t ⊆ Icc 0 1 := fun _ hs => ⟨hs.1.le,hs.2.trans ht.2⟩
    exact ae_restrict_of_ae_restrict_of_subset sub align
  have iz := inside 0 (left_mem_Icc.mpr pos)
  have il := inside L (right_mem_Icc.mpr pos)
  refine ⟨e.chart.map_target iz,e.chart.map_target il,z,cf.fst.continuousOn.comp cσ maps,
    fun t ht => inside _ (maps ht),by simp [z,zero,e.chart.right_inv iz],(e.chart.right_inv il).symm,
    (intervalIntegrable_congr_ae (ae _ (right_mem_Icc.mpr zero_le_one))).mpr vel,?_⟩
  intro t ht
  have dyn := forward_clock ν iv nn (fun s => (f s).1) H ch (fun s hs => (df s hs).fst) t ht
  rw [intervalIntegral.integral_congr_ae_restrict (ae t ht)]
  simpa only [z,zero] using dyn

#print axioms clocked_normal_segment

variable [IsManifold 𝓘(ℝ,State) ∞ M]

omit [IsManifold 𝓘(ℝ,State) ∞ M] in
private theorem zero_piece_family {m : ℕ} (Γ : Geometry M m) (e : Frame M m)
    (u : Control m) (z : C(Time,Phase)) (piece : NormalPiece e u z) (zero : pieceLength u = 0) :
    NormalFamily Γ e.chart e.chart (Segment e) (pieceLength u) u (z (clamp 0)) (z (clamp 1)) := by
  let ν (t : ℝ) := Real.sqrt (speedSq (u t))
  have iz := (pieceLength_clock u).symm.trans zero
  have ae := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae zero_le_one
    (f := ν) (.of_forall fun t => Real.sqrt_nonneg _) (original_speed_integrable u)).mp iz
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc] at ae
  have u0 : u = 0 := by
    apply Lp.ext
    filter_upwards [ae,piece.align,Lp.coeFn_zero (Fiber m) 2 controlMeasure] with t hv hu hz
    change ν t = 0 at hv
    change u t = ν t • _ at hu
    rw [hv,zero_smul] at hu
    exact hu.trans hz.symm
  obtain ⟨f,_,_,start,stop,_,_⟩ := piece.arc e u z
  rw [zero] at stop
  refine ⟨id,fun _ => u,start.symm.trans stop,rfl,differentiableAt_id,differentiableAt_const _,?_⟩
  filter_upwards [continuousAt_fst (e.chart.open_target.mem_nhds (piece.inside (clamp 0)))] with s hs
  exact ⟨hs,hs,u0 ▸ (zero_segment _ _ _).mpr ⟨rfl,e.chart.map_target hs⟩,zero ▸ TraceReach.zero _ _⟩

/-- Every normal piece belongs to a finite-dimensional differentiable family
with the same measured clock. Its control at the reference is the original
equivalence class; all nearby endpoints are both horizontal and Hamiltonian. -/
theorem NormalPiece.family {m : ℕ} (Γ : Geometry M m) (e : Frame M m) (he : e ∈ Γ.frames)
    (u : Control m) (z : C(Time,Phase)) (piece : NormalPiece e u z) :
    NormalFamily Γ e.chart e.chart (Segment e) (pieceLength u) u (z (clamp 0)) (z (clamp 1)) := by
  by_cases zero : pieceLength u = 0
  · exact zero_piece_family Γ e u z piece zero
  let L := pieceLength u
  have pos : 0 < L := lt_of_le_of_ne (pieceLength_nonneg u) (Ne.symm zero)
  let ν (t : ℝ) := Real.sqrt (speedSq (u t))
  let σ := arcClock ν
  have len : L = σ 1 := pieceLength_clock u
  have iv : IntervalIntegrable ν volume 0 1 := original_speed_integrable u
  have nn (t) : 0 ≤ ν t := Real.sqrt_nonneg _
  have maps : MapsTo σ (Icc 0 1) (Icc 0 L) := len ▸ image_subset_iff.mp (clock_range ν iv nn).2.subset
  have cσ : Continuous (fun t : Time => σ t) := continuousOn_iff_continuous_restrict.mp (continuousOn_arcClock iv)
  let θ : C(Time,Time) := ⟨fun t => clamp (σ (t:ℝ)/L),continuous_projIcc.comp (cσ.div_const L)⟩
  have θeq t (ht : t ∈ Icc (0:ℝ) 1) : θ (clamp t) = clamp (σ t/L) := by
    change clamp (σ ((clamp t):ℝ)/L) = _
    rw [show ((clamp t):ℝ) = t from congrArg Subtype.val (projIcc_of_mem zero_le_one ht)]
  have divIn t (ht : t ∈ Icc (0:ℝ) 1) : σ t/L ∈ Icc 0 1 :=
    ⟨div_nonneg (maps ht).1 pos.le,(div_le_one pos).mpr (maps ht).2⟩
  let U : Set Phase := Prod.fst ⁻¹' e.chart.target
  have cu : ContDiffOn ℝ 1 (hamiltonianField e.X) U := fun p hp =>
    ((hamiltonianField_smoothAt e p hp).of_le (by decide)).contDiffWithinAt
  obtain ⟨f,cf,im,f0,fL,ode,ref⟩ := piece.arc e u z
  obtain ⟨S,ds,sref,near⟩ := compact_arc_family U (e.chart.open_target.preimage continuous_fst)
    (hamiltonianField e.X) cu L pos f cf (fun s _ => im s) ode
  let ξ := z (clamp 0)
  change f 0 = ξ at f0
  rw [f0] at ds sref near
  have sin t : (S ξ t).1 ∈ e.chart.target := (sref t).symm ▸ im _
  obtain ⟨B,db,agree⟩ := coefficient_family e S ξ ds sin θ
  have recovers t (ht : t ∈ Icc (0:ℝ) 1) : S ξ (θ (clamp t)) = z (clamp t) := by
    rw [θeq t ht,sref,show ((clamp (σ t/L)):ℝ) = σ t/L from congrArg Subtype.val (projIcc_of_mem zero_le_one (divIn t ht)),
      show L*(σ t/L) = σ t by field_simp]
    exact ref t ht
  have orig : ∀ᵐ t ∂controlMeasure, u t = ν t • B ξ (clamp t) := by
    filter_upwards [piece.align,ae_restrict_mem measurableSet_Icc] with t ha ht
    rw [agree.self_of_nhds,recovers _ ht]
    exact ha
  obtain ⟨V,vu,dv,rep⟩ := differentiable_clock_controls u B ξ db orig
  let ev := (ContinuousMap.evalCLM ℝ (clamp 1) : C(Time,Phase) →L[ℝ] Phase)
  let F := ev ∘ S
  have t1 : ((clamp 1):ℝ) = 1 := congrArg Subtype.val (projIcc_of_mem zero_le_one (right_mem_Icc.mpr zero_le_one))
  have hit : F ξ = z (clamp 1) := by
    change S ξ (clamp 1) = _
    rw [sref,t1,mul_one,fL]
  refine ⟨F,V,hit,vu,ev.differentiableAt.comp ξ ds,dv,?_⟩
  filter_upwards [near,agree] with a ha ab
  let g (s : ℝ) := S a (clamp (s/L))
  have cg : Continuous g := (S a).continuous.comp (continuous_projIcc.comp (continuous_id.div_const _))
  have g0 : g 0 = a := by simpa only [g,zero_div] using ha.1
  have gL : g L = F a := by simp only [g,div_self pos.ne']; rfl
  have gc (s) : (g s).1 ∈ e.chart.target := ha.2.1 _
  have der (s) (hs : s ∈ Icc 0 L) : HasDerivWithinAt g (hamiltonianField e.X (g s)) (Icc 0 L) s := ha.2.2 _ hs
  have ode' := len ▸ der
  have controls : ∀ᵐ t ∂controlMeasure, V a t = ν t • normalCoefficients e.X (g (σ t)) := by
    filter_upwards [rep a,ae_restrict_mem measurableSet_Icc] with t hv ht
    rw [hv,ab,θeq _ ht]
  have path := clocked_normal_segment e ν iv nn g cg (fun s _ => gc s) ode' (V a) controls
  rw [← (show L = arcClock ν 1 from len),g0,gL] at path
  have trace := HamiltonTrace.of_chart Γ e he L g cg.continuousOn (fun s _ => gc s) der
  exact ⟨g0 ▸ gc 0,gL ▸ gc L,path,⟨_,trace,congrArg (packPhase e.chart) g0,congrArg (packPhase e.chart) gL⟩⟩

#print axioms NormalPiece.family

end MinimizingSard.Five
