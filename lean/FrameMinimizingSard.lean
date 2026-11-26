import RankThreeAxes
import PlaneRayRepair

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] [IsManifold 𝓘(ℝ,State) ∞ M]

private abbrev AxisSupportAt (Γ : Geometry M 3) (a : OpenPartialHomeomorph M State) (x : M) (q : State) :=
  ∀ {n : ℕ} (e : Fin (n+1) → Frame M 3) (w : Fin (n+1) → Control 3) (G : (Fin (n+1) → Control 3) → State),
    (∀ i, e i ∈ Γ.frames) → Joins e w x (a.symm q) →
    (∀ (k : ℕ) (d : Fin (k+1) → Frame M 3) (b : Fin (k+1) → Control 3),
      (∀ i, d i ∈ Γ.frames) → Joins d b x (a.symm q) → length w ≤ length b) →
    (∀ᶠ v in 𝓝 w, G v ∈ a.target ∧ ∀ y, Joins e v x y ↔ y = a.symm (G v)) →
    ContDiffAt ℝ 4 G w → G w = q → Module.finrank ℝ (LinearMap.range (fderiv ℝ G w).toLinearMap) = 3 →
    ∀ i : Fin 5, Pi.single i 1 ∉ LinearMap.range (fderiv ℝ G w).toLinearMap →
      AxisConnectors Γ a q (Pi.single i 1) → ShortConnectors Γ a q (1/3) →
      HasCostMultiplier length (fderiv ℝ G w) w

set_option maxHeartbeats 800000 in
private theorem ae_axis_support (Γ : Geometry M 3) (a : OpenPartialHomeomorph M State)
    (ha : a ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (x : M) : ∀ᵐ q : State, q ∈ a.target → AxisSupportAt Γ a x q := by
  classical
  let D (s : State) := pointedLengthValue Γ x (a.symm s)
  let P := {p : Fin 5 × Fin 5 // p.1 ≠ p.2}
  choose τ hu hv using fun p : P => split_coordinate_axes p.val.1 p.val.2 p.property
  have both (p : P) := (ae_no_fixed_box D (τ p) _ _ (hu p) (hv p) 2 (by decide)).and
    (ae_no_fixed_box D (τ p) _ _ (hu p) (hv p) 3 (by decide))
  filter_upwards [ae_all_iff.mpr both,all_rank_value_repair Γ (by decide) a ha] with q exclude value
  intro aq n e w G he path minimal graph smooth eq dim i outside axis repair
  let W := LinearMap.range (fderiv ℝ G w).toLinearMap
  let u : State := Pi.single i 1
  obtain ⟨j,trans⟩ := transverse_coordinate W dim u outside
  let v : State := Pi.single j 1
  have ne : i ≠ j := by
    rintro rfl
    exact trans ((show Submodule.span ℝ {u} ≤ W ⊔ _ from le_sup_right) (Submodule.subset_span (Set.mem_singleton _)))
  obtain ⟨π,cok,pu,pv⟩ := quotient_axes W dim u v outside trans
  by_contra absent
  obtain ⟨f,g,cf,cg,f0,g0,df,dg,σ,sp,ray⟩ := shortened_plane_ray Γ a e w x he G smooth
    (graph.mono fun _ h => h.2) absent π u v pu pv cok
  have len := pointedLengthValue_eq he path minimal
  rw [eq] at ray
  let V (z : ℝ × ℝ) := D (q+z.1 • u+z.2 • v)
  have v0 : V 0 = length w := by simpa [V,D] using len
  have th := thicken_shortened_ray Γ a x q u v f g cf.continuousAt cg.continuousAt f0 g0 (length w) σ sp ray axis repair
  have save : ∀ᶠ p : ℝ × ℝ × ℝ in 𝓝 0, 0 < p.1 →
      V (f p.1+p.1^2*p.2.1,g p.1+p.1^3*p.2.2) ≤ V 0-(σ/2)*p.1 := by rwa [v0]
  obtain ⟨k,hk,A,B,s,pos,δ,dp,box⟩ := box_of_shortened_ray V f g (half_pos sp) cf cg f0 g0 df dg save
  obtain ⟨U,op,mem,cont⟩ := (value aq x ⟨length w,n,e,w,he,path,rfl⟩).1
  have region : q ∈ continuityRegion D := mem_iUnion.mpr ⟨U,mem_iUnion.mpr ⟨⟨op,cont⟩,mem⟩⟩
  have noBox := exclude (⟨(i,j),ne⟩ : P)
  have vz : V 0 = D q := by simp [V]
  rw [vz] at box
  rcases hk with rfl | rfl
  · exact noBox.1 region A B s δ pos dp box
  · exact noBox.2 region A B s δ pos dp box

variable [T2Space M]
set_option maxHeartbeats 900000 in
/-- Fixed-source minimizing Sard for arbitrary smooth horizontal rank-three
frame geometries in dimension five, including geometries with varying growth. -/
theorem rank_three_minimizing_sard : ConclusionAtRank M 3 := by
  intro Γ x c hc
  obtain ⟨S,count,atlas,axes⟩ := ae_rank_three_axes Γ c hc
  letI : Countable S := count.to_subtype
  have support (a : S) := ae_chart_overlap a.val c (atlas a.val a.property) hc
    (AxisSupportAt Γ a.val x) (ae_axis_support Γ a.val (atlas a.val a.property) x)
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [axes,ae_all_iff.mpr support,ae_rank_three_residual Γ x c hc] with q dirs all bad
  rintro ⟨y,⟨cy,n,e,w,he,path,sing,minimal⟩,rfl⟩
  obtain ⟨G,gw,cg,graph,ab⟩ := all_rank_path_endpoint e w x y path c hc cy 4 (by decide)
  have dg := cg.differentiableAt (by decide : (1:WithTop ℕ∞) ≤ 4)
  obtain ⟨rank,absent⟩ := bad y rfl cy e w he path minimal G gw dg graph (ab.mp sing)
  let W := LinearMap.range (fderiv ℝ G w).toLinearMap
  have hq := c.map_source cy
  have get := dirs hq W rank
  rw [c.left_inv cy] at get
  obtain ⟨a,mem,ay,l,out,axis,repair⟩ := get
  have ha := atlas a mem
  let P := fderiv ℝ (a ∘ c.symm) (c y)
  let H := (a ∘ c.symm) ∘ G
  have th := transition_smooth (k := 4) c a hc ha y cy ay
  have ch : ContDiffAt ℝ 4 H w := (gw.symm ▸ th).comp w cg
  have h0 : H w = a y := by simp [H,gw,c.left_inv cy]
  have dH : fderiv ℝ H w = P.comp (fderiv ℝ G w) := by
    rw [show H = _ from rfl,fderiv_comp w (gw.symm ▸ th.differentiableAt (by decide)) dg,gw]
  have image : LinearMap.range (fderiv ℝ H w).toLinearMap = W.map P.toLinearMap := by
    rw [dH]; exact LinearMap.range_comp _ _
  obtain ⟨E,eq⟩ := ContinuousLinearMap.IsInvertible.of_inverse
    (transition_left a c ha hc y ay cy) (transition_left c a hc ha y cy ay)
  have rankH : Module.finrank ℝ (LinearMap.range (fderiv ℝ H w).toLinearMap) = 3 := by
    rw [image,show P = E.toContinuousLinearMap from eq.symm]; exact (E.toLinearEquiv.finrank_map_eq W).trans rank
  have localH : ∀ᶠ v in 𝓝 w, H v ∈ a.target ∧ ∀ z, Joins e v x z ↔ z = a.symm (H v) := by
    have atw := graph.self_of_nhds
    have src : c.symm (G w) ∈ a.source := ((atw.2 y).mp path) ▸ ay
    filter_upwards [graph,((c.symm.continuousAt atw.1).comp dg.continuousAt)
      (a.open_source.mem_nhds src)] with v gv av
    have av' : c.symm (G v) ∈ a.source := av
    exact ⟨a.map_source av,fun z => by simpa only [H,Function.comp_apply,a.left_inv av'] using gv.2 z⟩
  have inside : c y ∈ (c.symm.trans a).source := ⟨hq,show c.symm (c y) ∈ a.source from (c.left_inv cy).symm ▸ ay⟩
  have avail : AxisSupportAt Γ a x (a (c.symm (c y))) := fun {N} => @all (⟨a,mem⟩ : S) inside N
  rw [c.left_inv cy] at avail
  obtain ⟨η,p⟩ := avail e w H he (by rwa [a.left_inv ay]) (by rwa [a.left_inv ay])
    localH ch h0 rankH l (image.symm ▸ out) axis repair
  exact absent ⟨η.comp P,fun v => by simpa only [dH,ContinuousLinearMap.comp_apply] using p v⟩

/-- The complete five-dimensional statement as defined by the original
piecewise orthonormal-frame endpoint and the full L² control differential. -/
theorem five_dimensional_frame_sard [SecondCountableTopology M] [ConnectedSpace M] : Statement M :=
  (statement_iff_ranks_two_three_four M).mpr
    ⟨rank_two_minimizing_sard,rank_three_minimizing_sard,rank_four_minimizing_sard⟩

#print axioms rank_three_minimizing_sard
#print axioms five_dimensional_frame_sard
end MinimizingSard.Five
