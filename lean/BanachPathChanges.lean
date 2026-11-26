import IntrinsicCurveTheorem

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
open Volterra
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] {m : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {b : E} {k : ℕ}
variable {Γ : Geometry M m} {x : M} {F : E → C(Time,M)}

/-- Finite-order smooth dependence in a full normed parameter space. -/
def SmoothPathFamily (Γ : Geometry M m) (x : M) (F : E → C(Time,M)) (b : E) (k : ℕ) : Prop :=
  ∃ (n : ℕ) (P : TimePartition (n+1)) (e : Fin (n+1) → Frame M m) (Z : E → Fin (n+1) → SobolevData),
    (∀ i, e i ∈ Γ.frames) ∧ ContDiffAt ℝ k Z b ∧
    ∀ᶠ r in 𝓝 b, F r (clamp 0) = x ∧ SobolevJoins e (Z r) x (F r (clamp 1)) ∧ RepresentsPath P e (Z r) (F r)

theorem SmoothPathFamily.maps_into (family : SmoothPathFamily Γ x F b k) (K : Set Time) (hk : IsCompact K)
    (U : Set M) (ho : IsOpen U) (h0 : MapsTo (F b) K U) : ∀ᶠ r in 𝓝 b, MapsTo (F r) K U := by
  obtain ⟨n,P,e,Z,he,dz,near⟩ := family
  let B (i : Fin (n+1)) := P.atTime i ⁻¹' K
  let O (i : Fin (n+1)) := (e i).chart.target ∩ (e i).chart.symm ⁻¹' U
  have base (i) : MapsTo (ambientPath (Z b i)) (B i) (O i) := by
    obtain ⟨_,_,_,edge⟩ := near.self_of_nhds.2.1
    intro s hs
    have ref := near.self_of_nhds.2.2 i _ (P.atTime_mem i s)
    rw [P.clock_atTime] at ref
    exact ⟨(edge i).2.2.2.2.1 _,by change (e i).chart.symm _ ∈ U; rw [← ref]; exact h0 hs⟩
  have each (i) : ∀ᶠ r in 𝓝 b, MapsTo (ambientPath (Z r i)) (B i) (O i) := by
    let pr := (ContinuousLinearMap.proj i : (Fin (n+1) → SobolevData) →L[ℝ] SobolevData)
    have c := (ambientPath.continuous.comp pr.continuous).continuousAt.comp dz.continuousAt
    exact c.tendsto ((ContinuousMap.isOpen_setOf_mapsTo
      ((hk.isClosed.preimage (P.atTime_continuous i)).isCompact)
      ((e i).chart.continuousOn_symm.isOpen_inter_preimage (e i).chart.open_target ho)).mem_nhds (base i))
  filter_upwards [near,Filter.eventually_all.mpr each] with r hr ok
  intro t ht
  obtain ⟨i,hi⟩ := P.interval_cover t
  rw [hr.2.2 i t hi]
  exact (ok i (show P.localClock i t ∈ B i by change P.atTime i (P.localClock i t) ∈ K; rwa [P.atTime_clock i t hi])).2


theorem SmoothPathFamily.observe (family : SmoothPathFamily Γ x F b k) (H : M → State)
    (smooth : ∀ e ∈ Γ.frames, ContDiffOn ℝ ∞ (H ∘ (e : Frame M m).chart.symm) e.chart.target) :
    ∃ z : E → SobolevData, ContDiffAt ℝ k z b ∧ ∀ᶠ r in 𝓝 b, ∀ t, ambientPath (z r) t = H (F r t) := by
  obtain ⟨n,P,e,Z,he,dz,near⟩ := family
  have inside (i) : ∀ s, ambientPath (Z b i) s ∈ (e i).chart.target := by
    obtain ⟨_,_,_,edge⟩ := near.self_of_nhds.2.1
    exact (edge i).2.2.2.2.1
  choose T dT term using fun i => sobolev_coordinate_germ (e i).chart.target (e i).chart.open_target
    (H ∘ (e i).chart.symm) (smooth _ (he i)) (Z b i) (inside i) k
  obtain ⟨A,glue⟩ := P.glueAmbient
  let z (r : E) := A (fun i => T i (Z r i))
  have ds (i) : ContDiffAt ℝ k (fun r => Z r i) b := ((ContinuousLinearMap.proj i : (Fin (n+1) → SobolevData) →L[ℝ] SobolevData).contDiff.contDiffAt).comp b dz
  refine ⟨z,A.contDiff.contDiffAt.comp b (contDiffAt_pi.mpr (fun i => (dT i).comp b (ds i))),?_⟩
  have each (i) := (ds i).continuousAt.tendsto (term i)
  filter_upwards [near,Filter.eventually_all.mpr each] with r hr tt
  apply glue
  intro i s
  have ref := hr.2.2 i _ (P.atTime_mem i s)
  rw [P.clock_atTime] at ref
  exact ((tt i).2.1 s).2.trans (congrArg H ref.symm)


theorem SmoothPathFamily.in_coordinates [T2Space M] (family : SmoothPathFamily Γ x F b k)
    {n : ℕ} (P : TimePartition (n+1)) (e : Fin (n+1) → Frame M m) (he : ∀ i, e i ∈ Γ.frames)
    (base : ∀ i s, F b (P.atTime i s) ∈ (e i).chart.source) :
    ∃ Z : E → Fin (n+1) → SobolevData, ContDiffAt ℝ k Z b ∧
      ∀ᶠ r in 𝓝 b, SobolevJoins e (Z r) x (F r (clamp 1)) ∧ RepresentsPath P e (Z r) (F r) := by
  have near_horizontal : ∀ᶠ r in 𝓝 b, F r (clamp 0) = x ∧ ∃ l, PathHasLength Γ (F r) l := by
    obtain ⟨j,Q,d,Y,hd,_,near⟩ := family
    filter_upwards [near] with r h
    exact ⟨h.1,_,j,Q,d,Y r,hd,h.1.symm ▸ h.2.1,h.2.2,rfl⟩
  let K (i) := range (fun t => F b (P.atTime i t))
  have comp (i) : IsCompact (K i) := isCompact_range ((F b).continuous.comp (P.atTime_continuous i))
  choose H V sm ov cover src eq using fun i => extend_chart_observation (e i).chart (e i).compatible
    (K i) (comp i) (range_nonempty _) (range_subset_iff.mpr (base i))
  have stay (i) : ∀ᶠ r in 𝓝 b, ∀ t, F r (P.atTime i t) ∈ V i := by
    have h := family.maps_into (range (P.atTime i)) (isCompact_range (P.atTime_continuous i)) (V i) (ov i)
      (fun _ h => by obtain ⟨t,rfl⟩ := h; exact cover i (mem_range_self t))
    exact h.mono (fun r h t => h (mem_range_self t))
  choose z dz observed using fun i => family.observe (H i) (fun b _ => sm i b.chart b.compatible)
  choose R hR using fun i => restriction_operator 5 (a := P.left i) (P.cut_mem i.castSucc).1
    (P.duration_pos i) ((P.end_eq i).symm ▸ (P.cut_mem i.succ).2)
  let A (i : Fin (n+1)) : SobolevData →L[ℝ] SobolevData :=
    (((ContinuousMap.evalCLM ℝ (clamp (P.left i))).comp ambientPath)).prod
      ((R i).comp (ContinuousLinearMap.snd ℝ State (Control 5)))
  let Z (r : E) (i : Fin (n+1)) := A i (z i r)
  refine ⟨Z,contDiffAt_pi.mpr (fun i => (A i).contDiff.contDiffAt.comp b (dz i)),?_⟩
  filter_upwards [Filter.eventually_all.mpr stay,Filter.eventually_all.mpr observed,near_horizontal] with r near obs hor
  obtain ⟨l,hl⟩ := hor.2
  have pos (i s) : ambientPath (Z r i) s = (e i).chart (F r (P.atTime i s)) := by
    have tr := ambient_restrict (a := P.left i) (P.cut_mem i.castSucc).1 (P.duration_pos i)
      ((P.end_eq i).symm ▸ (P.cut_mem i.succ).2) (z i r).2 _ ((hR i _).1) (z i r).1 s
    have clock : clamp (P.left i+P.duration i*s) = P.atTime i s := projIcc_of_mem _ (P.atTime i s).property
    rw [clock] at tr
    exact tr.trans ((obs i _).trans (eq i (near i s)))
  have path := horizontal_in_requested_pieces hl P e he (Z r) (fun i s => src i (near i s)) pos
  exact ⟨hor.1 ▸ path.1,path.2⟩


#print axioms SmoothPathFamily.in_coordinates
end MinimizingSard.Five
