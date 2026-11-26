import PathChartObservations
import RecoverHorizontalPieces

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
open Volterra
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] [T2Space M] {m n : ℕ}

/-- Tests on an actual family, independent of any choice of time partition:
compact-open continuity, horizontal membership and differentiability in
the ambient Sobolev norm after every global smooth observation. -/
structure ObservationVariation (Γ : Geometry M m) (x : M) (F : ℝ → C(Time,M)) : Prop where
  maps_into : ∀ (K : Set Time), IsCompact K → ∀ (U : Set M), IsOpen U → MapsTo (F 0) K U →
    ∀ᶠ r in 𝓝 0, MapsTo (F r) K U
  near_horizontal : ∀ᶠ r in 𝓝 0, F r (clamp 0) = x ∧ ∃ l, PathHasLength Γ (F r) l
  observe : ∀ H : M → State, (∀ e ∈ Γ.frames, ContDiffOn ℝ ∞ (H ∘ (e : Frame M m).chart.symm) e.chart.target) →
    ∃ z : ℝ → SobolevData, DifferentiableAt ℝ z 0 ∧ ∀ᶠ r in 𝓝 0, ∀ t, ambientPath (z r) t = H (F r t)

omit [T2Space M] in
theorem HorizontalVariation.tests {Γ : Geometry M m} {x : M} {F : ℝ → C(Time,M)} (h : HorizontalVariation Γ x F) :
    ObservationVariation Γ x F := ⟨h.maps_into,h.near_horizontal,h.observe⟩

theorem ObservationVariation.in_any_coordinates {Γ : Geometry M m} {x : M} {F : ℝ → C(Time,M)}
    (family : ObservationVariation Γ x F) (P : TimePartition (n+1)) (e : Fin (n+1) → Frame M m)
    (he : ∀ i, e i ∈ Γ.frames) (base : ∀ i s, F 0 (P.atTime i s) ∈ (e i).chart.source) :
    ∃ Z : ℝ → Fin (n+1) → SobolevData, DifferentiableAt ℝ Z 0 ∧
      ∀ᶠ r in 𝓝 0, SobolevJoins e (Z r) x (F r (clamp 1)) ∧ RepresentsPath P e (Z r) (F r) := by
  let K (i) := range (fun t => F 0 (P.atTime i t))
  have comp (i) : IsCompact (K i) := isCompact_range ((F 0).continuous.comp (P.atTime_continuous i))
  choose H V sm ov cover src eq using fun i => extend_chart_observation (e i).chart (e i).compatible
    (K i) (comp i) (range_nonempty _) (range_subset_iff.mpr (base i))
  have stay (i) : ∀ᶠ r in 𝓝 0, ∀ t, F r (P.atTime i t) ∈ V i := by
    have h := family.maps_into (range (P.atTime i)) (isCompact_range (P.atTime_continuous i)) (V i) (ov i)
      (fun _ h => by obtain ⟨t,rfl⟩ := h; exact cover i (mem_range_self t))
    exact h.mono (fun r h t => h (mem_range_self t))
  choose z dz observed using fun i => family.observe (H i) (fun b _ => sm i b.chart b.compatible)
  choose R hR using fun i => restriction_operator 5 (a := P.left i) (P.cut_mem i.castSucc).1
    (P.duration_pos i) ((P.end_eq i).symm ▸ (P.cut_mem i.succ).2)
  let A (i : Fin (n+1)) : SobolevData →L[ℝ] SobolevData :=
    (((ContinuousMap.evalCLM ℝ (clamp (P.left i))).comp ambientPath)).prod
      ((R i).comp (ContinuousLinearMap.snd ℝ State (Control 5)))
  let Z (r : ℝ) (i : Fin (n+1)) := A i (z i r)
  refine ⟨Z,differentiableAt_pi.mpr (fun i => (A i).differentiableAt.comp 0 (dz i)),?_⟩
  filter_upwards [Filter.eventually_all.mpr stay,Filter.eventually_all.mpr observed,family.near_horizontal] with r near obs hor
  obtain ⟨l,hl⟩ := hor.2
  have pos (i s) : ambientPath (Z r i) s = (e i).chart (F r (P.atTime i s)) := by
    have tr := ambient_restrict (a := P.left i) (P.cut_mem i.castSucc).1 (P.duration_pos i)
      ((P.end_eq i).symm ▸ (P.cut_mem i.succ).2) (z i r).2 _ ((hR i _).1) (z i r).1 s
    have clock : clamp (P.left i+P.duration i*s) = P.atTime i s := projIcc_of_mem _ (P.atTime i s).property
    rw [clock] at tr
    exact tr.trans ((obs i _).trans (eq i (near i s)))
  have path := horizontal_in_requested_pieces hl P e he (Z r) (fun i s => src i (near i s)) pos
  exact ⟨hor.1 ▸ path.1,path.2⟩

theorem HorizontalVariation.in_any_coordinates {Γ : Geometry M m} {x : M} {F : ℝ → C(Time,M)}
    (family : HorizontalVariation Γ x F) (P : TimePartition (n+1)) (e : Fin (n+1) → Frame M m)
    (he : ∀ i, e i ∈ Γ.frames) (base : ∀ i s, F 0 (P.atTime i s) ∈ (e i).chart.source) :
    ∃ Z : ℝ → Fin (n+1) → SobolevData, DifferentiableAt ℝ Z 0 ∧
      ∀ᶠ r in 𝓝 0, SobolevJoins e (Z r) x (F r (clamp 1)) ∧ RepresentsPath P e (Z r) (F r) :=
  family.tests.in_any_coordinates P e he base

theorem observationVariation_iff {Γ : Geometry M m} {x : M} {F : ℝ → C(Time,M)} :
    ObservationVariation Γ x F ↔ HorizontalVariation Γ x F := by
  refine ⟨fun h => ?_,HorizontalVariation.tests⟩
  obtain ⟨l,n,P,e,p,he,walk,rep,_⟩ := h.near_horizontal.self_of_nhds.2
  obtain ⟨_,_,_,edge⟩ := walk
  have base (i s) : F 0 (P.atTime i s) ∈ (e i).chart.source := by
    rw [rep i _ (P.atTime_mem i s),P.clock_atTime]
    exact (e i).chart.map_target ((edge i).2.2.2.2.1 s)
  obtain ⟨Z,dz,coords⟩ := h.in_any_coordinates P e he base
  refine ⟨n,P,e,Z,he,dz,?_⟩
  filter_upwards [coords,h.near_horizontal] with r hr ht using ⟨ht.1,hr⟩

theorem curve_singular_iff_presentation {Γ : Geometry M m} {x : M} {γ : C(Time,M)}
    {P : TimePartition (n+1)} {e : Fin (n+1) → Frame M m} {p : Fin (n+1) → SobolevData}
    (he : ∀ i, e i ∈ Γ.frames) (path : SobolevJoins e p x (γ (clamp 1))) (rep : RepresentsPath P e p γ) :
    CurveSingular Γ x γ ↔ SobolevSingular e p x (γ (clamp 1)) := by
  refine ⟨fun h => h.in_presentation he rep,?_⟩
  rintro ⟨c,hc,dst,η,nz,test⟩
  refine ⟨c,hc,dst,η,nz,?_⟩
  intro F f0 variation derivable
  obtain ⟨q,_,_,edge⟩ := path
  have valid (i s) : ambientPath (p i) s ∈ (e i).chart.target := (edge i).2.2.2.2.1 _
  have base (i s) : F 0 (P.atTime i s) ∈ (e i).chart.source := by
    rw [f0,rep i _ (P.atTime_mem i s),P.clock_atTime]
    exact (e i).chart.map_target (valid i s)
  obtain ⟨Z,dz,hz⟩ := variation.in_any_coordinates P e he base
  have center := hz.self_of_nhds
  obtain ⟨_,_,_,zc⟩ := center.1
  have zp := (f0 ▸ center.2).unique_data rep (fun i => (zc i).2.2.2.2.1) valid
  have good := variation.maps_into {clamp 1} isCompact_singleton c.source c.open_source (by simpa [MapsTo,f0] using dst)
  refine test Z _ zp (by rw [f0]) dz derivable ?_
  filter_upwards [hz,good] with r hr h
  have hy := h (mem_singleton _)
  exact ⟨c.map_source hy,(c.left_inv hy).symm ▸ hr.1⟩

#print axioms observationVariation_iff
#print axioms HorizontalVariation.in_any_coordinates
#print axioms curve_singular_iff_presentation
end MinimizingSard.Five
