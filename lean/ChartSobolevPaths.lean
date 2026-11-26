import SmoothBundleGeometry
import TangentPathLength

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
open Volterra
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] [T2Space M] {m n : ℕ}

/-- Chart definition of manifold-valued W¹,²: on every chart interval,
the coordinate path is the Bochner primitive of an ambient L² velocity. -/
def ChartSobolev (γ : C(Time,M)) : Prop :=
  ∀ (a d : ℝ), 0 ≤ a → 0 < d → a+d ≤ 1 → ∀ c : OpenPartialHomeomorph M State,
    c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M → (∀ s : Time, γ (clamp (a+d*s)) ∈ c.source) →
      ∃ p : SobolevData, ∀ s : Time, ambientPath p s = c (γ (clamp (a+d*s)))

theorem PathHasLength.chart_sobolev {Γ : Geometry M m} {γ : C(Time,M)} {l : ℝ} (hl : PathHasLength Γ γ l) : ChartSobolev γ := by
  obtain ⟨n,P,e,p,he,walk,rep,_⟩ := hl
  have family : HorizontalVariation Γ (γ (clamp 0)) (fun _ => γ) :=
    ⟨n,P,e,fun _ => p,he,differentiableAt_const _,Filter.Eventually.of_forall (fun _ => ⟨rfl,walk,rep⟩)⟩
  intro a d ha hd endT c hc inside
  let atT (s : Time) := γ (clamp (a+d*s))
  have ct : Continuous atT := γ.continuous.comp (continuous_projIcc.comp (continuous_const.add (continuous_const.mul continuous_subtype_val)))
  obtain ⟨H,V,sm,_,cover,_,same⟩ := extend_chart_observation c hc (range atT) (isCompact_range ct) (range_nonempty _) (range_subset_iff.mpr inside)
  obtain ⟨Z,_,obs⟩ := family.observe H (fun b _ => sm b.chart b.compatible)
  let z := Z 0
  obtain ⟨R,hr⟩ := restriction_operator 5 ha hd endT
  refine ⟨(ambientPath z (clamp a),R z.2),fun s => ?_⟩
  exact (ambient_restrict ha hd endT _ _ (hr z.2).1 z.1 s).trans ((obs.self_of_nhds _).trans (same (cover (mem_range_self s))))

variable [IsManifold 𝓘(ℝ,State) ∞ M]

omit [T2Space M] in
private theorem horizontal_piece {Δ : (y : M) → Submodule ℝ (Tangent y)} {g : (y : M) → Δ y → ℝ}
    {γ : C(Time,M)} (tangent : ∀ᵐ t ∂volume.restrict (Ioc (0:ℝ) 1), tangentVelocity γ t ∈ Δ (γ (clamp t)))
    (e : Frame M m) (he : RepresentsMetric e Δ g) (P : TimePartition n) (i : Fin n) (p : SobolevData)
    (src : ∀ s, γ (P.atTime i s) ∈ e.chart.source) (pos : ∀ s, ambientPath p s = e.chart (γ (P.atTime i s))) :
    e.HorizontalSobolev p := by
  refine ⟨fun s => (pos s).symm ▸ e.chart.map_source (src s),?_⟩
  let a := P.left i
  let d := P.duration i
  let f (s : ℝ) := a+d*s
  let b (t : ℝ) := (t-a)/d
  have hd : 0 < d := P.duration_pos i
  have inverse (s : ℝ) : b (f s) = s := by dsimp [b,f]; field_simp; ring
  have kept (r : ℝ) (hr : r ∈ Ioo (0:ℝ) 1) : P.atTime i (clamp r) = clamp (f r) := by
    have cr : ((clamp r):ℝ) = r := by unfold clamp; rw [projIcc_of_mem _ ⟨hr.1.le,hr.2.le⟩]
    have eq : ((P.atTime i (clamp r)):ℝ) = f r := by change a+d*((clamp r):ℝ) = _; rw [cr]
    rw [← eq]; exact (projIcc_val _ _).symm
  have qmp : Measure.QuasiMeasurePreserving f (volume : Measure ℝ) volume :=
    (measurePreserving_add_left volume a).quasiMeasurePreserving.comp (Measure.quasiMeasurePreserving_smul volume hd.ne')
  rw [ae_restrict_iff' measurableSet_Ioc] at tangent
  have prim := (ambient_primitive p).ae_derivative
  rw [ae_restrict_iff' measurableSet_Ioo] at prim
  let pred (r : ℝ) := p.2 r ∈ LinearMap.range (e.coefficient (ambientPath p (clamp r))).toLinearMap
  change ∀ᵐ r ∂volume.restrict (Icc (0:ℝ) 1), pred r
  rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc,ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [prim,qmp.ae tangent] with r dr tan
  intro hr
  have clock := kept r hr
  have inside : γ (clamp (f r)) ∈ e.chart.source := clock ▸ src (clamp r)
  have tan' := tan (show f r ∈ Ioc (0:ℝ) 1 from ⟨add_pos_of_nonneg_of_pos (P.cut_mem i.castSucc).1 (mul_pos hd hr.1),
    (add_le_add_left (mul_le_of_le_one_right hd.le hr.2.le) _).trans ((P.end_eq i).symm ▸ (P.cut_mem i.succ).2)⟩)
  have db : HasDerivAt b d⁻¹ (f r) := by simpa [b,one_div] using ((hasDerivAt_id (f r)).sub_const a).div_const d
  have eq : (fun s => e.chart (γ (clamp s))) =ᶠ[𝓝 (f r)] ((fun v => ambientPath p (clamp v)) ∘ b) := by
    have valid : b (f r) ∈ Ioo (0:ℝ) 1 := (inverse r).symm ▸ hr
    filter_upwards [db.continuousAt (isOpen_Ioo.mem_nhds valid)] with s hs
    have one := pos (clamp (b s))
    have back : f (b s) = s := by dsimp [b,f]; field_simp; ring
    rw [kept _ hs,back] at one
    exact one.symm
  have dr' := dr hr
  have phy := (((inverse r).symm ▸ dr').scomp (f r) db).congr_of_eventuallyEq eq
  have tv := tangentVelocity_of_chart_deriv e γ (f r) _ inside phy
  obtain ⟨L,hL⟩ := he _ inside
  let u := L.symm ⟨_,tan'⟩
  have param : (L u : Tangent _) = tangentVelocity γ (f r) := congrArg Subtype.val (L.apply_symm_apply ⟨_,tan'⟩)
  have id := e.tangentMap_injective inside ((hL u).1.symm.trans (param.trans tv))
  refine ⟨d • u,?_⟩
  change e.coefficient (ambientPath p (clamp r)) (d • u) = p.2 r
  rw [pos,clock,map_smul]
  change (e.coefficient (e.chart (γ (clamp (f r))))) u = d⁻¹ • p.2 (b (f r)) at id
  rw [id,inverse,smul_inv_smul₀ hd.ne']

theorem path_length_iff_intrinsic {Γ : Geometry M m} {Δ : (y : M) → Submodule ℝ (Tangent y)} {g : (y : M) → Δ y → ℝ}
    (metric : ∀ e ∈ Γ.frames, RepresentsMetric e Δ g) (γ : C(Time,M)) (l : ℝ) :
    PathHasLength Γ γ l ↔ ChartSobolev γ ∧
      (∀ᵐ t ∂volume.restrict (Ioc (0:ℝ) 1), tangentVelocity γ t ∈ Δ (γ (clamp t))) ∧ tangentLength Δ g γ = l := by
  refine ⟨fun h => ⟨h.chart_sobolev,h.tangent_metric metric⟩,?_⟩
  rintro ⟨sob,tan,rfl⟩
  obtain ⟨k,P,e,he,inside⟩ := path_frame_subcover Γ γ
  cases k with
  | zero => have h := P.last; rw [show Fin.last 0 = 0 from rfl,P.first] at h; norm_num at h
  | succ n =>
    have src (i s) := inside i _ (P.atTime_mem i s)
    have clock (i) (s : Time) : clamp (P.left i+P.duration i*s) = P.atTime i s := projIcc_of_mem _ (P.atTime i s).property
    choose p pos using fun i => sob (P.left i) (P.duration i) (P.cut_mem i.castSucc).1 (P.duration_pos i)
      ((P.end_eq i).symm ▸ (P.cut_mem i.succ).2) (e i).chart (e i).compatible (fun s => (clock i s).symm ▸ src i s)
    have atP (i s) : ambientPath (p i) s = (e i).chart (γ (P.atTime i s)) := by simpa only [clock] using pos i s
    have hor (i) := horizontal_piece tan (e i) (metric _ (he i)) P i (p i) (src i) (atP i)
    have walk : SobolevJoins e p (γ (clamp 0)) (γ (clamp 1)) := by
      refine ⟨fun j => γ (P.unitCut j),?_,?_,fun i => ?_⟩
      · apply congrArg γ; apply Subtype.ext; simp [TimePartition.unitCut,P.first,clamp]
      · apply congrArg γ; apply Subtype.ext; simp [TimePartition.unitCut,P.last,clamp]
      · exact ⟨by simpa using src i (clamp 0),by simpa using src i (clamp 1),
          by simpa only [P.atTime_zero,(ambient_primitive (p i)).at_zero] using atP i (clamp 0),
          by simpa only [P.atTime_one] using atP i (clamp 1),hor i⟩
    have rep : RepresentsPath P e p γ := by
      intro i t ht
      rw [atP,P.atTime_clock i t ht,(e i).chart.left_inv (P.atTime_clock i t ht ▸ src i (P.localClock i t))]
    have h : PathHasLength Γ γ (sobolevLength e p) := ⟨n,P,e,p,he,walk,rep,rfl⟩
    exact (h.tangent_metric metric).2.symm ▸ h

#print axioms PathHasLength.chart_sobolev
#print axioms path_length_iff_intrinsic
end MinimizingSard.Five
