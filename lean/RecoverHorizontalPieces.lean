import IntrinsicLength
import SobolevObservation

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
open Volterra
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] {m n : ℕ}

theorem HorizontalVariation.near_horizontal {Γ : Geometry M m} {x : M} {F : ℝ → C(Time,M)}
    (family : HorizontalVariation Γ x F) : ∀ᶠ r in 𝓝 0, F r (clamp 0) = x ∧ ∃ l, PathHasLength Γ (F r) l := by
  obtain ⟨n,P,e,Z,he,_,near⟩ := family
  filter_upwards [near] with r h
  exact ⟨h.1,_,n,P,e,Z r,he,h.1.symm ▸ h.2.1,h.2.2,rfl⟩

theorem horizontal_in_requested_pieces {Γ : Geometry M m} {γ : C(Time,M)} {l : ℝ} (hl : PathHasLength Γ γ l)
    (P : TimePartition n) (e : Fin n → Frame M m) (he : ∀ i, e i ∈ Γ.frames) (p : Fin n → SobolevData)
    (inside : ∀ i s, γ (P.atTime i s) ∈ (e i).chart.source)
    (pos : ∀ i s, ambientPath (p i) s = (e i).chart (γ (P.atTime i s))) :
    SobolevJoins e p (γ (clamp 0)) (γ (clamp 1)) ∧ RepresentsPath P e p γ := by
  have horizontal (i) : (e i).HorizontalSobolev (p i) := by
    refine ⟨fun s => (pos i s).symm ▸ (e i).chart.map_source (inside i s),?_⟩
    let a := P.left i
    let d := P.duration i
    let f (s : ℝ) := a+d*s
    have hd : 0 < d := P.duration_pos i
    have qmp : Measure.QuasiMeasurePreserving f (volume : Measure ℝ) volume :=
      (measurePreserving_add_left volume a).quasiMeasurePreserving.comp (Measure.quasiMeasurePreserving_smul volume hd.ne')
    have vel := hl.chart_velocity (e i) (he i)
    rw [ae_restrict_iff' measurableSet_Ioc] at vel
    have der := (ambient_primitive (p i)).ae_derivative
    rw [ae_restrict_iff' measurableSet_Ioo] at der
    have matchTime (r : ℝ) (hr : r ∈ Ioo (0:ℝ) 1) : P.atTime i (clamp r) = clamp (f r) := by
      have cr : ((clamp r):ℝ) = r := by unfold clamp; rw [projIcc_of_mem _ ⟨hr.1.le,hr.2.le⟩]
      have eq : ((P.atTime i (clamp r)):ℝ) = f r := by change a+d*((clamp r):ℝ) = _; rw [cr]
      rw [← eq]
      exact (projIcc_val _ _).symm
    have int (r : ℝ) (hr : r ∈ Ioo (0:ℝ) 1) : f r ∈ Ioc (0:ℝ) 1 := by
      exact ⟨add_pos_of_nonneg_of_pos (P.cut_mem i.castSucc).1 (mul_pos hd hr.1),
        (add_le_add_left (mul_le_of_le_one_right hd.le hr.2.le) _).trans ((P.end_eq i).symm ▸ (P.cut_mem i.succ).2)⟩
    change ∀ᵐ r ∂volume.restrict (Icc (0:ℝ) 1), _
    let pred (r : ℝ) := (p i).2 r ∈ LinearMap.range ((e i).coefficient (ambientPath (p i) (clamp r))).toLinearMap
    change ∀ᵐ r ∂volume.restrict (Icc (0:ℝ) 1), pred r
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc,ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [der,qmp.ae vel] with r dr vr
    intro hr
    have clock := matchTime r hr
    obtain ⟨v,dv⟩ := vr (int r hr) (clock ▸ inside i (clamp r))
    have df : HasDerivAt f d r := by simpa [f] using ((hasDerivAt_id r).const_mul d).const_add a
    have same : (fun s => ambientPath (p i) (clamp s)) =ᶠ[𝓝 r] ((fun s => (e i).chart (γ (clamp s))) ∘ f) := by
      filter_upwards [isOpen_Ioo.mem_nhds hr] with s hs
      simpa only [Function.comp_apply,← matchTime s hs] using pos i (clamp s)
    refine ⟨d • v,?_⟩
    change (e i).coefficient (ambientPath (p i) (clamp r)) (d • v) = (p i).2 r
    rw [map_smul,pos i,clock]
    exact ((dv.scomp r df).congr_of_eventuallyEq same).unique (dr hr)
  refine ⟨⟨fun j => γ (P.unitCut j),?_,?_,fun i => ?_⟩,?_⟩
  · apply congrArg γ; apply Subtype.ext; simp [TimePartition.unitCut,P.first,clamp]
  · apply congrArg γ; apply Subtype.ext; simp [TimePartition.unitCut,P.last,clamp]
  · exact ⟨by simpa using inside i (clamp 0),by simpa using inside i (clamp 1),
      by simpa only [P.atTime_zero,(ambient_primitive (p i)).at_zero] using pos i (clamp 0),
      by simpa only [P.atTime_one] using pos i (clamp 1),horizontal i⟩
  · intro i t ht
    have g := pos i (P.localClock i t)
    have s := inside i (P.localClock i t)
    rw [P.atTime_clock i t ht] at g s
    rw [g,(e i).chart.left_inv s]

#print axioms HorizontalVariation.near_horizontal
#print axioms horizontal_in_requested_pieces
end MinimizingSard.Five
