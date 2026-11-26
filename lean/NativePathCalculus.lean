import IntrinsicHilbertSard
import Mathlib.Geometry.Manifold.ContMDiff.Defs

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
open Volterra
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] [T2Space M] [IsManifold 𝓘(ℝ,State) ∞ M]
variable {m : ℕ} {Δ : (y : M) → Submodule ℝ (Tangent y)} {g : (y : M) → Δ y → ℝ}

theorem native_endpoint_smooth (Γ : Geometry M m) (x : M) :
    ContMDiff 𝓘(ℝ,PathModel m) 𝓘(ℝ,State) ∞ (HorizontalPaths.endpoint (Γ := Γ) (x := x)) := by
  intro γ
  let A := (ControlChart.exists_chart γ).choose
  let c := chartAt State γ.endpoint
  obtain ⟨u,hu⟩ := (ControlChart.exists_chart γ).choose_spec
  obtain ⟨p,path,_,codes⟩ := (show A.Graph γ u from hu)
  have atU : extChartAt 𝓘(ℝ,PathModel m) γ γ = u := A.encode_eq hu
  refine contMDiffAt_iff.mpr ⟨(path_eval_continuous Γ x (clamp 1)).continuousAt,?_⟩
  rw [atU]
  apply ContDiffAt.contDiffWithinAt
  apply contDiffAt_infty.mpr
  intro k
  obtain ⟨_,_,G,_,_,_,_,_,dg,fw,_⟩ := sobolev_chain_chart A.frames p (A.split u) x γ.endpoint path codes
    c (chart_mem_maximalAtlas _) (mem_chart_source _ _) (k+1) (by omega)
  have d : ContDiffAt ℝ (k+1 : ℕ) (G ∘ A.split) u := dg.comp u A.split.contDiff.contDiffAt
  apply (d.of_le (by exact_mod_cast Nat.le_succ k)).congr_of_eventuallyEq
  filter_upwards [(A.decode_family hu 1 le_rfl).2,A.split.continuous.continuousAt.tendsto fw] with v hv hg
  obtain ⟨β,hβ⟩ := hv
  change c (A.decode v).endpoint = G (A.split v)
  rw [A.decode_eq hβ]
  obtain ⟨z,w,_,cv⟩ := hβ
  exact (congrArg c ((hg.2.1 _).mp (w.control cv))).trans (c.right_inv hg.1)

omit [T2Space M] [IsManifold 𝓘(ℝ,State) ∞ M] in
theorem tangentVelocity_eq_mfderiv (γ : C(Time,M)) (r : ℝ) :
    tangentVelocity γ r = mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,State) (fun s : ℝ => γ (clamp s)) r (1 : ℝ) := by
  let f (s : ℝ) := γ (clamp s)
  let v (s : ℝ) := chartAt State (f r) (f s)
  have w : writtenInExtChartAt 𝓘(ℝ,ℝ) 𝓘(ℝ,State) r f = v := rfl
  have loc : extChartAt 𝓘(ℝ,ℝ) r r = r := rfl
  have fullRange : range (𝓘(ℝ,ℝ) : ℝ → ℝ) = univ := range_id
  have test : MDifferentiableAt 𝓘(ℝ,ℝ) 𝓘(ℝ,State) f r ↔ DifferentiableAt ℝ v r := by
    rw [mdifferentiableAt_iff,w,loc,fullRange,differentiableWithinAt_univ]
    exact and_iff_right (γ.continuous.comp continuous_projIcc).continuousAt
  change deriv v r = mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,State) f r (1 : ℝ)
  rw [mfderiv,w,loc,fullRange,fderivWithin_univ]
  by_cases h : DifferentiableAt ℝ v r
  · rw [if_pos (test.mpr h)]
    rfl
  · rw [if_neg (fun h' => h (test.mp h')),deriv_zero_of_not_differentiableAt h]
    rfl

def PathAtlas.smoothEndpoint {Q : C(Time,M) → Prop} (A : PathAtlas Q m) : Prop :=
  letI := A.topology
  letI := A.charts
  ContMDiff 𝓘(ℝ,PathModel m) 𝓘(ℝ,State) ∞ (fun γ : Subtype Q => γ.val (clamp 1))

omit [T2Space M] [IsManifold 𝓘(ℝ,State) ∞ M] in
private theorem smooth_transport {Q R : C(Time,M) → Prop} (h : Q = R) (A : PathAtlas Q m) :
    (h ▸ A : PathAtlas R m).smoothEndpoint ↔ A.smoothEndpoint := by subst R; rfl

theorem intrinsic_endpoint_smooth (geometry : HasBundleCoordinates m Δ g) (hm : 0 < m) (x : M) :
    (intrinsicPathAtlas geometry hm x).smoothEndpoint := by
  rw [intrinsicPathAtlas,smooth_transport]
  exact native_endpoint_smooth _ _

#print axioms native_endpoint_smooth
#print axioms tangentVelocity_eq_mfderiv
#print axioms intrinsic_endpoint_smooth
end MinimizingSard.Five
