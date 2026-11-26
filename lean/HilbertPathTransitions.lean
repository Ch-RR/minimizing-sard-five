import HilbertControlCharts

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
open Volterra
namespace ControlChart
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] [T2Space M] [IsManifold 𝓘(ℝ,State) ∞ M]
variable {m : ℕ} {Γ : Geometry M m} {x : M} (A : ControlChart Γ x)

omit [T2Space M] in
theorem decode_family {γ u} (h : A.Graph γ u) (k : ℕ) (hk : 1 ≤ k) :
    SmoothPathFamily Γ x (fun v => (A.decode v).val) u k ∧ ∀ᶠ v in 𝓝 u, v ∈ A.chart.target := by
  obtain ⟨p,path,_,codes⟩ := h
  obtain ⟨F,R,G,fu,_,_,df,_,_,fw,bw⟩ := sobolev_chain_chart A.frames p (A.split u) x γ.endpoint path codes
    (chartAt State γ.endpoint) (chart_mem_maximalAtlas _) (mem_chart_source _ _) k hk
  let Z := F ∘ A.split
  have dz : ContDiffAt ℝ k Z u := df.comp u A.split.contDiff.contDiffAt
  have back : ∀ᶠ v in 𝓝 u, ∀ b, SobolevJoins A.frames (Z v) x b → FrameCodes A.frames (Z v) (R (Z v)) ∧ F (R (Z v)) = Z v :=
    dz.continuousAt.tendsto (fu.symm ▸ bw)
  have good : ∀ᶠ v in 𝓝 u, v ∈ A.chart.target ∧ SobolevJoins A.frames (Z v) x (A.decode v).endpoint ∧
      RepresentsPath A.partition A.frames (Z v) (A.decode v).val := by
    filter_upwards [A.split.continuous.continuousAt.tendsto fw,back] with v front inv
    obtain ⟨_,_,walk,right⟩ := front
    obtain ⟨ξ,src,dst,rep⟩ := walk.realize A.partition
    have w : SobolevJoins A.frames (Z v) x (ξ (clamp 1)) := dst.symm ▸ walk
    let o : HorizontalPaths Γ x := ⟨ξ,src,_,A.n,A.partition,A.frames,Z v,A.member,src.symm ▸ w,rep,rfl⟩
    have present : A.Graph o v := ⟨Z v,w,rep,right ▸ (inv _ w).1⟩
    exact ⟨⟨o,present⟩,A.decode_eq present ▸ w,A.decode_eq present ▸ rep⟩
  exact ⟨⟨A.n,A.partition,A.frames,Z,A.member,dz,good.mono (fun v hv => ⟨(A.decode v).property.1,hv.2⟩)⟩,good.mono (fun _ hv => hv.1)⟩

theorem encode_family {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {b : E} {k : ℕ}
    {F : E → HorizontalPaths Γ x} {u} (fam : SmoothPathFamily Γ x (fun r => (F r).val) b k)
    (h : A.Graph (F b) u) (hk : 1 ≤ k) :
    ContDiffAt ℝ k (A.encode ∘ F) b ∧ ∀ᶠ r in 𝓝 b, F r ∈ A.chart.source := by
  obtain ⟨p,path,rp,codes⟩ := h
  obtain ⟨q,first,last,edge⟩ := path
  have base (i s) : (F b).val (A.partition.atTime i s) ∈ (A.frames i).chart.source := by
    rw [rp i _ (A.partition.atTime_mem i s),A.partition.clock_atTime]
    exact (A.frames i).chart.map_target ((edge i).2.2.2.2.1 _)
  obtain ⟨Z,dz,near⟩ := fam.in_coordinates A.partition A.frames A.member base
  obtain ⟨_,_,_,ez⟩ := near.self_of_nhds.1
  have center : Z b = p := near.self_of_nhds.2.unique_data rp (fun i => (ez i).2.2.2.2.1) (fun i => (edge i).2.2.2.2.1)
  obtain ⟨_,R,_,_,_,_,_,dr,_,_,bw⟩ := sobolev_chain_chart A.frames p (A.split u) x (F b).endpoint
    ⟨q,first,last,edge⟩ codes (chartAt State (F b).endpoint) (chart_mem_maximalAtlas _) (mem_chart_source _ _) k hk
  have localGraph : ∀ᶠ r in 𝓝 b, A.Graph (F r) (A.split.symm (R (Z r))) := by
    filter_upwards [near,dz.continuousAt.tendsto (center.symm ▸ bw)] with r hr inv
    exact ⟨Z r,hr.1,hr.2,A.split.apply_symm_apply _ ▸ (inv _ hr.1).1⟩
  have d := A.split.symm.contDiff.contDiffAt.comp b ((show ContDiffAt ℝ k R (Z b) from center.symm ▸ dr).comp b dz)
  exact ⟨d.congr_of_eventuallyEq (localGraph.mono fun _ hr => A.encode_eq hr),localGraph.mono fun _ hr => ⟨_,hr⟩⟩

theorem transition (B : ControlChart Γ x) {u} (hit : u ∈ (A.chart.symm.trans B.chart).source) :
    ContDiffAt ℝ ∞ (B.encode ∘ A.decode) u ∧ (A.chart.symm.trans B.chart).source ∈ 𝓝 u := by
  obtain ⟨⟨γ,ha⟩,v,hb⟩ := hit
  have each (k : ℕ) := A.decode_family ha (k+1) (by omega)
  have both (k : ℕ) := B.encode_family (each k).1 hb (by omega)
  refine ⟨contDiffAt_infty.mpr (fun k => (both k).1.of_le (by exact_mod_cast Nat.le_succ k)),?_⟩
  exact ((each 0).2.and (both 0).2).mono fun _ h => h

#print axioms ControlChart.transition
end ControlChart
end MinimizingSard.Five
