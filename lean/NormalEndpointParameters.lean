import NormalPieceFamily

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
open Volterra
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] [IsManifold 𝓘(ℝ,State) ∞ M]

/-- All the fine normal variations on a segment reassemble through its very
same bounded linear coordinates, including controls away from the reference. -/
theorem HasNormalLift.family {m : ℕ} (Γ : Geometry M m) (e : Frame M m) (he : e ∈ Γ.frames)
    (w : Control m) (x y : M) (ex : x ∈ e.chart.source) (p q : Covector) (lift : HasNormalLift e w x y p q) :
    NormalFamily Γ e.chart e.chart (Segment e) (pieceLength w) w (e.chart x,p) (e.chart y,q) := by
  obtain ⟨n,R,k,b,Z,k0,kn,b0,bn,cost,joins,arcs⟩ := lift
  let s (j : Fin (n+1)) : Phase := (k j,b j)
  have member (j : Fin (n+1)) : (s j).1 ∈ e.chart.target := by
    induction j using Fin.induction with
    | zero => change k 0 ∈ e.chart.target; rw [k0]; exact e.chart.map_source ex
    | succ i _ =>
      have atEnd := (arcs i).2.2.inside (clamp 1)
      rw [(arcs i).2.1] at atEnd
      exact atEnd
  have cell (i : Fin n) : NormalFamily Γ e.chart e.chart (Segment e) (pieceLength (R w i))
      (R w i) (s i.castSucc) (s i.succ) := by
    have f := (arcs i).2.2.family Γ e he _ _
    rwa [(arcs i).1,(arcs i).2.1] at f
  have fam := NormalFamily.chain Γ (fun _ : Fin n => e) (fun _ => e.chart) _
    (fun i => pieceLength_nonneg (R w i)) (R w) s member cell
  have len := cost w
  rw [length_pieces] at len
  have st : s 0 = (e.chart x,p) := Prod.ext k0 b0
  have fin : s (Fin.last n) = (e.chart y,q) := Prod.ext kn bn
  rw [st,fin,len] at fam
  obtain ⟨F,V,fp,vp,df,dv,near⟩ := fam
  refine ⟨F,R.symm ∘ V,fp,by simp [vp],df,R.symm.differentiableAt.comp _ dv,?_⟩
  filter_upwards [near] with a h
  have rel := joins (R.symm (V a)) (e.chart.symm a.1) (e.chart.symm (F a).1)
  rw [R.apply_symm_apply] at rel
  exact ⟨h.1,h.2.1,rel.mpr h.2.2.1,h.2.2.2⟩

/-- The five real parameters represent an arbitrary covector in the fixed
source chart. -/
def covectorParameters : State ≃L[ℝ] Covector :=
  ((Pi.basisFun ℝ (Fin 5)).toDualEquiv.trans LinearMap.toContinuousLinearMap).toContinuousLinearEquiv

def normalParameterMap {m : ℕ} (Γ : Geometry M m) (x : M) (c : OpenPartialHomeomorph M State)
    (h : Bool) (v : State) : State :=
  if h then c (normalTerminal Γ (packCov (chartAt State x) x (covectorParameters v))).1 else c x

/-- A family with a fixed travel time gives a factorization of the single
unit-time endpoint map in original control coordinates. A separate constant
map covers the source point. -/
theorem normal_family_factor [T2Space M] {m n : ℕ} (Γ : Geometry M m) (x y : M)
    (c : OpenPartialHomeomorph M State) (cy : y ∈ c.source)
    (e : Fin n → Frame M m) (w : Fin n → Control m) (p q : Covector)
    (G : (Fin n → Control m) → State) (gy : G w = c y)
    (graph : ∀ᶠ u in 𝓝 w, G u ∈ c.target ∧ ∀ t, Joins e u x t ↔ t = c.symm (G u))
    (fam : NormalFamily Γ (chartAt State x) c (Joins e) (length w) w ((chartAt State x) x,p) (c y,q)) :
    ∃ (i : Bool) (ξ : State) (V : State → (Fin n → Control m)), V ξ = w ∧ DifferentiableAt ℝ V ξ ∧
      normalParameterMap Γ x c i =ᶠ[𝓝 ξ] G ∘ V := by
  obtain ⟨F,V,fy,vw,df,dv,near⟩ := fam
  let a := chartAt State x
  let s : Phase := (a x,p)
  let L := length w
  have ax : x ∈ a.source := mem_chart_source _ _
  by_cases zero : L = 0
  · have tr := near.self_of_nhds.2.2.2
    rw [show length w = 0 from zero,fy] at tr
    obtain ⟨f,_,start,stop⟩ := tr
    have xy := congrArg Prod.fst (start.symm.trans stop)
    change a.symm (a x) = c.symm (c y) at xy
    rw [a.left_inv ax,c.left_inv cy] at xy
    refine ⟨false,0,fun _ => w,rfl,differentiableAt_const _,.of_forall fun _ => ?_⟩
    exact (congrArg c xy).trans gy.symm
  · have pos : 0 < L := lt_of_le_of_ne (control_length_nonneg w) (Ne.symm zero)
    let ξ := covectorParameters.symm (L • p)
    let I (v : State) : Phase := (a x,L⁻¹ • covectorParameters v)
    have ip : I ξ = s := by simp [I,ξ,s,pos.ne']
    have di : DifferentiableAt ℝ I ξ := (differentiableAt_const (a x)).prodMk
      (covectorParameters.differentiableAt.const_smul L⁻¹)
    have pull : DifferentiableAt ℝ (V ∘ I) ξ := by
      apply DifferentiableAt.comp ξ _ di
      rw [ip]
      exact dv
    have value : (V ∘ I) ξ = w := (congrArg V ip).trans vw
    have source (v : State) : scaleCot L (packPhase a (I v)) = packCov a x (covectorParameters v) := by
      refine Prod.ext (a.left_inv ax) ?_
      change L • ((L⁻¹ • covectorParameters v).comp (chartJac (chartAt State (a.symm (a x))) a (a.symm (a x)))) = _
      rw [a.left_inv ax,ContinuousLinearMap.smul_comp,smul_smul,mul_inv_cancel₀ pos.ne',one_smul]
      rfl
    have tn : Tendsto I (𝓝 ξ) (𝓝 s) := ip ▸ di.continuousAt.tendsto
    have tg : Tendsto (V ∘ I) (𝓝 ξ) (𝓝 w) := value ▸ pull.continuousAt.tendsto
    refine ⟨true,ξ,V ∘ I,value,pull,?_⟩
    filter_upwards [tn near,tg graph] with v h gp
    have scaled := TraceReach.unit_time Γ pos h.2.2.2
    obtain ⟨f,tr,st,fi⟩ := scaled
    rw [source] at st
    have endt := tr.terminal Γ
    rw [st,fi] at endt
    have walk := h.2.2.1
    change Joins e (V (I v)) (a.symm (a x)) (c.symm (F (I v)).1) at walk
    rw [a.left_inv ax] at walk
    have eq := (gp.2 _).mp walk
    change c (normalTerminal Γ (packCov a x (covectorParameters v))).1 = G (V (I v))
    rw [endt]
    exact (congrArg c eq).trans (c.right_inv gp.1)

#print axioms HasNormalLift.family
#print axioms normal_family_factor

/-- In horizontal rank two, every supported fixed-source endpoint admits the
required local factorization through a map on five free covector parameters. -/
theorem parameter_factor_of_segment_solver [T2Space M] {m : ℕ}
    (graphs : ∀ (f : Frame M m) (u : Control m) (a b : M), Segment f u a b → HasSmoothSegmentGraph f 1 (f.chart a,u))
    (solver : SegmentLiftSolver M m) (Γ : Geometry M m) (x y : M)
    (c : OpenPartialHomeomorph M State) (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (cy : y ∈ c.source)
    {n : ℕ} (e : Fin (n+1) → Frame M m) (w : Fin (n+1) → Control m)
    (he : ∀ i, e i ∈ Γ.frames) (path : Joins e w x y)
    (G : (Fin (n+1) → Control m) → State) (gw : G w = c y)
    (graph : ∀ᶠ u in 𝓝 w, G u ∈ c.target ∧ ∀ t, Joins e u x t ↔ t = c.symm (G u))
    (sup : HasCostMultiplier length (fderiv ℝ G w) w) :
    ∃ (i : Bool) (ξ : State) (V : State → (Fin (n+1) → Control m)), V ξ = w ∧ DifferentiableAt ℝ V ξ ∧
      normalParameterMap Γ x c i =ᶠ[𝓝 ξ] G ∘ V := by
  classical
  obtain ⟨q,q0,qn,seg⟩ := path
  let a (j : Fin ((n+1)+1)) := if j = Fin.last (n+1) then c else chartAt State (q j)
  have an : a (Fin.last (n+1)) = c := by simp [a]
  have nz : (0 : Fin ((n+1)+1)) ≠ Fin.last (n+1) := by
    intro eq
    have h := congrArg Fin.val eq
    change 0 = n+1 at h
    omega
  have az : a 0 = chartAt State x := by simp [a,nz,q0]
  have reg (j) : a j ∈ maximalAtlas 𝓘(ℝ,State) ∞ M := by
    unfold a
    split <;> first | exact hc | exact chart_mem_maximalAtlas _
  have mem (j) : q j ∈ (a j).source := by
    unfold a
    split
    · next h => simpa only [h,qn] using cy
    · exact mem_chart_source _ _
  obtain ⟨η,upper⟩ := sup
  have ggraph := graph
  rw [← an,← q0] at ggraph
  obtain ⟨p,_,lifts⟩ := supported_path_lift_of_segments graphs solver e w q seg a mem reg G ggraph η upper
  let z (j : Fin ((n+1)+1)) : Phase := (a j (q j),p j)
  have cells (i : Fin (n+1)) : NormalFamily Γ (a i.castSucc) (a i.succ) (Segment (e i)) (pieceLength (w i))
      (w i) (z i.castSucc) (z i.succ) :=
    NormalFamily.rechart Γ _ _ (e i).chart (reg _) (reg _) (e i).compatible _ _
      (mem _) (seg i).1 (mem _) (seg i).2.1 _ _ _ _ _
      ((lifts i).family Γ (e i) (he i) _ _ _ (seg i).1 _ _)
  have fam := NormalFamily.chain Γ e a _ (fun i => pieceLength_nonneg (w i)) w z
    (fun j => (a j).map_source (mem j)) cells
  change NormalFamily Γ (a 0) (a (Fin.last (n+1))) (Joins e) (∑ i, pieceLength (w i)) w
    (a 0 (q 0),p 0) (a (Fin.last (n+1)) (q (Fin.last (n+1))),p (Fin.last (n+1))) at fam
  rw [az,an,q0,qn,← length_pieces] at fam
  exact normal_family_factor Γ x y c cy e w _ _ G gw graph fam

theorem supported_parameter_factor [T2Space M] (Γ : Geometry M 2) (x y : M)
    (c : OpenPartialHomeomorph M State) (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (cy : y ∈ c.source)
    {n : ℕ} (e : Fin (n+1) → Frame M 2) (w : Fin (n+1) → Control 2)
    (he : ∀ i, e i ∈ Γ.frames) (path : Joins e w x y)
    (G : (Fin (n+1) → Control 2) → State) (gw : G w = c y)
    (graph : ∀ᶠ u in 𝓝 w, G u ∈ c.target ∧ ∀ t, Joins e u x t ↔ t = c.symm (G u))
    (sup : HasCostMultiplier length (fderiv ℝ G w) w) :
    ∃ (i : Bool) (ξ : State) (V : State → (Fin (n+1) → Control 2)), V ξ = w ∧ DifferentiableAt ℝ V ξ ∧
      normalParameterMap Γ x c i =ᶠ[𝓝 ξ] G ∘ V :=
  parameter_factor_of_segment_solver (fun f u a b seg => arbitrary_segment_graph f u a b seg 1 (by decide))
    rank_two_segment_lift_solver Γ x y c hc cy e w he path G gw graph sup

/-- Fixed-source minimizing Sard in the original five-dimensional rank-two
frame-control presentation, measured in every compatible chart. -/
theorem rank_two_minimizing_sard [T2Space M] : ConclusionAtRank M 2 := by
  intro Γ x c hc
  apply rank_two_null_of_normal_parameters Γ x c hc (normalParameterMap Γ x c)
  intro n e w y hy he path _ G gw graph _ sup
  exact supported_parameter_factor Γ x y c hc hy e w he path G gw graph sup

#print axioms supported_parameter_factor
#print axioms rank_two_minimizing_sard

end MinimizingSard.Five
