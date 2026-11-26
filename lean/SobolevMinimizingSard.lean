import SobolevChainCharts

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] [IsManifold 𝓘(ℝ,State) ∞ M] {m n : ℕ}

set_option maxHeartbeats 800000 in
/-- The entire endpoint differential has exactly the singularity detected
by testing all differentiable curves of horizontal ambient Sobolev data.
All common nodes may vary independently of the fixed initial source. -/
theorem sobolev_singular_iff (e : Fin n → Frame M m) (p : Fin n → SobolevData) (u : Fin n → Control m)
    {x y : M} (path : SobolevJoins e p x y) (codes : FrameCodes e p u) :
    SobolevSingular e p x y ↔ Singular e u x y := by
  constructor
  · rintro ⟨c,hc,cy,η,nz,test⟩
    obtain ⟨F,R,G,Fu,_,gu,dF,_,dG,fw,_⟩ := sobolev_chain_chart e p u x y path codes c hc cy 1 le_rfl
    refine ⟨c,hc,cy,G,_,gu,fw.mono (fun _ h => ⟨h.1,h.2.1⟩),(dG.differentiableAt (by decide)).hasFDerivAt,?_⟩
    intro onto
    apply nz
    ext v
    obtain ⟨h,rfl⟩ := onto v
    let I (t : ℝ) := u+t • h
    have i0 : I 0 = u := by simp [I]
    have di : HasDerivAt I h 0 := (hasDerivAt_id 0).smul_const h |>.const_add u |>.congr_deriv (by simp)
    have reg := (dG.differentiableAt (by decide)).hasFDerivAt
    have dg := (i0.symm ▸ reg).comp_hasDerivAt 0 di
    have df := (i0.symm ▸ (dF.differentiableAt (by decide))).comp 0 di.differentiableAt
    have saved := test (F ∘ I) (G ∘ I) ((congrArg F i0).trans Fu) ((congrArg G i0).trans gu) df dg.differentiableAt
      (by filter_upwards [(i0 ▸ di.continuousAt.tendsto) fw] with t h using ⟨h.1,h.2.2.1⟩)
    rw [dg.deriv] at saved
    change η ((fderiv ℝ G u) h) = 0
    simpa only [i0] using saved
  · rintro ⟨c,hc,cy,H,D,_,gh,dh,bad⟩
    obtain ⟨F,R,G,_,rp,gu,_,dR,dG,fw,bw⟩ := sobolev_chain_chart e p u x y path codes c hc cy 1 le_rfl
    have same : H =ᶠ[𝓝 u] G := by
      filter_upwards [gh,fw] with v h g
      exact c.symm.injOn h.1 g.1 ((g.2.1 _).mp ((h.2 _).mpr rfl))
    have defect : ¬ Function.Surjective (fderiv ℝ G u) := by rwa [← same.fderiv_eq,dh.fderiv]
    let W := LinearMap.range (fderiv ℝ G u).toLinearMap
    have out : ∃ z, z ∉ W := by
      by_contra! all
      exact defect (fun z => all z)
    obtain ⟨v,out⟩ := out
    obtain ⟨l,nz,kill⟩ := W.exists_dual_map_eq_bot_of_notMem out inferInstance
    let η := l.toContinuousLinearMap
    have ann (h) : η (fderiv ℝ G u h) = 0 := by
      have v : l (fderiv ℝ G u h) ∈ W.map l := ⟨_,⟨h,rfl⟩,rfl⟩
      rwa [kill] at v
    refine ⟨c,hc,cy,η,fun zero => nz (DFunLike.congr_fun zero v),?_⟩
    intro Z f zp f0 dz df graph
    let C := R ∘ Z
    have C0 : C 0 = u := (congrArg R zp).trans rp
    have dc : DifferentiableAt ℝ C 0 := (zp.symm ▸ (dR.differentiableAt (by decide))).comp 0 dz
    have val : f =ᶠ[𝓝 0] G ∘ C := by
      filter_upwards [graph,(zp ▸ dz.continuousAt.tendsto) bw,(C0 ▸ dc.continuousAt.tendsto) fw] with t chart pull push
      have walk := chart.2.control (pull _ chart.2).1
      exact c.symm.injOn chart.1 push.1 ((push.2.1 _).mp walk)
    have endpointDeriv := (C0.symm ▸ (dG.differentiableAt (by decide)).hasFDerivAt).comp_hasDerivAt 0 dc.hasDerivAt
    rw [(endpointDeriv.congr_of_eventuallyEq val).deriv]
    rw [C0]
    exact ann _

/-- All lengths use the ambient Sobolev velocity and the local horizontal
metric. Both singularity and competition range over Sobolev data. -/
def sobolevMinEndpoints (Γ : Geometry M m) (x : M) : Set M :=
  {y | ∃ (n : ℕ) (e : Fin (n+1) → Frame M m) (p : Fin (n+1) → SobolevData),
    (∀ i, e i ∈ Γ.frames) ∧ SobolevJoins e p x y ∧ SobolevSingular e p x y ∧
      ∀ (k : ℕ) (d : Fin (k+1) → Frame M m) (z : Fin (k+1) → SobolevData),
        (∀ i, d i ∈ Γ.frames) → SobolevJoins d z x y → sobolevLength e p ≤ sobolevLength d z}

theorem sobolev_endpoints_eq (Γ : Geometry M m) (x : M) :
    sobolevMinEndpoints Γ x = singularMinEndpoints Γ x := by
  ext y
  constructor
  · rintro ⟨n,e,p,he,path,sing,minimal⟩
    obtain ⟨u,codes⟩ := path.has_codes
    refine ⟨n,e,u,he,path.control codes,(sobolev_singular_iff e p u path codes).mp sing,?_⟩
    intro k d v hd walk
    obtain ⟨b,raw,hb⟩ := walk.sobolev
    simpa only [← codes.length_eq,← hb.length_eq] using minimal k d b hd raw
  · rintro ⟨n,e,u,he,path,sing,minimal⟩
    obtain ⟨p,raw,codes⟩ := path.sobolev
    refine ⟨n,e,p,he,raw,(sobolev_singular_iff e p u raw codes).mpr sing,?_⟩
    intro k d z hd walk
    obtain ⟨v,hv⟩ := walk.has_codes
    simpa only [codes.length_eq,hv.length_eq] using minimal k d v hd (walk.control hv)

theorem five_dimensional_sobolev_sard [T2Space M] [SecondCountableTopology M] [ConnectedSpace M]
    (m : ℕ) (hm : 0 < m) (h5 : m < 5) (Γ : Geometry M m) (x : M) (c : OpenPartialHomeomorph M State)
    (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) :
    volume (c '' (c.source ∩ sobolevMinEndpoints Γ x)) = 0 := by
  rw [sobolev_endpoints_eq]
  exact five_dimensional_frame_sard m hm h5 Γ x c hc

#print axioms sobolev_singular_iff
#print axioms sobolev_endpoints_eq
#print axioms five_dimensional_sobolev_sard
end MinimizingSard.Five
