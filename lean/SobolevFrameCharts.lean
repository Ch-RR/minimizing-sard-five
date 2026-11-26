import SobolevPaths

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace MinimizingSard.Five
open Volterra

/-- Superposition of a field defined on an open domain has a smooth
extension in a neighborhood of any continuous path contained in the domain. -/
theorem field_on_path_germ {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (O : Set E) (op : IsOpen O)
    (X : E → V) (k : ℕ) (cx : ContDiffOn ℝ k X O) (w : C(Time,E)) (hw : ∀ t, w t ∈ O) :
    ∃ N : C(Time,E) → C(Time,V), ContDiff ℝ k N ∧ ∀ᶠ z in 𝓝 w, ∀ t, z t ∈ O ∧ N z t = X (z t) := by
  obtain ⟨Y,U,cy,ou,wU,sub,agree⟩ := compact_smooth_extension O (range w) op
    (isCompact_range w.continuous) (range_nonempty _) (range_subset_iff.mpr hw) X cx
  have near : {z : C(Time,E) | MapsTo z univ U} ∈ 𝓝 w :=
    (ContinuousMap.isOpen_setOf_mapsTo isCompact_univ ou).mem_nhds (fun t _ => wU (mem_range_self t))
  refine ⟨pathField Y cy.continuous,pathField_smooth Y cy,?_⟩
  filter_upwards [near] with z hz
  exact fun t => ⟨sub (hz (mem_univ t)),agree (hz (mem_univ t))⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] {m : ℕ}

private theorem vel_from_solution (e : Frame M m) {a : State} {u : Control m} {w : C(Time,State)}
    (sol : e.Solves u a w) (A : C(Time,Fiber m →L[ℝ] State)) (eq : ∀ t, A t = e.coefficient (w t)) :
    ambientPath (a,multiplyVelocity (Fiber m) State A u) = w := by
  have h := e.solve_primitive sol
  have ae := multiplyVelocity_ae A u
  simp only [eq] at ae
  have prim := h.replace_ae ae.symm
  ext t : 1
  exact ((ambient_primitive _).2 t).trans (prim.2 t).symm

private theorem recovered_control (e : Frame M m) {p : State × Control 5} {u : Control m}
    (sol : e.Solves u p.1 (ambientPath p)) (R : C(Time,State →L[ℝ] Fiber m))
    (eq : ∀ t, R t = e.recover (ambientPath p t)) :
    multiplyVelocity State (Fiber m) R p.2 = u := by
  let A : C(Time,Fiber m →L[ℝ] State) := ⟨fun t => e.coefficient (ambientPath p t),
    e.coefficient_smooth.continuousOn.comp_continuous (ambientPath p).continuous sol.1⟩
  have same := vel_from_solution e sol A (fun _ => rfl)
  have prim := ambient_primitive (p.1,multiplyVelocity (Fiber m) State A u)
  change TimePrimitive (ambientPath (p.1,multiplyVelocity (Fiber m) State A u)) p.1 _ at prim
  rw [same] at prim
  have ident := prim.velocity_unique (ambient_primitive p)
  change multiplyVelocity (Fiber m) State A u = p.2 at ident
  apply Lp.ext
  filter_upwards [multiplyVelocity_ae R p.2,multiplyVelocity_ae A u] with r hr hs
  change multiplyVelocity (Fiber m) State A u r = A (clamp r) (u r) at hs
  rw [ident] at hs
  rw [hr,hs,eq]; exact e.recover_coefficient (sol.1 (clamp r)) _

set_option maxHeartbeats 900000 in
/-- Two-sided parametrization of the horizontal subset in ambient W¹,²
coordinates. The inverse extends smoothly to nearby ambient velocities.
The forward map varies both the starting point and every L² control. -/
theorem sobolev_frame_chart (e : Frame M m) (p : State × Control 5) (hp : e.HorizontalSobolev p)
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ (u : Control m) (F : State × Control m → State × Control 5)
      (R : State × Control 5 → State × Control m),
      e.Solves u p.1 (ambientPath p) ∧ F (p.1,u) = p ∧ R p = (p.1,u) ∧
      ContDiffAt ℝ k F (p.1,u) ∧ ContDiffAt ℝ k R p ∧
      (∀ᶠ v in 𝓝 (p.1,u), (F v).1 = v.1 ∧ e.Solves v.2 v.1 (ambientPath (F v)) ∧
        e.HorizontalSobolev (F v) ∧ R (F v) = v) ∧
      ∀ᶠ z in 𝓝 p, e.HorizontalSobolev z → (R z).1 = z.1 ∧
        e.Solves (R z).2 z.1 (ambientPath z) ∧ F (R z) = z := by
  obtain ⟨u,sol,_⟩ := (horizontal_iff_unique_control e p).mp hp
  let w := ambientPath p
  let b := (p.1,u)
  obtain ⟨S,s0,cs,solutions⟩ := frame_path_family e u p.1 w sol k hk
  obtain ⟨A,ca,fields⟩ := field_on_path_germ e.chart.target e.chart.open_target e.coefficient k
    (e.coefficient_smooth.of_le (by exact_mod_cast (le_top : (k:ℕ∞) ≤ ⊤))) w hp.1
  obtain ⟨B,cb,duals⟩ := field_on_path_germ e.chart.target e.chart.open_target e.recover k
    (e.recover_smooth.of_le (by exact_mod_cast (le_top : (k:ℕ∞) ≤ ⊤))) w hp.1
  let F (v : State × Control m) := (v.1,multiplyVelocity (Fiber m) State (A (S v)) v.2)
  let R (z : State × Control 5) := (z.1,multiplyVelocity State (Fiber m) (B (ambientPath z)) z.2)
  have cf : ContDiffAt ℝ k F b := contDiffAt_fst.prodMk
    (multiplyVelocity_smooth (ca.contDiffAt.comp b cs) contDiffAt_snd)
  have cr : ContDiffAt ℝ k R p := contDiffAt_fst.prodMk
    (multiplyVelocity_smooth (cb.contDiffAt.comp p ambientPath.contDiff.contDiffAt) contDiffAt_snd)
  have sLim : Tendsto S (𝓝 b) (𝓝 w) := s0 ▸ cs.continuousAt.tendsto
  have fw : ∀ᶠ v in 𝓝 b, ambientPath (F v) = S v ∧ e.Solves v.2 v.1 (ambientPath (F v)) := by
    filter_upwards [solutions,sLim fields] with v hs hA
    have eq := vel_from_solution e hs.1 _ (fun t => (hA t).2)
    exact ⟨eq,eq.symm ▸ hs.1⟩
  have z0 : ambientPath (F b) = w := fw.self_of_nhds.1.trans s0
  have eq0 : F b = p := by
    refine Prod.ext (show (F b).1 = p.1 from rfl) ?_
    have h := ambient_primitive (F b)
    rw [z0] at h
    exact h.velocity_unique (ambient_primitive p)
  have r0 : R p = b := Prod.ext rfl (recovered_control e sol _ (fun t => (duals.self_of_nhds t).2))
  have Flim : Tendsto F (𝓝 b) (𝓝 p) := eq0 ▸ cf.continuousAt.tendsto
  have Rlim : Tendsto R (𝓝 p) (𝓝 b) := r0 ▸ cr.continuousAt.tendsto
  have wlim : Tendsto ambientPath (𝓝 p) (𝓝 w) := ambientPath.continuous.tendsto p
  refine ⟨u,F,R,sol,eq0,r0,cf,cr,?_,?_⟩
  · filter_upwards [fw,(wlim.comp Flim) duals] with v h du
    have eq : R (F v) = v := Prod.ext rfl (recovered_control e h.2 _ (fun t => (du t).2))
    refine ⟨rfl,h.2,?_,eq⟩
    apply (horizontal_iff_unique_control e (F v)).mpr
    exact ⟨v.2,h.2,fun z hz => (recovered_control e hz _ (fun t => (du t).2)).symm.trans
      (recovered_control e h.2 _ (fun t => (du t).2))⟩
  · filter_upwards [wlim duals,Rlim fw] with z du near
    intro hz
    obtain ⟨v,vs,_⟩ := (horizontal_iff_unique_control e z).mp hz
    have eq : (R z).2 = v := recovered_control e vs _ (fun t => (du t).2)
    have ss : e.Solves (R z).2 z.1 (ambientPath z) := eq.symm ▸ vs
    have same := e.solves_unique (R z).2 z.1 _ _ near.2 ss
    have h := ambient_primitive (F (R z))
    rw [same] at h
    exact ⟨rfl,ss,Prod.ext rfl (h.velocity_unique (ambient_primitive z))⟩

#print axioms field_on_path_germ
#print axioms sobolev_frame_chart
end MinimizingSard.Five
