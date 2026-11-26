import ArcLengthClock
import NormalPathLift
import EndpointRankFloor

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
open Volterra
variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M]

theorem hamiltonianField_smoothAt {m : ℕ} (e : Frame M m) (z : Phase) (inside : z.1 ∈ e.chart.target) :
    ContDiffAt ℝ ∞ (hamiltonianField e.X) z := by
  choose X sm agree using fun i => smooth_germ_extension e.chart.open_target inside (e.X i) (e.smooth i)
  have fields : ∀ᶠ q in 𝓝 z.1, ∀ i, X i =ᶠ[𝓝 q] e.X i :=
    eventually_all.mpr fun i => (agree i).eventuallyEq_nhds
  apply (hamiltonianField_smooth X sm).contDiffAt.congr_of_eventuallyEq
  filter_upwards [continuousAt_fst.tendsto fields] with p hp
  simp only [hamiltonianField,normalCoefficients,fun i => (hp i).self_of_nhds,fun i => (hp i).fderiv_eq (𝕜 := ℝ)]

theorem pieceLength_clock {m : ℕ} (w : Control m) :
    pieceLength w = arcClock (fun t => Real.sqrt (speedSq (w t))) 1 := by
  have eq := length_pieces (fun _ : Fin 1 => w)
  simpa only [length,Fin.sum_univ_one,arcClock] using eq.symm

/-- A normal piece yields an ordinary Hamilton orbit up to and including
its true length, with the reference control recovered on its original clock. -/
theorem NormalPiece.arc {m : ℕ} (e : Frame M m) (w : Control m) (z : C(Time,Phase)) (piece : NormalPiece e w z) :
    ∃ f : ℝ → Phase, Continuous f ∧ (∀ s, (f s).1 ∈ e.chart.target) ∧
      f 0 = z (clamp 0) ∧ f (pieceLength w) = z (clamp 1) ∧
      (∀ s ∈ Icc 0 (pieceLength w), HasDerivWithinAt f (hamiltonianField e.X (f s)) (Icc 0 (pieceLength w)) s) ∧
      ∀ t ∈ Icc (0:ℝ) 1, f (arcClock (fun s => Real.sqrt (speedSq (w s))) t) = z (clamp t) := by
  let v (t : ℝ) := Real.sqrt (speedSq (w t))
  let B (t : ℝ) := z (clamp t)
  have cb : Continuous B := z.continuous.comp continuous_projIcc
  have cx : ContinuousOn (hamiltonianField e.X) (B '' Icc (0:ℝ) 1) := by
    rintro _ ⟨t,_,rfl⟩
    exact (hamiltonianField_smoothAt e _ (piece.inside _)).continuousAt.continuousWithinAt
  obtain ⟨f,cf,im,rec,ode⟩ := autonomous_arc v (original_speed_integrable w)
    (fun t => Real.sqrt_nonneg _) B cb.continuousOn _ cx piece.primitive
  have inside (s) : (f s).1 ∈ e.chart.target := by
    obtain ⟨t,_,h⟩ := im s
    exact h ▸ piece.inside _
  refine ⟨f,cf,inside,by simpa only [arcClock,intervalIntegral.integral_same] using rec 0 (left_mem_Icc.mpr zero_le_one),
    ?_,?_,rec⟩
  · rw [pieceLength_clock]; exact rec 1 (right_mem_Icc.mpr zero_le_one)
  · rw [pieceLength_clock]; exact ode

/-- Outside one null set, every minimizing singular control from the fixed
source admits normal lifts, with matching covectors in any specified system
of node charts ending at the measuring chart. -/
theorem ae_singular_minimizer_normal_lift [IsManifold 𝓘(ℝ,State) ∞ M]
    (Γ : Geometry M 2) (x : M) (c : OpenPartialHomeomorph M State)
    (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) :
    ∀ᵐ Q : State, Q ∈ c.target → ∀ {n : ℕ} (e : Fin (n+1) → Frame M 2) (w : Fin (n+1) → Control 2)
      (q : Fin ((n+1)+1) → M), q 0 = x → q (Fin.last (n+1)) = c.symm Q →
      (∀ i, e i ∈ Γ.frames) → (∀ i, Segment (e i) (w i) (q i.castSucc) (q i.succ)) →
      (∀ (k : ℕ) (a : Fin (k+1) → Frame M 2) (b : Fin (k+1) → Control 2),
        (∀ i, a i ∈ Γ.frames) → Joins a b x (c.symm Q) → length w ≤ length b) →
      Singular e w x (c.symm Q) →
      ∀ a : Fin ((n+1)+1) → OpenPartialHomeomorph M State, a (Fin.last (n+1)) = c →
        (∀ j, q j ∈ (a j).source) → (∀ j, a j ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) →
        ∃ p : Fin ((n+1)+1) → State →L[ℝ] ℝ, ∀ i, HasNormalLift (e i) (w i) (q i.castSucc) (q i.succ)
          ((p i.castSucc).comp (fderiv ℝ (a i.castSucc ∘ (e i).chart.symm) ((e i).chart (q i.castSucc))))
          ((p i.succ).comp (fderiv ℝ (a i.succ ∘ (e i).chart.symm) ((e i).chart (q i.succ)))) := by
  filter_upwards [ae_singular_minimizer_has_multiplier Γ x c hc] with Q good
  intro hQ n e w q q0 qn he seg min bad a an hq ha
  have path := (show Joins e w x (c.symm Q) from ⟨q,q0,qn,seg⟩)
  obtain ⟨G,_,_,graph,sing⟩ := path_endpoint_and_singularity e w x _ path c hc (c.map_target hQ) 1 (by decide)
  obtain ⟨η,sup⟩ := good hQ e w G he path min graph (sing.mp bad)
  rw [← an,← q0] at graph
  obtain ⟨p,_,lifts⟩ := supported_path_lift e w q seg a hq ha G graph η sup
  exact ⟨p,lifts⟩

#print axioms hamiltonianField_smoothAt
#print axioms NormalPiece.arc
#print axioms ae_singular_minimizer_normal_lift
end MinimizingSard.Five
