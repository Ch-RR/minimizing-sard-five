import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! A precise target in the local orthonormal-frame control presentation.
The last declaration is a proposition, not a proof. Relating this
presentation to the intrinsic horizontal Sobolev path space is a separate
obligation. No predicate for singularity or minimality is supplied as data. -/
noncomputable section
open Set MeasureTheory IsManifold
open scoped Topology Manifold ContDiff

namespace MinimizingSard.Five
abbrev State := Fin 5 → ℝ
abbrev Fiber (m : ℕ) := Fin m → ℝ
abbrev Control (m : ℕ) := Lp (Fiber m) 2 (volume.restrict (Icc (0 : ℝ) 1))

def speedSq {m : ℕ} (u : Fiber m) : ℝ := ∑ i, u i ^ 2

inductive BracketWord (m : ℕ) where
  | field : Fin m → BracketWord m
  | bracket : BracketWord m → BracketWord m → BracketWord m

def BracketWord.eval {m : ℕ} (X : Fin m → State → State) :
    BracketWord m → State → State
  | .field i => X i
  | .bracket a b => VectorField.lieBracket ℝ (a.eval X) (b.eval X)

variable (M : Type*) [TopologicalSpace M] [ChartedSpace State M]

structure Frame (m : ℕ) where
  chart : OpenPartialHomeomorph M State
  compatible : chart ∈ maximalAtlas 𝓘(ℝ, State) ∞ M
  X : Fin m → State → State
  smooth : ∀ i, ContDiffOn ℝ ∞ (X i) chart.target
  independent : ∀ z ∈ chart.target, LinearIndependent ℝ (fun i => X i z)
  generating : ∀ z ∈ chart.target,
    Submodule.span ℝ (range (fun w : BracketWord m => w.eval X z)) = ⊤

variable {M} {m : ℕ}

def Frame.velocity (e : Frame M m) (z : State) (u : Fiber m) : State :=
  ∑ i, u i • e.X i z

/-- Local orthonormal frames with identical horizontal velocity and metric
on chart overlaps. Indexing by a set allows arbitrary covers. -/
structure Geometry (M : Type*) [TopologicalSpace M] [ChartedSpace State M] (m : ℕ) where
  frames : Set (Frame M m)
  cover : ∀ x : M, ∃ e ∈ frames, x ∈ e.chart.source
  overlap : ∀ e ∈ frames, ∀ d ∈ frames, ∀ x ∈ e.chart.source ∩ d.chart.source,
    ∃ T : Fiber m ≃ₗ[ℝ] Fiber m, ∀ u,
      speedSq (T u) = speedSq u ∧
      (fderiv ℝ (d.chart ∘ e.chart.symm) (e.chart x)) (e.velocity (e.chart x) u) =
        d.velocity (d.chart x) (T u)

/-- Integral equation on one time-rescaled chart segment. -/
def Segment (e : Frame M m) (u : Control m) (x y : M) : Prop :=
  x ∈ e.chart.source ∧ y ∈ e.chart.source ∧ ∃ z : ℝ → State,
    ContinuousOn z (Icc 0 1) ∧ MapsTo z (Icc 0 1) e.chart.target ∧
    z 0 = e.chart x ∧ z 1 = e.chart y ∧
    IntervalIntegrable (fun t => e.velocity (z t) (u t)) volume 0 1 ∧
    ∀ t ∈ Icc (0 : ℝ) 1, z t = z 0 + ∫ s in (0 : ℝ)..t, e.velocity (z s) (u s)

def Joins {n : ℕ} (e : Fin n → Frame M m) (u : Fin n → Control m) (x y : M) : Prop :=
  ∃ nodes : Fin (n+1) → M, nodes 0 = x ∧ nodes (Fin.last n) = y ∧
    ∀ i, Segment (e i) (u i) (nodes i.castSucc) (nodes i.succ)

def length {n : ℕ} (u : Fin n → Control m) : ℝ :=
  ∑ i, ∫ t in (0 : ℝ)..1, Real.sqrt (speedSq ((u i) t))

/-- The local endpoint graph is determined by the segment ODE and all
controls in a neighborhood, including variations on every segment. -/
def SingularIn {n : ℕ} (e : Fin n → Frame M m) (u : Fin n → Control m) (x y : M)
    (chart : OpenPartialHomeomorph M State) : Prop :=
  ∃ (endInChart : (Fin n → Control m) → State)
    (D : (Fin n → Control m) →L[ℝ] State),
    endInChart u = chart y ∧
    (∀ᶠ v in 𝓝 u, endInChart v ∈ chart.target ∧
      ∀ z, Joins e v x z ↔ z = chart.symm (endInChart v)) ∧
    HasFDerivAt endInChart D u ∧ ¬ Function.Surjective D

def Singular {n : ℕ} (e : Fin n → Frame M m) (u : Fin n → Control m) (x y : M) : Prop :=
  ∃ chart : OpenPartialHomeomorph M State,
    chart ∈ maximalAtlas 𝓘(ℝ, State) ∞ M ∧ y ∈ chart.source ∧ SingularIn e u x y chart

/-- An endpoint singular in one smooth target chart is singular in
every smooth target chart containing it, for the same control family. -/
theorem singular_iff_in_chart [IsManifold 𝓘(ℝ, State) ∞ M] {n : ℕ}
    (e : Fin n → Frame M m) (u : Fin n → Control m) (x y : M)
    (c : OpenPartialHomeomorph M State) (hc : c ∈ maximalAtlas 𝓘(ℝ, State) ∞ M)
    (hy : y ∈ c.source) : Singular e u x y ↔ SingularIn e u x y c := by
  refine ⟨?_,fun h => ⟨c,hc,hy,h⟩⟩
  rintro ⟨b,hb,hby,F,D,hF,graph,df,defect⟩
  let P := c ∘ b.symm
  have inv : b.symm (F u) = y := by rw [hF,b.left_inv hby]
  have target : F u ∈ b.target := hF ▸ b.map_source hby
  have inC : b.symm (F u) ∈ c.source := inv.symm ▸ hy
  have hsrc : F u ∈ (b.symm.trans c).source := ⟨target,inC⟩
  have smooth : ContDiffOn ℝ ∞ P (b.symm.trans c).source := by
    have h := (IsManifold.compatible_of_mem_maximalAtlas hb hc).1
    change ContDiffOn ℝ ∞ P ((b.symm.trans c).source ∩ range (𝓘(ℝ, State))) at h
    simpa using h
  have trans : DifferentiableAt ℝ P (F u) :=
    ((smooth _ hsrc).contDiffAt ((b.symm.trans c).open_source.mem_nhds hsrc)).differentiableAt
      (by simp)
  let A := fderiv ℝ P (F u)
  refine ⟨P ∘ F, A.comp D, ?_, ?_, trans.hasFDerivAt.comp u df, ?_⟩
  · exact congrArg c inv
  · have lift : ContinuousAt (b.symm ∘ F) u :=
      (b.symm.continuousAt target).comp df.continuousAt
    have nearby : ∀ᶠ v in 𝓝 u, b.symm (F v) ∈ c.source :=
      lift (c.open_source.mem_nhds inC)
    filter_upwards [graph,nearby] with v hv hnear
    refine ⟨c.map_source hnear, ?_⟩
    intro z
    change Joins e v x z ↔ z = c.symm (c (b.symm (F v)))
    rw [c.left_inv hnear]
    exact hv.2 z
  · intro onto
    have ontoA : Function.Surjective A := fun z =>
      let ⟨v,hv⟩ := onto z
      ⟨D v,hv⟩
    have inj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := A.toLinearMap) rfl).mpr ontoA
    apply defect
    intro z
    obtain ⟨v,hv⟩ := onto (A z)
    exact ⟨v,inj hv⟩

#print axioms singular_iff_in_chart

def singularMinEndpoints (G : Geometry M m) (x : M) : Set M :=
  {y | ∃ (n : ℕ) (e : Fin (n+1) → Frame M m) (u : Fin (n+1) → Control m),
    (∀ i, e i ∈ G.frames) ∧ Joins e u x y ∧ Singular e u x y ∧
    ∀ (k : ℕ) (d : Fin (k+1) → Frame M m) (v : Fin (k+1) → Control m),
      (∀ i, d i ∈ G.frames) → Joins d v x y → length u ≤ length v}

/-- Five-dimensional fixed-source conclusion, locally expressed using
Lebesgue outer measure in every smooth chart. -/
def Statement (M : Type*) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ConnectedSpace M] [ChartedSpace State M] [IsManifold 𝓘(ℝ, State) ∞ M] : Prop :=
  ∀ m : ℕ, 0 < m → m < 5 → ∀ (G : Geometry M m) (x : M)
    (chart : OpenPartialHomeomorph M State), chart ∈ maximalAtlas 𝓘(ℝ, State) ∞ M →
    volume (chart '' (chart.source ∩ singularMinEndpoints G x)) = 0

end MinimizingSard.Five

namespace MinimizingSard.Five

private theorem word_rank_one (X : Fin 1 → State → State) (w : BracketWord 1) :
    w.eval X = X 0 ∨ w.eval X = 0 := by
  induction w with
  | field i =>
    left
    rw [Subsingleton.elim i 0]
    rfl
  | bracket a b ha hb =>
    right
    change VectorField.lieBracket ℝ (a.eval X) (b.eval X) = 0
    rcases ha with ha | ha <;> rcases hb with hb | hb <;>
      simp [ha, hb, VectorField.lieBracket_zero_left, VectorField.lieBracket_zero_right]

/-- In the actual frame presentation, one horizontal direction cannot
bracket-generate a five-dimensional tangent space. -/
theorem rank_one_impossible {M : Type*} [TopologicalSpace M] [ChartedSpace State M]
    (G : Geometry M 1) (x : M) : False := by
  obtain ⟨e,_,hx⟩ := G.cover x
  let z := e.chart x
  have hz : z ∈ e.chart.target := e.chart.map_source hx
  let S := Submodule.span ℝ ({e.X 0 z} : Set State)
  have incl : Submodule.span ℝ (range (fun w : BracketWord 1 => w.eval e.X z)) ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w,rfl⟩
    change w.eval e.X z ∈ S
    rcases word_rank_one e.X w with h | h
    · rw [h]
      exact Submodule.mem_span_singleton_self _
    · rw [h]
      exact S.zero_mem
  rw [e.generating z hz] at incl
  have dimle := Submodule.finrank_mono incl
  have vne := (e.independent z hz).ne_zero (0 : Fin 1)
  have small : Module.finrank ℝ S = 1 := finrank_span_singleton vne
  rw [small, finrank_top, Module.finrank_fin_fun] at dimle
  omega

def ConclusionAtRank (M : Type*) [TopologicalSpace M] [ChartedSpace State M] (m : ℕ) : Prop :=
  ∀ (G : Geometry M m) (x : M) (chart : OpenPartialHomeomorph M State),
    chart ∈ maximalAtlas 𝓘(ℝ, State) ∞ M →
    volume (chart '' (chart.source ∩ singularMinEndpoints G x)) = 0

/-- Exhaustive rank split, with exactly the same endpoint set as the target. -/
theorem statement_iff_ranks_two_three_four (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ConnectedSpace M] [ChartedSpace State M]
    [IsManifold 𝓘(ℝ, State) ∞ M] :
    Statement M ↔ ConclusionAtRank M 2 ∧ ConclusionAtRank M 3 ∧ ConclusionAtRank M 4 := by
  constructor
  · intro h
    exact ⟨h 2 (by decide) (by decide), h 3 (by decide) (by decide),
      h 4 (by decide) (by decide)⟩
  · rintro ⟨h2,h3,h4⟩ m hm h5
    have cases : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · exact fun G x => (rank_one_impossible G x).elim
    · exact h2
    · exact h3
    · exact h4

#print axioms rank_one_impossible
#print axioms statement_iff_ranks_two_three_four
end MinimizingSard.Five
