import BanachPathChanges
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five
open Volterra

abbrev PathModel (m : ℕ) := Lp (EuclideanSpace ℝ (Fin m)) 2 (volume.restrict (Icc (0:ℝ) 1))

def modelControlEquiv (m : ℕ) : PathModel m ≃L[ℝ] Control m := by
  let L := EuclideanSpace.equiv (Fin m) ℝ
  let μ := volume.restrict (Icc (0:ℝ) 1)
  let D := L.toContinuousLinearMap.compLpL 2 μ
  let R := L.symm.toContinuousLinearMap.compLpL 2 μ
  have left (u : PathModel m) : R (D u) = u := by
    apply Lp.ext
    filter_upwards [L.symm.toContinuousLinearMap.coeFn_compLpL (D u),L.toContinuousLinearMap.coeFn_compLpL u] with s hr hd
    change R (D u) s = L.symm (D u s) at hr
    exact hr.trans ((congrArg L.symm hd).trans (L.symm_apply_apply _))
  have right (u : Control m) : D (R u) = u := by
    apply Lp.ext
    filter_upwards [L.toContinuousLinearMap.coeFn_compLpL (R u),L.symm.toContinuousLinearMap.coeFn_compLpL u] with s hd hr
    change D (R u) s = L (R u s) at hd
    exact hd.trans ((congrArg L hr).trans (L.apply_symm_apply _))
  exact { toLinearEquiv := { D.toLinearMap with invFun := R, left_inv := left, right_inv := right }
          continuous_toFun := D.continuous
          continuous_invFun := R.continuous }

variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M] {m : ℕ} {Γ : Geometry M m} {x : M}
structure ControlChart (Γ : Geometry M m) (x : M) where
  n : ℕ
  partition : TimePartition (n+1)
  frames : Fin (n+1) → Frame M m
  member : ∀ i, frames i ∈ Γ.frames
  fallback : HorizontalPaths Γ x

namespace ControlChart
variable (A : ControlChart Γ x)
def split : PathModel m ≃L[ℝ] (Fin (A.n+1) → Control m) :=
  (modelControlEquiv m).trans (A.partition.coordinates m).choose

def Graph (γ : HorizontalPaths Γ x) (u : PathModel m) :=
  ∃ p, SobolevJoins A.frames p x γ.endpoint ∧ RepresentsPath A.partition A.frames p γ.val ∧ FrameCodes A.frames p (A.split u)

theorem control_unique {γ : HorizontalPaths Γ x} {u v} (hu : A.Graph γ u) (hv : A.Graph γ v) : u = v := by
  obtain ⟨p,hp,rp,cp⟩ := hu
  obtain ⟨z,hz,rz,cz⟩ := hv
  obtain ⟨_,_,_,ep⟩ := hp
  obtain ⟨_,_,_,ez⟩ := hz
  have eq := rp.unique_data rz (fun i => (ep i).2.2.2.2.1) (fun i => (ez i).2.2.2.2.1)
  subst z
  apply A.split.injective
  funext i
  exact ((horizontal_iff_unique_control _ _).mp (ep i).2.2.2.2).unique (cp i) (cz i)

theorem path_unique {γ β : HorizontalPaths Γ x} {u} (h : A.Graph γ u) (j : A.Graph β u) : γ = β := by
  obtain ⟨p,⟨q,first,_,ep⟩,rp,cp⟩ := h
  obtain ⟨z,⟨r,start,_,ez⟩,rz,cz⟩ := j
  have step (i) (same : q i.castSucc = r i.castSucc) : p i = z i := by
    have init := (ep i).2.2.1.trans ((congrArg (A.frames i).chart same).trans (ez i).2.2.1.symm)
    exact ambientPath_injective ((A.frames i).solves_unique _ _ _ _ (cp i) (init.symm ▸ cz i))
  have node (i) : q i = r i := by
    induction i using Fin.induction with
    | zero => exact first.trans start.symm
    | succ i ih =>
      apply (A.frames i).chart.injOn (ep i).2.1 (ez i).2.1
      exact (ep i).2.2.2.1.symm.trans ((congrArg (fun p => ambientPath p (clamp 1)) (step i ih)).trans (ez i).2.2.2.1)
  have same : p = z := funext fun i => step i (node i.castSucc)
  exact Subtype.ext (rp.unique (same.symm ▸ rz))

open Classical in
def encode (γ : HorizontalPaths Γ x) : PathModel m := if h : ∃ u, A.Graph γ u then h.choose else 0
open Classical in
def decode (u : PathModel m) : HorizontalPaths Γ x := if h : ∃ γ, A.Graph γ u then h.choose else A.fallback

theorem encode_eq {γ u} (h : A.Graph γ u) : A.encode γ = u := by
  have ex := Exists.intro u h
  exact (show A.encode γ = ex.choose by simp [encode,ex]).trans (A.control_unique ex.choose_spec h)
theorem decode_eq {γ u} (h : A.Graph γ u) : A.decode u = γ := by
  have ex : ∃ o, A.Graph o u := ⟨γ,h⟩
  exact (show A.decode u = ex.choose by simp [decode,ex]).trans (A.path_unique ex.choose_spec h)

def chart : PartialEquiv (HorizontalPaths Γ x) (PathModel m) where
  toFun := A.encode
  invFun := A.decode
  source := {γ | ∃ u, A.Graph γ u}
  target := {u | ∃ γ, A.Graph γ u}
  map_source' := by rintro γ ⟨u,h⟩; exact ⟨γ,(A.encode_eq h).symm ▸ h⟩
  map_target' := by rintro u ⟨γ,h⟩; exact ⟨u,(A.decode_eq h).symm ▸ h⟩
  left_inv' := by rintro γ ⟨u,h⟩; rw [A.encode_eq h,A.decode_eq h]
  right_inv' := by rintro u ⟨γ,h⟩; rw [A.decode_eq h,A.encode_eq h]

theorem exists_chart (γ : HorizontalPaths Γ x) : ∃ A : ControlChart Γ x, γ ∈ A.chart.source := by
  obtain ⟨_,n,P,e,p,he,hp,rp,_⟩ := γ.property.2
  let A : ControlChart Γ x := ⟨n,P,e,he,γ⟩
  obtain ⟨v,cv⟩ := hp.has_codes
  refine ⟨A,A.split.symm v,p,?_,rp,?_⟩
  · change SobolevJoins e p x (γ.val (clamp 1))
    exact (congrArg (fun a => SobolevJoins e p a (γ.val (clamp 1))) γ.property.1).mp hp
  simpa only [A.split.apply_symm_apply] using cv

#print axioms ControlChart.exists_chart
#print axioms ControlChart.path_unique
end ControlChart
end MinimizingSard.Five
