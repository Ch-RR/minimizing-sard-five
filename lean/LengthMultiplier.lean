import ControlLengthGeometry
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.LinearAlgebra.Isomorphisms

noncomputable section
open Set Filter
open scoped Topology

namespace MinimizingSard.Five

variable {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]

/-- A supporting endpoint covector for a convex cost, with unit cost multiplier. -/
def HasCostMultiplier (J : U → ℝ) (A : U →L[ℝ] State) (w : U) : Prop :=
  ∃ η : State →L[ℝ] ℝ, ∀ v, J w + η (A (v-w)) ≤ J v

theorem costMultiplier_iff_linear_fiber_min (J : U → ℝ) (jc : Continuous J)
    (jv : ConvexOn ℝ univ J) (A : U →L[ℝ] State) (w : U) :
    HasCostMultiplier J A w ↔ ∀ v, A v = A w → J w ≤ J v := by
  constructor
  · rintro ⟨η, h⟩ v hv
    simpa [map_sub,hv] using h v
  intro hmin
  let S : Set (U × ℝ) := {p | J p.1 < p.2}
  let T : Set (U × ℝ) := {p | A p.1 = A w ∧ p.2 = J w}
  have sc : Convex ℝ S := by simpa [S] using jv.convex_strict_epigraph
  have so : IsOpen S := isOpen_lt (jc.comp continuous_fst) continuous_snd
  have tc : Convex ℝ T := by
    intro p hp q hq a b _ _ hab
    obtain ⟨hp₁,hp₂⟩ := hp
    obtain ⟨hq₁,hq₂⟩ := hq
    change A (a • p.1 + b • q.1) = A w ∧ a * p.2 + b * q.2 = J w
    rw [map_add,map_smul,map_smul,hp₁,hq₁,← add_smul,hab,one_smul,hp₂,hq₂,← add_mul,hab,one_mul]
    exact ⟨rfl,rfl⟩
  have disj : Disjoint S T := by
    apply Set.disjoint_left.mpr
    rintro p hs ⟨ha,hr⟩
    exact (not_lt_of_ge (hmin p.1 ha)) (hr ▸ hs : J p.1 < J w)
  obtain ⟨f,k,below,above⟩ := geometric_hahn_banach_open sc so tc disj
  let g := f.comp (ContinuousLinearMap.inl ℝ U ℝ)
  let b := -f (0,1)
  have split (v : U) (r : ℝ) : f (v,r) = g v - r*b := by
    have eq : (v,r) = (v,0) + r • ((0,1) : U × ℝ) := by simp
    rw [eq,map_add,map_smul]
    change g v + r * f (0,1) = _
    dsimp [b]
    ring
  have onGraph (v : U) : g v - J v*b ≤ k := by
    rw [← split]
    have lim : Continuous (fun r : ℝ => f (v,r)) :=
      f.continuous.comp (continuous_const.prodMk continuous_id)
    apply le_of_tendsto (lim.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (J v) ≤ 𝓝 (J v)))
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (below (v,r) hr).le
  have fiber (v : U) (hv : A v = A w) : k ≤ g v - J w*b := by
    rw [← split]
    exact above (v,J w) ⟨hv,rfl⟩
  have eq := le_antisymm (onGraph w) (fiber w rfl)
  have pos : 0 < b := by
    have lt := below (w,J w+1) (show (w,J w+1) ∈ S by change J w < J w+1; linarith)
    rw [split] at lt
    linarith
  have kernel : LinearMap.ker A.toLinearMap ≤ LinearMap.ker g.toLinearMap := by
    intro v hv
    have av : A v = 0 := hv
    have lo := fiber (w+v) (by simp [av])
    have hi := fiber (w-v) (by simp [av])
    rw [map_add] at lo
    rw [map_sub] at hi
    change g v = 0
    linarith
  let Q := (LinearMap.ker A.toLinearMap).liftQ g.toLinearMap kernel
  let R := Q.comp A.toLinearMap.quotKerEquivRange.symm.toLinearMap
  obtain ⟨η, he⟩ := R.exists_extend
  have fac (v : U) : η (A v) = g v := by
    have mem : A.toLinearMap v ∈ LinearMap.range A.toLinearMap := ⟨v,rfl⟩
    have ev := LinearMap.congr_fun he ⟨_,mem⟩
    change η (A v) = Q (A.toLinearMap.quotKerEquivRange.symm ⟨_,mem⟩) at ev
    rw [A.toLinearMap.quotKerEquivRange_symm_apply_image v mem] at ev
    exact ev
  refine ⟨b⁻¹ • η.toContinuousLinearMap, fun v => ?_⟩
  change J w + b⁻¹ * η (A (v-w)) ≤ J v
  rw [fac,map_sub,← div_eq_inv_mul]
  have dif : (g v - g w)/b ≤ J v - J w := (div_le_iff₀ pos).mpr (by
    linarith [onGraph v])
  linarith

/-- This alternative uses the length from the statement even when speeds vanish. -/
theorem no_length_multiplier_iff_shorter {m n : ℕ}
    (A : (Fin n → Control m) →L[ℝ] State) (w : Fin n → Control m) :
    ¬ HasCostMultiplier length A w ↔ ∃ h, A h = 0 ∧ length (w+h) < length w := by
  rw [costMultiplier_iff_linear_fiber_min length continuous_control_length convex_control_length]
  constructor
  · intro h
    push_neg at h
    obtain ⟨v,hv,lt⟩ := h
    exact ⟨v-w,by simp [hv],by simpa [add_sub_cancel_left] using lt⟩
  · rintro ⟨h,hh,lt⟩ hmin
    exact lt.not_ge (hmin (w+h) (by simp [hh]))

#print axioms costMultiplier_iff_linear_fiber_min
#print axioms no_length_multiplier_iff_shorter
end MinimizingSard.Five
