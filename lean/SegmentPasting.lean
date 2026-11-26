import ControlPasting

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace MinimizingSard.Five
namespace TimePartition
variable {n m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace State M]

private theorem paste_velocity (P : TimePartition n) (f : Fin n → ℝ → State)
    (hi : ∀ i, IntervalIntegrable (f i) volume 0 1) :
    ∃ G : ℝ → State, Integrable G ∧
      (∀ i t, t ∈ P.block i → G t = (P.duration i)⁻¹ • f i ((t-P.left i)/P.duration i)) ∧
      ∀ i s, s ∈ Icc (0:ℝ) 1 →
        (∫ t in P.left i..P.left i+P.duration i*s, G t) = ∫ t in (0:ℝ)..s, f i t := by
  classical
  let g i := (P.block i).indicator (fun t : ℝ => (P.duration i)⁻¹ • f i ((t-P.left i)/P.duration i))
  let G t := ∑ i, g i t
  have integrable (i) : Integrable (g i) := by
    apply (integrable_indicator_iff measurableSet_Ioc).mpr
    have dil : IntervalIntegrable (fun t => f i (t/P.duration i)) volume 0 (P.duration i) := by
      simpa [div_eq_mul_inv,mul_comm] using (hi i).comp_mul_left (c := (P.duration i)⁻¹)
    have shift : IntervalIntegrable (fun t => f i ((t-P.left i)/P.duration i)) volume
        (P.left i) (P.cut i.succ) := by
      simpa only [zero_add,add_comm (P.duration i),end_eq] using dil.comp_sub_right (P.left i)
    exact (shift.smul (P.duration i)⁻¹).1
  have val (i) (t) (ht : t ∈ P.block i) : G t = (P.duration i)⁻¹ • f i ((t-P.left i)/P.duration i) := by
    change (∑ j, g j t) = _
    rw [Finset.sum_eq_single i]
    · exact indicator_of_mem ht _
    · intro j _ hji
      exact indicator_of_notMem (fun hj => Set.disjoint_left.mp (P.blocks_disjoint hji) hj ht) _
    · simp
  refine ⟨G,integrable_finset_sum _ (fun i _ => integrable i),val,?_⟩
  intro i s hs
  let a := P.left i
  let d := P.duration i
  have hd : 0 < d := P.duration_pos i
  have same : (∫ t in a..a+d*s, G t) = ∫ t in a..a+d*s, d⁻¹ • f i ((t-a)/d) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    rw [uIoc_of_le (le_add_of_nonneg_right (mul_nonneg hd.le hs.1))] at ht
    apply val
    exact ⟨ht.1,ht.2.trans ((add_le_add_left (mul_le_of_le_one_right hd.le hs.2) a).trans_eq (P.end_eq i))⟩
  rw [same,intervalIntegral.integral_smul]
  have tr := intervalIntegral.integral_comp_sub_right (fun t => f i (t/d)) a (a := a) (b := a+d*s)
  rw [tr,sub_self,add_sub_cancel_left,intervalIntegral.inv_smul_integral_comp_div]
  simp [hd.ne']

/-- Reassemble solutions of the original chart integral equations.
The velocity field is recovered a.e. on the whole interval, including
when one changes representatives of any of the L² controls. -/
private theorem join_to_segment (P : TimePartition n) (e : Frame M m) (u : Control m)
    (v : Fin n → Control m) (back : ∀ i, ∀ᵐ t ∂volume.restrict (P.block i),
      u t = (P.duration i)⁻¹ • v i ((t-P.left i)/P.duration i))
    {x y : M} (hx : x ∈ e.chart.source) (hy : y ∈ e.chart.source)
    (join : Joins (fun _ => e) v x y) : Segment e u x y := by
  obtain ⟨nodes,h0,hN,segs⟩ := join
  choose _ _ z cz mz start stop hi eq using segs
  let f i t := e.velocity (z i t) (v i t)
  obtain ⟨G,hG,gv,intEq⟩ := paste_velocity P f hi
  have ints (a b : ℝ) : IntervalIntegrable G volume a b := hG.intervalIntegrable
  let Z (t : ℝ) := e.chart x + ∫ s in (0:ℝ)..t, G s
  have z0 : Z 0 = e.chart x := by simp [Z]
  have node (j : Fin (n+1)) : Z (P.cut j) = e.chart (nodes j) := by
    induction j using Fin.induction with
    | zero => rw [P.first,h0,z0]
    | succ i ih =>
      have it := intEq i 1 (by norm_num)
      rw [mul_one,P.end_eq] at it
      have add := intervalIntegral.integral_add_adjacent_intervals
        (ints (0:ℝ) (P.left i)) (ints (P.left i) (P.cut i.succ))
      have step : Z (P.cut i.succ) = Z (P.left i) + ∫ t in (0:ℝ)..1, f i t := by
        dsimp only [Z]; rw [← add,← add_assoc,it]
      rw [step,show Z (P.left i) = e.chart (nodes i.castSucc) from ih,← start i,← stop i]
      exact (eq i 1 (by norm_num)).symm
  have along (i) (s) (hs : s ∈ Icc (0:ℝ) 1) : Z (P.left i+P.duration i*s) = z i s := by
    have add := intervalIntegral.integral_add_adjacent_intervals (ints (0:ℝ) (P.left i))
      (ints (P.left i) (P.left i+P.duration i*s))
    change e.chart x + _ = _
    rw [← add,← add_assoc,intEq i s hs]
    change Z (P.left i) + _ = _
    rw [show Z (P.left i) = e.chart (nodes i.castSucc) from node i.castSucc,← start i]
    exact (eq i s hs).symm
  have param (i) (t) (ht : t ∈ P.block i) :
      (t-P.left i)/P.duration i ∈ Icc (0:ℝ) 1 := by
    refine ⟨div_nonneg (sub_nonneg.mpr ht.1.le) (P.duration_pos i).le,(div_le_one (P.duration_pos i)).mpr ?_⟩
    have l : t ≤ P.left i+P.duration i := (P.end_eq i).symm ▸ ht.2
    linarith
  have recover (i) (t : ℝ) : P.left i+P.duration i*((t-P.left i)/P.duration i) = t := by
    field_simp [(P.duration_pos i).ne']; ring
  have pos (i) (t) (ht : t ∈ P.block i) : Z t = z i ((t-P.left i)/P.duration i) := by
    have h := along i _ (param i t ht)
    rwa [recover] at h
  have aemap : ∀ᵐ t ∂volume, t ∈ Ioc (0:ℝ) 1 → e.velocity (Z t) (u t) = G t := by
    have each (i) : ∀ᵐ t ∂volume, t ∈ P.block i → e.velocity (Z t) (u t) = G t := by
      apply (ae_restrict_iff' measurableSet_Ioc).mp
      filter_upwards [back i,ae_restrict_mem (measurableSet_Ioc (a := P.left i) (b := P.cut i.succ))] with t hu ht
      rw [hu,pos i t ht,gv i t ht]
      simp [f,Frame.velocity,Finset.smul_sum,smul_smul]
    filter_upwards [ae_all_iff.mpr each] with t hs
    intro ht
    obtain ⟨i,h⟩ := mem_iUnion.mp (P.covers ht)
    exact hs i h
  have eqae (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      (fun s => e.velocity (Z s) (u s)) =ᵐ[volume.restrict (uIoc 0 t)] G := by
    rw [uIoc_of_le ht.1]
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    exact aemap.mono (fun s h hs => h ⟨hs.1,hs.2.trans ht.2⟩)
  refine ⟨hx,hy,Z,(continuous_const.add (hG.continuous_primitive 0)).continuousOn,?_,z0,?_,
    (intervalIntegrable_congr_ae (eqae 1 (by norm_num))).mpr (ints 0 1),?_⟩
  · intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h,z0]; exact e.chart.map_source hx
    · obtain ⟨i,ht'⟩ := mem_iUnion.mp (P.covers ⟨h,ht.2⟩)
      rw [pos i t ht']; exact mz i (param i t ht')
  · simpa only [P.last,hN] using node (Fin.last n)
  · intro t ht
    rw [z0,intervalIntegral.integral_congr_ae_restrict (eqae t ht)]

/-- One and the same control-coordinate isomorphism recovers the exact
endpoint relation for every control and both endpoints. -/
theorem segment_iff_joins (P : TimePartition n) (e : Frame M m) :
    ∃ R : Control m ≃L[ℝ] (Fin n → Control m),
      (∀ u i, ∀ᵐ s ∂volume.restrict (Icc (0:ℝ) 1), R u i s = P.duration i • u (P.left i+P.duration i*s)) ∧
      ∀ u x y, Segment e u x y ↔ Joins (fun _ => e) (R u) x y := by
  obtain ⟨R,rep,back⟩ := P.coordinates m
  refine ⟨R,rep,?_⟩
  intro u x y
  constructor
  · rintro ⟨hx,hy,z,cz,mz,zx,zy,hi,ode⟩
    refine ⟨fun j => e.chart.symm (z (P.cut j)),?_,?_,?_⟩
    · change e.chart.symm (z (P.cut 0)) = x
      rw [P.first,zx,e.chart.left_inv hx]
    · change e.chart.symm (z (P.cut (Fin.last n))) = y
      rw [P.last,zy,e.chart.left_inv hy]
    · intro i
      obtain ⟨v,hv,_,seg⟩ := subsegment e u z cz mz hi ode (P.cut_mem i.castSucc).1 (P.duration_pos i)
        ((P.end_eq i).symm ▸ (P.cut_mem i.succ).2)
      have equal : v = R u i := by
        apply Lp.ext
        filter_upwards [hv,rep u i] with s h1 h2 using h1.trans h2.symm
      change Segment e v (e.chart.symm (z (P.left i))) (e.chart.symm (z (P.left i+P.duration i))) at seg
      simpa only [equal,P.end_eq] using seg
  · intro join
    have hn : 0 < n := by
      by_contra! hz
      have h := P.last
      have eq : Fin.last n = 0 := by apply Fin.ext; change n = 0; omega
      rw [eq,P.first] at h; norm_num at h
    obtain ⟨node,nx,ny,segs⟩ := join
    let i : Fin n := ⟨0,hn⟩
    let j : Fin n := ⟨n-1,by omega⟩
    have first : i.castSucc = 0 := Fin.ext rfl
    have last : j.succ = Fin.last n := by apply Fin.ext; change n-1+1 = n; omega
    have hx := (segs i).1
    have hy := (segs j).2.1
    rw [first,nx] at hx
    rw [last,ny] at hy
    exact join_to_segment P e u (R u) (back u) hx hy ⟨node,nx,ny,segs⟩

#print axioms segment_iff_joins

private theorem one_joins (e : Frame M m) (u : Fin 1 → Control m) (x y : M) :
    Joins (fun _ : Fin 1 => e) u x y ↔ Segment e (u 0) x y := by
  constructor
  · rintro ⟨w,hx,hy,h⟩
    simpa only [show (0:Fin 1).castSucc = 0 from rfl,show (0:Fin 1).succ = Fin.last 1 from rfl,hx,hy] using h 0
  · intro h
    refine ⟨![x,y],rfl,rfl,?_⟩
    intro i; fin_cases i; exact h

private theorem carry_singular {k l : ℕ} {e : Fin k → Frame M m} {d : Fin l → Frame M m}
    (R : (Fin k → Control m) ≃L[ℝ] (Fin l → Control m)) (u : Fin k → Control m)
    (x y : M) (c : OpenPartialHomeomorph M State)
    (graph : ∀ b z, Joins e b x z ↔ Joins d (R b) x z) :
    SingularIn e u x y c → SingularIn d (R u) x y c := by
  rintro ⟨F,D,atU,localGraph,dF,defect⟩
  refine ⟨F ∘ R.symm,D.comp R.symm.toContinuousLinearMap,?_,?_,?_,?_⟩
  · simpa only [Function.comp_apply,R.symm_apply_apply] using atU
  · have push : Tendsto R.symm (𝓝 (R u)) (𝓝 u) := by simpa using R.symm.continuous.tendsto (R u)
    filter_upwards [push localGraph] with b hb
    refine ⟨hb.1,?_⟩
    intro z
    exact ((R.apply_symm_apply b) ▸ (graph (R.symm b) z)).symm.trans (hb.2 z)
  · exact (show HasFDerivAt F D (R.symm (R u)) by simpa using dF).comp _ R.symm.toContinuousLinearMap.hasFDerivAt
  · intro sur
    apply defect
    intro z
    obtain ⟨b,hb⟩ := sur z
    exact ⟨R.symm b,hb⟩

/-- Subdividing a single original chart segment preserves the original
definition of singularity in both directions and in every target chart. -/
theorem singular_under_subdivision (P : TimePartition n) (e : Frame M m) :
    ∃ R : (Fin 1 → Control m) ≃L[ℝ] (Fin n → Control m),
      (∀ u i, ∀ᵐ s ∂volume.restrict (Icc (0:ℝ) 1), R u i s = P.duration i • u 0 (P.left i+P.duration i*s)) ∧
      ∀ u x y c, SingularIn (fun _ : Fin 1 => e) u x y c ↔
        SingularIn (fun _ : Fin n => e) (R u) x y c := by
  obtain ⟨R,rep,eq⟩ := segment_iff_joins P e
  let L := (ContinuousLinearEquiv.funUnique (Fin 1) ℝ (Control m)).trans R
  have graph (b : Fin 1 → Control m) (x y : M) : Joins (fun _ : Fin 1 => e) b x y ↔
      Joins (fun _ : Fin n => e) (L b) x y := (one_joins e b x y).trans (eq (b 0) x y)
  refine ⟨L,fun u i => rep (u 0) i,?_⟩
  intro u x y c
  refine ⟨carry_singular L u x y c (fun b z => graph b x z),?_⟩
  intro h
  have rev (b) (z) : Joins (fun _ : Fin n => e) b x z ↔ Joins (fun _ : Fin 1 => e) (L.symm b) x z := by
    simpa only [L.apply_symm_apply] using (graph (L.symm b) x z).symm
  simpa only [L.symm_apply_apply] using carry_singular L.symm (L u) x y c rev h

#print axioms singular_under_subdivision
end TimePartition
end MinimizingSard.Five
