import OriginalTerminalTriples

noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
namespace MinimizingSard.Five

variable {M : Type*} [TopologicalSpace M] [ChartedSpace State M]

theorem zero_segment {m : ℕ} (e : Frame M m) (x y : M) :
    Segment e 0 x y ↔ x = y ∧ x ∈ e.chart.source := by
  have zero (z : ℝ → State) {b : ℝ} (hb : b ∈ Icc (0:ℝ) 1) :
      (fun s => e.velocity (z s) ((0 : Control m) s)) =ᵐ[volume.restrict (uIoc 0 b)] 0 := by
    rw [uIoc_of_le hb.1]
    have sub : Ioc (0:ℝ) b ⊆ Icc 0 1 := fun t ht => ⟨ht.1.le,ht.2.trans hb.2⟩
    filter_upwards [ae_restrict_of_ae_restrict_of_subset sub
      (Lp.coeFn_zero (Fiber m) 2 (volume.restrict (Icc (0:ℝ) 1)))] with s hs
    change (0 : Control m) s = 0 at hs
    change e.velocity (z s) ((0 : Control m) s) = 0
    rw [hs]; simp [Frame.velocity]
  have prim (z : ℝ → State) {b : ℝ} (hb : b ∈ Icc (0:ℝ) 1) :
      (∫ s in (0:ℝ)..b, e.velocity (z s) ((0 : Control m) s)) = 0 := by
    rw [intervalIntegral.integral_congr_ae_restrict (zero z hb)]
    simp
  constructor
  · rintro ⟨hx,hy,z,_,_,zx,zy,_,ode⟩
    have eq := ode 1 ⟨zero_le_one,le_rfl⟩
    rw [prim z ⟨zero_le_one,le_rfl⟩,add_zero,zx,zy] at eq
    exact ⟨e.chart.injOn hx hy eq.symm,hx⟩
  · rintro ⟨rfl,hx⟩
    let z := fun _ : ℝ => e.chart x
    refine ⟨hx,hx,z,continuousOn_const,fun _ _ => e.chart.map_source hx,rfl,rfl,?_,?_⟩
    · exact (intervalIntegrable_congr_ae (zero z ⟨zero_le_one,le_rfl⟩)).mpr (intervalIntegrable_const)
    · intro t ht
      rw [prim z ht,add_zero]

private def cutAt (a : ℝ) (ha : a ∈ Ioo (0:ℝ) 1) : TimePartition 2 where
  cut := ![0,a,1]
  first := rfl
  last := rfl
  increasing := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact ha.1 | exact ha.2 | exact zero_lt_one | (exfalso; revert hij; decide)

private theorem compress_control (e : Frame M 2) (w : Control 2) (a : ℝ) (ha : a ∈ Ioo (0:ℝ) 1)
    (off : ∀ᵐ t ∂volume.restrict (Ioo a 1), w t = 0)
    (active : ∀ b ∈ Ico (0:ℝ) a, ¬ ∀ᵐ t ∂volume.restrict (Ioo b a), w t = 0) :
    ∃ (J : Control 2 →L[ℝ] Control 2) (v : Control 2), J v = w ∧
      (∀ b ∈ Ico (0:ℝ) 1, ¬ ∀ᵐ s ∂volume.restrict (Ioo b 1), v s = 0) ∧
      ∀ z x y, Segment e (J z) x y ↔ Segment e z x y := by
  let T := cutAt a ha
  obtain ⟨R,rep,rel⟩ := T.segment_iff_joins e
  have du : T.duration 0 = a := sub_zero a
  have dv : T.duration 1 = 1-a := rfl
  have l0 : T.left 0 = 0 := rfl
  have l1 : T.left 1 = a := rfl
  have forward : Measure.QuasiMeasurePreserving (fun s : ℝ => a+(1-a)*s) (volume : Measure ℝ) volume :=
    (measurePreserving_add_left volume a).quasiMeasurePreserving.comp
      (Measure.quasiMeasurePreserving_smul volume (sub_pos.mpr ha.2).ne')
  have rmap := forward.restrict (s := Ioo (0:ℝ) 1) (t := Ioo a 1) (by
    intro s hs
    exact ⟨lt_add_of_pos_right _ (mul_pos (sub_pos.mpr ha.2) hs.1),
      by linarith [mul_lt_mul_of_pos_left hs.2 (sub_pos.mpr ha.2)]⟩)
  have zr : R w 1 = 0 := by
    apply Lp.ext
    have v0 := Lp.coeFn_zero (Fiber 2) 2 (volume.restrict (Icc (0:ℝ) 1))
    have hp := rmap.ae off
    rw [restrict_Ioo_eq_restrict_Icc] at hp
    filter_upwards [rep w 1,hp,v0] with s hs hz h0
    change w (a+(1-a)*s) = 0 at hz
    rw [l1,dv,hz,smul_zero] at hs
    exact hs.trans h0.symm
  let J := R.symm.toContinuousLinearMap.comp (ContinuousLinearMap.single ℝ (fun _ : Fin 2 => Control 2) 0)
  have coord (v : Control 2) : R (J v) = Pi.single 0 v := R.apply_symm_apply _
  refine ⟨J,R w 0,R.injective (by rw [coord]; funext i; fin_cases i <;> simp [zr]),?_,?_⟩
  · intro b hb silent
    apply active (a*b) ⟨mul_nonneg ha.1.le hb.1,mul_lt_of_lt_one_right ha.1 hb.2⟩
    have back : Measure.QuasiMeasurePreserving (fun t : ℝ => t/a) (volume : Measure ℝ) volume := by
      simpa only [div_eq_inv_mul,smul_eq_mul] using Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) (inv_ne_zero ha.1.ne')
    have bm := back.restrict (s := Ioo (a*b) a) (t := Ioo b 1) (by
      intro t ht
      exact ⟨(lt_div_iff₀ ha.1).mpr (mul_comm b a ▸ ht.1),(div_lt_one ha.1).mpr ht.2⟩)
    have sub : Ioo b 1 ⊆ Icc (0:ℝ) 1 := fun t ht => ⟨hb.1.trans ht.1.le,ht.2.le⟩
    filter_upwards [bm.ae silent,bm.ae (ae_restrict_of_ae_restrict_of_subset sub (rep w 0))] with t hzero hrep
    change R w 0 (t/a) = 0 at hzero
    change R w 0 (t/a) = T.duration 0 • w (T.left 0 + T.duration 0*(t/a)) at hrep
    rw [du,l0,zero_add,show a*(t/a) = t by field_simp [ha.1.ne'],hzero] at hrep
    exact (smul_eq_zero.mp hrep.symm).resolve_left ha.1.ne'
  · intro z x y
    rw [rel,coord]
    constructor
    · rintro ⟨q,qx,qy,parts⟩
      have p0 : Segment e z (q 0) (q 1) := by simpa using parts 0
      have p1 : Segment e 0 (q 1) (q (Fin.last 2)) := by simpa using parts 1
      rw [qx,((zero_segment _ _ _).mp p1).1,qy] at p0
      exact p0
    · intro path
      refine ⟨![x,y,y],rfl,rfl,?_⟩
      intro i
      fin_cases i
      · simpa using path
      · simpa using (zero_segment e y y).mpr ⟨rfl,path.2.1⟩

theorem endpoint_representative_smooth [IsManifold 𝓘(ℝ,State) ∞ M] {n : ℕ}
    (e : Fin (n+1) → Frame M 2) (w : Fin (n+1) → Control 2) {x y : M} (path : Joins e w x y)
    (c : OpenPartialHomeomorph M State) (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (hy : y ∈ c.source)
    (G : (Fin (n+1) → Control 2) → State)
    (graph : ∀ᶠ b in 𝓝 w, G b ∈ c.target ∧ ∀ z, Joins e b x z ↔ z = c.symm (G b)) :
    ContDiffAt ℝ 2 G w := by
  obtain ⟨F,_,cf,fg,_⟩ := path_endpoint_and_singularity e w x y path c hc hy 2 (by decide)
  apply cf.congr_of_eventuallyEq
  filter_upwards [graph,fg] with t g f
  have h := (f.2 _).mp ((g.2 _).mpr rfl)
  exact (c.right_inv g.1).symm.trans ((congrArg c h).trans (c.right_inv f.1))

private theorem finite_row_comp {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (F : U → State) (L : V →L[ℝ] U)
    (v : V) (p : State →L[ℝ] ℝ) (cf : ContDiffAt ℝ 2 F (L v))
    [FiniteDimensional ℝ (LinearMap.range (kernelRowAt F (L v) p))] :
    FiniteDimensional ℝ (LinearMap.range (kernelRowAt (F ∘ L) v p)) := by
  let A := F ∘ L
  have dL (x : V) : fderiv ℝ (fun t => L t) x = L := L.hasFDerivAt.fderiv
  have d1 : fderiv ℝ A v = (fderiv ℝ F (L v)).comp L :=
    ((cf.differentiableAt (by decide)).hasFDerivAt.comp v L.hasFDerivAt).fderiv
  have d2 (h l : V) : fderiv ℝ (fderiv ℝ A) v h l = fderiv ℝ (fderiv ℝ F) (L v) (L h) (L l) := by
    have eq := Transport.second_comp (fun t => L t) F v h l L.contDiff.contDiffAt cf
    have const : fderiv ℝ (fderiv ℝ (fun t => L t)) v = 0 := by
      rw [show fderiv ℝ (fun t => L t) = fun _ => L from funext dL]; exact fderiv_const_apply _
    simpa only [A,dL,const,ContinuousLinearMap.zero_apply,map_zero,zero_add] using eq
  let K := LinearMap.ker (fderiv ℝ A v).toLinearMap
  let N := LinearMap.ker (fderiv ℝ F (L v)).toLinearMap
  let incl : K →ₗ[ℝ] N := (L.toLinearMap.comp K.subtype).codRestrict N (fun h => by
    change fderiv ℝ F (L v) (L h.val) = 0
    exact (congrArg (fun T : V →L[ℝ] State => T h.val) d1).symm.trans h.property)
  let H := kernelRowAt F (L v) p
  let Q := H.rangeRestrict.comp incl
  apply finite_range_of_kernel Q
  intro h hh
  apply LinearMap.ext
  intro l
  have ke : Q h = 0 := hh
  have z : p (fderiv ℝ (fderiv ℝ F) (L v) (L h.val) (L l.val)) = 0 :=
    congrArg (fun t : LinearMap.range H => t.val (incl l)) ke
  exact (congrArg p (d2 h.val l.val)).trans z

set_option maxHeartbeats 800000 in
/-- An equivalent last control has motion arbitrarily close to its endpoint. -/
theorem active_last_compression {n : ℕ}
    (e : Fin (n+1) → Frame M 2) (w : Fin (n+1) → Control 2) {x y : M}
    (path : Joins e w x y) (c : OpenPartialHomeomorph M State)
    (G : (Fin (n+1) → Control 2) → State)
    (graph : ∀ᶠ b in 𝓝 w, G b ∈ c.target ∧ ∀ z, Joins e b x z ↔ z = c.symm (G b))
    (moves : w (Fin.last n) ≠ 0) :
    ∃ (v : Fin (n+1) → Control 2) (K : (Fin (n+1) → Control 2) →L[ℝ] (Fin (n+1) → Control 2)),
      K v = w ∧ Joins e v x y ∧
      (∀ᶠ t in 𝓝 v, (G ∘ K) t ∈ c.target ∧ ∀ z, Joins e t x z ↔ z = c.symm ((G ∘ K) t)) ∧
      ¬ IdleTail (v (Fin.last n)) := by
  let j := Fin.last n
  by_cases quiet : IdleTail (w j)
  swap
  · exact ⟨w,ContinuousLinearMap.id ℝ _,rfl,path,graph,quiet⟩
  obtain ⟨a,ha,off,before⟩ := first_idle_time _ quiet
  have pos : 0 < a := by
    by_contra! nonpos
    have zero := le_antisymm nonpos ha.1
    subst a
    apply moves
    apply Lp.ext
    rw [restrict_Ioo_eq_restrict_Icc] at off
    filter_upwards [off,Lp.coeFn_zero (Fiber 2) 2 (volume.restrict (Icc (0:ℝ) 1))] with s hs hz
    exact hs.trans hz.symm
  obtain ⟨J,b,jb,active,rel⟩ := compress_control (e j) (w j) a ⟨pos,ha.2⟩ off before
  let v := Function.update w j b
  let K : (Fin (n+1) → Control 2) →L[ℝ] (Fin (n+1) → Control 2) :=
    ContinuousLinearMap.pi (fun i => if i = j then J.comp (ContinuousLinearMap.proj j) else ContinuousLinearMap.proj i)
  have atJ (t : Fin (n+1) → Control 2) : K t j = J (t j) := by simp [K]
  have atI (t : Fin (n+1) → Control 2) (i) (neq : i ≠ j) : K t i = t i := by simp [K,neq]
  have base : K v = w := by
    funext i
    by_cases hi : i = j
    · subst i; simpa [atJ,v] using jb
    · rw [atI v i hi]; exact Function.update_of_ne hi _ _
  have paths (t : Fin (n+1) → Control 2) (z : M) : Joins e (K t) x z ↔ Joins e t x z := by
    have segments (i : Fin (n+1)) (s r : M) : Segment (e i) (K t i) s r ↔ Segment (e i) (t i) s r := by
      by_cases hi : i = j
      · subst i; rw [atJ]; exact rel _ _ _
      · rw [atI t i hi]
    exact exists_congr fun nodes => and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun i => segments i _ _
  have newPath := (paths v y).mp (base.symm ▸ path)
  have graph' : ∀ᶠ t in 𝓝 v, (G ∘ K) t ∈ c.target ∧ ∀ z, Joins e t x z ↔ z = c.symm ((G ∘ K) t) := by
    filter_upwards [(show Tendsto K (𝓝 v) (𝓝 w) from base ▸ K.continuous.tendsto v) graph] with t ht
    exact ⟨ht.1,fun z => (paths t z).symm.trans (ht.2 z)⟩
  refine ⟨v,K,base,newPath,graph',?_⟩
  rintro ⟨b,hb,off⟩
  exact active b hb (by simpa only [v,Function.update_self,j] using off)

set_option maxHeartbeats 1200000 in
/-- The original covector and the terminal frame are preserved even when
the last chart segment moves and subsequently waits. No assumption on
the speed on any subinterval is needed. -/
theorem whole_terminal_triples_of_last_nonzero [IsManifold 𝓘(ℝ,State) ∞ M] {n : ℕ}
    (e : Fin (n+1) → Frame M 2) (w : Fin (n+1) → Control 2) {x y : M}
    (path : Joins e w x y) (c : OpenPartialHomeomorph M State)
    (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (hy : y ∈ c.source)
    (G : (Fin (n+1) → Control 2) → State)
    (graph : ∀ᶠ b in 𝓝 w, G b ∈ c.target ∧ ∀ z, Joins e b x z ↔ z = c.symm (G b))
    (p : State →L[ℝ] ℝ) (rank : FiniteDimensional ℝ (LinearMap.range (kernelRowAt G w p)))
    (moves : w (Fin.last n) ≠ 0) :
    let f := e (Fin.last n)
    let z := f.chart y
    let l := p.comp (fderiv ℝ (c ∘ f.chart.symm) z)
    ∀ i, l (VectorField.lieBracket ℝ (f.X i) (VectorField.lieBracket ℝ (f.X 0) (f.X 1)) z) = 0 := by
  obtain ⟨v,K,base,newPath,graph',active⟩ := active_last_compression e w path c G graph moves
  have sm : ContDiffAt ℝ 2 G (K v) := by rw [base]; exact endpoint_representative_smooth e w path c hc hy G graph
  have rr : FiniteDimensional ℝ (LinearMap.range (kernelRowAt G (K v) p)) := by rw [base]; exact rank
  have rank' := @finite_row_comp _ _ _ _ _ _ G K v p sm rr
  refine (whole_terminal_triples_or_idle e v newPath c hc hy (G ∘ K) graph' p rank').resolve_right ?_
  rintro ⟨d,hd,hd0,_⟩
  exact active ⟨d,hd,hd0⟩

theorem whole_simple_bracket_of_last_nonzero [IsManifold 𝓘(ℝ,State) ∞ M] {n : ℕ}
    (e : Fin (n+1) → Frame M 2) (w : Fin (n+1) → Control 2) {x y : M}
    (path : Joins e w x y) (c : OpenPartialHomeomorph M State)
    (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (hy : y ∈ c.source)
    (G : (Fin (n+1) → Control 2) → State)
    (graph : ∀ᶠ b in 𝓝 w, G b ∈ c.target ∧ ∀ z, Joins e b x z ↔ z = c.symm (G b))
    (p : State →L[ℝ] ℝ) (ann : ∀ h, p (fderiv ℝ G w h) = 0)
    (moves : w (Fin.last n) ≠ 0) :
    let f := e (Fin.last n)
    let z := f.chart y
    p (fderiv ℝ (c ∘ f.chart.symm) z (VectorField.lieBracket ℝ (f.X 0) (f.X 1) z)) = 0 := by
  obtain ⟨v,K,base,newPath,graph',active⟩ := active_last_compression e w path c G graph moves
  have sm := endpoint_representative_smooth e w path c hc hy G graph
  have d := fderiv_comp v ((base.symm ▸ sm).differentiableAt (by decide)) K.differentiableAt
  have kill (h) : p (fderiv ℝ (G ∘ K) v h) = 0 := by
    rw [d,ContinuousLinearMap.comp_apply,base]
    exact ann _
  exact (whole_active_bracket_or_idle e v newPath c hc hy (G ∘ K) graph' p kill).resolve_right
    (fun ⟨a,ha,t,_⟩ => active ⟨a,ha,t⟩)

#print axioms whole_simple_bracket_of_last_nonzero

#print axioms whole_terminal_triples_of_last_nonzero

private theorem drop_idle {n : ℕ} (e : Fin (n+1) → Frame M 2) (w : Fin (n+1) → Control 2)
    (idle : w (Fin.last n) = 0) (x y : M) :
    Joins e w x y ↔ Joins (fun i : Fin n => e i.castSucc) (fun i => w i.castSucc) x y ∧
      y ∈ (e (Fin.last n)).chart.source := by
  constructor
  · rintro ⟨q,qx,qy,parts⟩
    have last := parts (Fin.last n)
    rw [idle,Fin.succ_last,qy] at last
    obtain ⟨mid,ins⟩ := (zero_segment _ _ _).mp last
    refine ⟨⟨fun i => q i.castSucc,qx,mid,?_⟩,mid ▸ ins⟩
    intro i
    simpa only [Fin.castSucc_succ] using parts i.castSucc
  · rintro ⟨⟨q,qx,qy,parts⟩,hy⟩
    let nodes : Fin (n+2) → M := Fin.snoc q y
    refine ⟨nodes,by simpa [nodes] using qx,by simp [nodes],?_⟩
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [nodes,idle,Fin.succ_last,qy] using (zero_segment (e (Fin.last n)) y y).mpr ⟨rfl,hy⟩
    · simpa [nodes,← Fin.castSucc_succ] using parts j


set_option maxHeartbeats 2400000 in
private theorem prefix_data [IsManifold 𝓘(ℝ,State) ∞ M] {n : ℕ}
    (e : Fin (n+2) → Frame M 2) (w : Fin (n+2) → Control 2) {x y : M} (path : Joins e w x y)
    (idle : w (Fin.last (n+1)) = 0) (c : OpenPartialHomeomorph M State)
    (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (hy : y ∈ c.source)
    (G : (Fin (n+2) → Control 2) → State)
    (graph : ∀ᶠ b in 𝓝 w, G b ∈ c.target ∧ ∀ z, Joins e b x z ↔ z = c.symm (G b))
    (p : State →L[ℝ] ℝ) (ann : ∀ h, p (fderiv ℝ G w h) = 0)
    :
    let f := fun i : Fin (n+1) => e i.castSucc
    let v := fun i : Fin (n+1) => w i.castSucc
    Joins f v x y ∧ ∃ H : (Fin (n+1) → Control 2) → State,
      (∀ᶠ b in 𝓝 v, H b ∈ c.target ∧ ∀ z, Joins f b x z ↔ z = c.symm (H b)) ∧
      (∀ h, p (fderiv ℝ H v h) = 0) ∧
      (FiniteDimensional ℝ (LinearMap.range (kernelRowAt G w p)) →
        FiniteDimensional ℝ (LinearMap.range (kernelRowAt H v p))) := by
  let f := fun i : Fin (n+1) => e i.castSucc
  let v := fun i : Fin (n+1) => w i.castSucc
  obtain ⟨pre,inside⟩ := (drop_idle (M := M) (n := n+1) e w idle x y).mp path
  obtain ⟨H,hw,ch,hg,_⟩ := path_endpoint_and_singularity f v x y pre c hc hy 2 (by decide)
  let I : (Fin (n+1) → Control 2) →L[ℝ] (Fin (n+2) → Control 2) :=
    ContinuousLinearMap.pi (Fin.lastCases 0 (fun i => ContinuousLinearMap.proj i))
  have last (b) : I b (Fin.last (n+1)) = 0 := by simp [I]
  have prev (b) (i : Fin (n+1)) : I b i.castSucc = b i := by simp [I]
  have base : I v = w := by
    funext i
    exact Fin.lastCases ((last v).trans idle.symm) (fun j => prev v j) i
  have eq : c.symm (H v) = y := by rw [hw,c.left_inv hy]
  have within : ∀ᶠ b in 𝓝 v, c.symm (H b) ∈ (e (Fin.last (n+1))).chart.source := by
    have cont := ((c.symm.continuousAt (hw.symm ▸ c.map_source hy)).comp (x := v) ch.continuousAt)
    have here : c.symm (H v) ∈ (e (Fin.last (n+1))).chart.source := eq.symm ▸ inside
    exact cont ((e (Fin.last (n+1))).chart.open_source.mem_nhds here)
  have same : H =ᶠ[𝓝 v] G ∘ I := by
    filter_upwards [hg,within,(show Tendsto I (𝓝 v) (𝓝 w) from base ▸ I.continuous.tendsto v) graph] with b h mem g
    have earlier := (h.2 _).mpr rfl
    have full := (drop_idle e (I b) (last b) x (c.symm (H b))).mpr ⟨by simpa only [prev] using earlier,mem⟩
    have id := (g.2 _).mp full
    exact (c.right_inv h.1).symm.trans ((congrArg c id).trans (c.right_inv g.1))
  have smooth := endpoint_representative_smooth e w path c hc hy G graph
  have d := (same.fderiv_eq (𝕜 := ℝ)).trans (((base.symm ▸ smooth).differentiableAt (by decide)).hasFDerivAt.comp v I.hasFDerivAt).fderiv
  refine ⟨pre,H,hg,?_,?_⟩
  · intro h
    rw [d,ContinuousLinearMap.comp_apply,base]
    exact ann _
  · intro rank
    have sm : ContDiffAt ℝ 2 G (I v) := by rw [base]; exact smooth
    have rr : FiniteDimensional ℝ (LinearMap.range (kernelRowAt G (I v) p)) := by rw [base]; exact rank
    exact same_kernel_rank same.symm p (@finite_row_comp _ _ _ _ _ _ G I v p sm rr)

/-- Vanishing of the complete rank-two bracket flag through length three
in the coordinates of a frame of the path at the endpoint. -/
def AnnihilatesThirdFlag (f : Frame M 2) (c : OpenPartialHomeomorph M State) (p : State →L[ℝ] ℝ) (y : M) : Prop :=
  let z := f.chart y
  let l := p.comp (fderiv ℝ (c ∘ f.chart.symm) z)
  (∀ i, l (f.X i z) = 0) ∧ l (VectorField.lieBracket ℝ (f.X 0) (f.X 1) z) = 0 ∧
    ∀ i, l (VectorField.lieBracket ℝ (f.X i) (VectorField.lieBracket ℝ (f.X 0) (f.X 1)) z) = 0

/-- For distinct original endpoints, a kernel-Hessian row of finite
rank whose covector annihilates the endpoint differential annihilates
the third flag in an original active terminal frame. Trailing zero
controls and arbitrary pauses are allowed. -/
theorem whole_third_flag_at_distinct_endpoint [IsManifold 𝓘(ℝ,State) ∞ M] (x y : M) (distinct : x ≠ y)
    (c : OpenPartialHomeomorph M State) (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (hy : y ∈ c.source)
    (p : State →L[ℝ] ℝ) : ∀ (n : ℕ) (e : Fin (n+1) → Frame M 2) (w : Fin (n+1) → Control 2),
    Joins e w x y → ∀ G : (Fin (n+1) → Control 2) → State,
      (∀ᶠ b in 𝓝 w, G b ∈ c.target ∧ ∀ z, Joins e b x z ↔ z = c.symm (G b)) →
      (∀ h, p (fderiv ℝ G w h) = 0) → FiniteDimensional ℝ (LinearMap.range (kernelRowAt G w p)) →
      ∃ i, w i ≠ 0 ∧ (∀ j, i < j → w j = 0) ∧ y ∈ (e i).chart.source ∧ AnnihilatesThirdFlag (e i) c p y := by
  intro n
  induction n
  all_goals
    intro e w path G graph ann rank
    by_cases idle : w (Fin.last _) = 0
    case neg =>
      have inside : y ∈ (e (Fin.last _)).chart.source := by
        obtain ⟨q,_,qy,parts⟩ := path
        simpa only [Fin.succ_last,qy] using (parts (Fin.last _)).2.1
      have h := whole_terminal_bracket e w path c hc hy G graph p
      exact ⟨Fin.last _,idle,fun j hj => (not_lt_of_ge (Fin.le_last j) hj).elim,inside,h.1 ann,h.2 rank 0 1,
        whole_terminal_triples_of_last_nonzero e w path c hc hy G graph p rank idle⟩
  ·
    obtain ⟨q,qx,qy,parts⟩ := path
    have seg := parts (0 : Fin 1)
    rw [show (0 : Fin 1) = Fin.last 0 from rfl] at seg
    rw [idle,Fin.succ_last,qy] at seg
    exact (distinct (qx.symm.trans ((zero_segment _ _ _).mp seg).1)).elim
  ·
    rename_i n' inductiveHypothesis
    obtain ⟨pre,H,g,a,r⟩ := prefix_data e w path idle c hc hy G graph p ann
    obtain ⟨i,moves,after,ins,flag⟩ := inductiveHypothesis _ _ pre H g a (r rank)
    refine ⟨i.castSucc,moves,?_,ins,flag⟩
    intro j
    exact Fin.lastCases (fun _ => idle) (fun k hk => after k (Fin.castSucc_lt_castSucc_iff.mp hk)) j

#print axioms whole_third_flag_at_distinct_endpoint
def AnnihilatesSecondFlag (f : Frame M 2) (c : OpenPartialHomeomorph M State) (p : State →L[ℝ] ℝ) (y : M) : Prop :=
  let z := f.chart y
  let l := p.comp (fderiv ℝ (c ∘ f.chart.symm) z)
  (∀ i, l (f.X i z) = 0) ∧ l (VectorField.lieBracket ℝ (f.X 0) (f.X 1) z) = 0

/-- All first-order annihilators kill the second bracket layer at the last
active frame of any nonconstant path. -/
theorem whole_second_flag_at_distinct_endpoint [IsManifold 𝓘(ℝ,State) ∞ M] (x y : M) (distinct : x ≠ y)
    (c : OpenPartialHomeomorph M State) (hc : c ∈ maximalAtlas 𝓘(ℝ,State) ∞ M) (hy : y ∈ c.source)
    (p : State →L[ℝ] ℝ) : ∀ (n : ℕ) (e : Fin (n+1) → Frame M 2) (w : Fin (n+1) → Control 2),
    Joins e w x y → ∀ G : (Fin (n+1) → Control 2) → State,
      (∀ᶠ b in 𝓝 w, G b ∈ c.target ∧ ∀ z, Joins e b x z ↔ z = c.symm (G b)) →
      (∀ h, p (fderiv ℝ G w h) = 0) →
      ∃ i, w i ≠ 0 ∧ (∀ j, i < j → w j = 0) ∧ y ∈ (e i).chart.source ∧ AnnihilatesSecondFlag (e i) c p y := by
  intro n
  induction n
  all_goals
    intro e w path G graph ann
    by_cases idle : w (Fin.last _) = 0
    case neg =>
      have inside : y ∈ (e (Fin.last _)).chart.source := by
        obtain ⟨q,_,qy,parts⟩ := path
        simpa only [Fin.succ_last,qy] using (parts (Fin.last _)).2.1
      have h := whole_terminal_bracket e w path c hc hy G graph p
      exact ⟨Fin.last _,idle,fun j hj => (not_lt_of_ge (Fin.le_last j) hj).elim,inside,h.1 ann,
        whole_simple_bracket_of_last_nonzero e w path c hc hy G graph p ann idle⟩
  ·
    obtain ⟨q,qx,qy,parts⟩ := path
    have seg := parts (0 : Fin 1)
    rw [show (0 : Fin 1) = Fin.last 0 from rfl] at seg
    rw [idle,Fin.succ_last,qy] at seg
    exact (distinct (qx.symm.trans ((zero_segment _ _ _).mp seg).1)).elim
  ·
    rename_i n' inductiveHypothesis
    obtain ⟨pre,H,g,a,_⟩ := prefix_data e w path idle c hc hy G graph p ann
    obtain ⟨i,moves,after,ins,flag⟩ := inductiveHypothesis _ _ pre H g a
    refine ⟨i.castSucc,moves,?_,ins,flag⟩
    intro j
    exact Fin.lastCases (fun _ => idle) (fun k hk => after k (Fin.castSucc_lt_castSucc_iff.mp hk)) j

#print axioms whole_second_flag_at_distinct_endpoint

end MinimizingSard.Five
