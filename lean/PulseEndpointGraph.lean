import PulseHessianLocalization

/-! Joining two genuine L² pulses in the moving-frame integral ODE. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology Interval
open MinimizingSard.Pulse
namespace MinimizingSard.PulseGeometry
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def Columns.velocity (X : Columns E) (t : ℝ) (x : E) (v : Fin 2 → ℝ) : E :=
  v 0 • X.Y 0 t x + v 1 • X.Y 1 t x

def Columns.Path (X : Columns E) (q : E) (v : Controls) (z : ℝ → E) : Prop :=
  ContinuousOn z (Icc 0 1) ∧
  IntervalIntegrable (fun t => X.velocity t (z t) (v t)) volume 0 1 ∧
  ∀ t ∈ Icc (0 : ℝ) 1, z t = q + ∫ s in 0..t, X.velocity s (z s) (v s)

def Columns.Endpoint (X : Columns E) (q : E) (F : Controls → E) : Prop :=
  ∀ᶠ v in 𝓝 (0 : Controls), ∀ z : ℝ → E, X.Path q v z → F v = z 1

private def piece (i : Label) (f : ℝ → E) := (Ioc i.a i.b).indicator f
private def primitive (i : Label) (f : ℝ → E) (t : ℝ) := ∫ s in (0 : ℝ)..t, piece i f s

private theorem primitive_set (i : Label) (f : ℝ → E) {t : ℝ} (ht : 0 ≤ t) :
    primitive i f t = ∫ s in Ioc i.a (min t i.b), f s := by
  rw [primitive, intervalIntegral.integral_of_le ht, piece,
    setIntegral_indicator measurableSet_Ioc, Ioc_inter_Ioc, sup_eq_right.mpr i.left_pos.le]

private theorem primitive_before (i : Label) (f : ℝ → E) {t : ℝ} (ht : 0 ≤ t) (early : t ≤ i.a) :
    primitive i f t = 0 := by
  rw [primitive_set i f ht, Ioc_eq_empty (not_lt.mpr ((min_le_left _ _).trans early))]
  simp

private theorem primitive_during (i : Label) (f : ℝ → E) {t : ℝ} (ht : t ∈ Icc i.a i.b) :
    primitive i f t = ∫ s in i.a..t, f s := by
  rw [primitive_set i f (i.left_pos.le.trans ht.1), min_eq_left ht.2,
    intervalIntegral.integral_of_le ht.1]

private theorem primitive_after (i : Label) (f : ℝ → E) {t : ℝ} (ht : i.b ≤ t) :
    primitive i f t = ∫ s in i.a..i.b, f s := by
  rw [primitive_set i f ((i.left_pos.trans i.nonempty).le.trans ht), min_eq_right ht,
    intervalIntegral.integral_of_le i.nonempty.le]

private def basisSignal (i : Label) (t : ℝ) : Fin 2 → ℝ :=
  (Ioc i.a i.b).indicator (fun _ => Pi.single i.channel 1) t

private theorem coe_basis (i : Label) : ⇑i.control =ᵐ[Causal.timeMeasure] basisSignal i := by
  have e := indicatorConstLp_coeFn (p := 2) (μ := Causal.timeMeasure) (s := Ioo i.a i.b)
      (hs := measurableSet_Ioo) (hμs := measure_Ioo_lt_top.ne) (c := (Pi.single i.channel 1 : Fin 2 → ℝ))
  filter_upwards [e, (ae_restrict_of_ae (Ioo_ae_eq_Ioc (μ := (volume : Measure ℝ))
    (a := i.a) (b := i.b)) : Ioo i.a i.b =ᵐ[Causal.timeMeasure] Ioc i.a i.b)] with t h he
  have iffMem : t ∈ Ioo i.a i.b ↔ t ∈ Ioc i.a i.b := Iff.of_eq he
  simpa only [Label.control,Causal.pulse,basisSignal, Set.indicator, iffMem] using h

private theorem basis_velocity (X : Columns E) (i : Label) (h t : ℝ) (x : E) :
    X.velocity t x (h • basisSignal i t) =
      (Ioc i.a i.b).indicator (fun s => h • X.Y i.channel s x) t := by
  by_cases ht : t ∈ Ioc i.a i.b
  · obtain hc | hc : i.channel = 0 ∨ i.channel = 1 := by omega
    all_goals simp [Columns.velocity,basisSignal,ht,hc]
  · simp [Columns.velocity,basisSignal,ht]

/-- The endpoint of the concatenated local solutions is realized by a
single path for the sum of the two indicator controls in L². -/
theorem two_pulses_join (X : Columns E) (q : E) (i j : Label) (ij : i.b ≤ j.a)
    (h k : ℝ) (z w : ℝ → E)
    (hz : Solves (X.Y i.channel) q i.a i.b h z)
    (hw : Solves (X.Y j.channel) (z i.b) j.a j.b k w) :
    ∃ y, X.Path q (h • i.control + k • j.control) y ∧ y 1 = w j.b := by
  let f (t : ℝ) := h • X.Y i.channel t (z t)
  let g (t : ℝ) := k • X.Y j.channel t (w t)
  have ifin : Integrable (piece i f) := by
    apply (integrable_indicator_iff measurableSet_Ioc).mpr
    have c := (X.continuous i.channel).comp_continuousOn (continuousOn_id.prodMk hz.1)
    exact (continuousOn_const.smul c).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have jfin : Integrable (piece j g) := by
    apply (integrable_indicator_iff measurableSet_Ioc).mpr
    have c := (X.continuous j.channel).comp_continuousOn (continuousOn_id.prodMk hw.1)
    exact (continuousOn_const.smul c).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  let y (t : ℝ) := q + primitive i f t + primitive j g t
  have first (t : ℝ) (ht : t ∈ Icc i.a i.b) : y t = z t := by
    dsimp only [y]
    rw [primitive_during i f ht, primitive_before j g (i.left_pos.le.trans ht.1) (ht.2.trans ij),
      add_zero, hz.2 t ht, ← intervalIntegral.integral_smul]
  have last (t : ℝ) (ht : t ∈ Icc j.a j.b) : y t = w t := by
    dsimp only [y]
    rw [primitive_after i f (ij.trans ht.1),primitive_during j g ht,hw.2 t ht,
      hz.2 i.b (right_mem_Icc.mpr i.nonempty.le)]
    simp only [f,g,intervalIntegral.integral_smul]
  have endpoint : y 1 = w j.b := by
    rw [← last j.b (right_mem_Icc.mpr j.nonempty.le)]
    dsimp only [y]
    rw [primitive_after i f i.right_lt.le, primitive_after j g j.right_lt.le,
      primitive_after i f (ij.trans j.nonempty.le),primitive_after j g le_rfl]
  let ctrl := h • i.control + k • j.control
  let rhs (t : ℝ) := X.velocity t (y t) (ctrl t)
  have eq : rhs =ᵐ[Causal.timeMeasure] fun t => piece i f t + piece j g t := by
    filter_upwards [Lp.coeFn_add (h • i.control) (k • j.control), Lp.coeFn_smul h i.control,
      Lp.coeFn_smul k j.control, coe_basis i,coe_basis j] with t es ei ej bi bj
    change X.velocity t (y t) (ctrl t) = _
    change (h • i.control + k • j.control : Controls) t = _ at es
    simp only [ctrl,es,Pi.add_apply,ei,ej,Pi.smul_apply,bi,bj]
    have add (u v : Fin 2 → ℝ) : X.velocity t (y t) (u+v) =
        X.velocity t (y t) u + X.velocity t (y t) v := by
      simp only [Columns.velocity,Pi.add_apply,add_smul]; abel
    rw [add, basis_velocity,basis_velocity]
    have same (v : Label) (a : ℝ) (w' : ℝ → E) (hh : ∀ t ∈ Icc v.a v.b, y t = w' t) :
        (Ioc v.a v.b).indicator (fun s => a • X.Y v.channel s (y t)) t =
        piece v (fun s => a • X.Y v.channel s (w' s)) t := by
      by_cases ht : t ∈ Ioc v.a v.b
      · simp [piece,ht,hh t ⟨ht.1.le,ht.2⟩]
      · simp [piece,ht]
    exact congrArg₂ (· + ·) (same i h z first) (same j k w last)
  change rhs =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] _ at eq
  rw [restrict_Ioo_eq_restrict_Ioc] at eq
  have int := ifin.add jfin
  refine ⟨y,⟨((continuous_const.add (ifin.continuous_primitive 0)).add
    (jfin.continuous_primitive 0)).continuousOn, ?_, ?_⟩,endpoint⟩
  · apply (int.intervalIntegrable (a := 0) (b := 1)).congr_ae
    rw [uIoc_of_le zero_le_one]
    exact eq.symm
  · intro t ht
    have rel := ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc_right ht.2) eq
    have equal : (∫ s in 0..t, rhs s) = ∫ s in 0..t, piece i f s + piece j g s :=
      intervalIntegral.integral_congr_ae_restrict (by rwa [uIoc_of_le ht.1])
    change y t = q + ∫ s in 0..t, rhs s
    rw [equal,intervalIntegral.integral_add ifin.intervalIntegrable jfin.intervalIntegrable]
    exact add_assoc _ _ _

#print axioms two_pulses_join

variable [FiniteDimensional ℝ E]

/-- The pulse-plane graph is a consequence of the endpoint semantics for
the full moving-frame ODE and the existence of the short pulse solutions. -/
theorem graph_of_integral_endpoint (X : Columns E) (q : E) (F : Controls → E)
    (endpoint : X.Endpoint q F) (Z : Label → E → ℝ → ℝ → E)
    (sol : ∀ i, (X.window i).FamilyNear q (Z i)) : X.Graph F q Z := by
  intro i j ij
  have hz := (sol i).self_of_nhds
  have initial := hz.self_of_nhds.2 i.b (right_mem_Icc.mpr i.nonempty.le)
  simp only [zero_smul,add_zero] at initial
  have hd := amplitude_derivative (X.Y i.channel) (X.continuous _) q i.nonempty.le (Z i q) hz
  have lim : Tendsto (fun h => Z i q h i.b) (𝓝 0) (𝓝 q) := by
    have lim' : Tendsto (fun h => Z i q h i.b) (𝓝 0) (𝓝 (Z i q 0 i.b)) := hd.continuousAt
    rwa [initial] at lim'
  let u (a : ℝ × ℝ) := a.1 • i.control + a.2 • j.control
  have cu : Continuous u := (continuous_fst.smul continuous_const).add (continuous_snd.smul continuous_const)
  have tu : Tendsto u (𝓝 ((0,0) : ℝ × ℝ)) (𝓝 0) := by
    simpa [u] using (cu.continuousAt (x := ((0,0) : ℝ × ℝ))).tendsto
  have pairs := tu.eventually endpoint
  rw [nhds_prod_eq] at pairs
  filter_upwards [hz,lim.eventually (sol j),pairs.curry] with h hzi hzj ends
  filter_upwards [hzj,ends] with k hw he
  obtain ⟨y,hy,final⟩ := two_pulses_join X q i j ij h k _ _ hzi hw
  exact final.symm.trans (he y hy).symm

/-- Terminal bracket exclusion with the actual moving-frame path equation,
the actual control derivative, and the Hessian restricted to its kernel. -/
theorem integral_endpoint_kills_triples (X : Columns E) (q : E) (F : Controls → E)
    (p : E →L[ℝ] ℝ) (endpoint : X.Endpoint q F) (smooth : ContDiffAt ℝ 2 F 0)
    [FiniteDimensional ℝ (LinearMap.range (restrictedHessianRow F p))]
    (Z : Label → E → ℝ → ℝ → E) (sol : ∀ i, (X.window i).FamilyNear q (Z i))
    (B : ℝ → E → E) (u v : ℝ → ℝ) (hend : B 1 = VectorField.lieBracket ℝ (X.Y 0 1) (X.Y 1 1))
    (hB : ContinuousOn (fun t => MixedTime.jet (B t) q) (Icc 0 1))
    (flow : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1),
      HasDerivAt (fun s => MixedTime.jet (X.Y 0 s) q) (-(v t) • MixedTime.jet (B t) q) t ∧
      HasDerivAt (fun s => MixedTime.jet (X.Y 1 s) q) (u t • MixedTime.jet (B t) q) t ∧
      (u t ≠ 0 ∨ v t ≠ 0)) :
    ∀ i, p (VectorField.lieBracket ℝ (X.Y i 1)
      (VectorField.lieBracket ℝ (X.Y 0 1) (X.Y 1 1)) q) = 0 :=
  finite_hessian_kills_triples X F q p smooth Z sol (graph_of_integral_endpoint X q F endpoint Z sol)
    B u v hend hB flow

#print axioms graph_of_integral_endpoint
#print axioms integral_endpoint_kills_triples
end MinimizingSard.PulseGeometry
