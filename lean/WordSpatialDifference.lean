import FrameGeneratorWord
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace MinimizingSard.Five
open Volterra
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

private def affinePath (p : E × E × E) : C(Time,E × E) :=
  ⟨fun t => (p.1 + (t:ℝ) • p.2.1,p.2.2),(continuous_const.add (continuous_subtype_val.smul continuous_const)).prodMk continuous_const⟩

private def affinePathL : (E × E × E) →L[ℝ] C(Time,E × E) := by
  let L : (E × E × E) →ₗ[ℝ] C(Time,E × E) := {
    toFun := affinePath
    map_add' := fun p r => by
      apply ContinuousMap.ext
      intro t
      refine Prod.ext ?_ rfl
      change (p.1+r.1) + (t:ℝ) • (p.2.1+r.2.1) = (p.1 + (t:ℝ) • p.2.1) + (r.1 + (t:ℝ) • r.2.1)
      rw [smul_add]
      abel
    map_smul' := fun c p => by
      apply ContinuousMap.ext
      intro t
      refine Prod.ext ?_ rfl
      change c • p.1 + (t:ℝ) • c • p.2.1 = c • (p.1 + (t:ℝ) • p.2.1)
      rw [smul_add,smul_comm (t:ℝ) c]
  }
  apply L.mkContinuous 2
  intro p
  refine (ContinuousMap.norm_le _ (by positivity)).mpr ?_
  intro t
  have h₁ := norm_fst_le p
  have h₂ := (norm_fst_le p.2).trans (norm_snd_le p)
  have h₃ := (norm_snd_le p.2).trans (norm_snd_le p)
  have step := mul_le_of_le_one_left (norm_nonneg p.2.1) t.2.2
  change max ‖p.1 + (t:ℝ) • p.2.1‖ ‖p.2.2‖ ≤ _
  apply max_le
  · refine (norm_add_le _ _).trans ?_
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg t.2.1]
    linarith
  · linarith [norm_nonneg p]

/-- Localize a finite-order differentiable germ without changing any of its derivatives there. -/
private theorem extend_finite [FiniteDimensional ℝ E] (n : ℕ) (f : E → State) (x : E)
    (hf : ContDiffAt ℝ n f x) : ∃ g : E → State, ContDiff ℝ n g ∧ g =ᶠ[𝓝 x] f := by
  obtain ⟨U,hU,cu⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨b,supp,_,cb,_,bx⟩ := exists_smooth_tsupport_subset (interior_mem_nhds.mpr hU)
  let a : ContDiffBump (1:ℝ) := ⟨1/4,1/2,by norm_num,by norm_num⟩
  have a0 : a 0 = 0 := a.zero_of_le_dist (by change (1/2:ℝ) ≤ dist 0 1; norm_num)
  let g (y : E) := a (b y) • f y
  have ca : ContDiff ℝ n (fun y => a (b y)) := (a.contDiff.comp cb).of_le (mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  refine ⟨g,contDiff_iff_contDiffAt.mpr ?_,?_⟩
  · intro y
    by_cases hy : y ∈ interior U
    · exact ca.contDiffAt.smul (cu.contDiffAt (mem_interior_iff_mem_nhds.mp hy))
    · apply (contDiffAt_const (c := (0:State))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp (fun h => hy (supp h))] with z h
      simp [g,h,a0]
  · have near := (show Tendsto b (𝓝 x) (𝓝 1) by simpa only [bx] using cb.continuous.tendsto x).eventually a.eventuallyEq_one
    filter_upwards [near] with z hz
    simp [g,show a (b z) = 1 from hz]

/-- Exact finite differences along a scaled vector, with a jointly differentiable coefficient,
including at zero scale. The formula does not divide by the scale. -/
theorem smooth_scaled_difference [FiniteDimensional ℝ E] (n : ℕ) (f : E → State) (x : E)
    (hf : ContDiffAt ℝ (n+1) f x) :
    ∃ J : E × E × E → State, ContDiff ℝ n J ∧
      (∀ᶠ y in 𝓝 x, ∀ v, J (y,0,v) = fderiv ℝ f y v) ∧
      ∀ᶠ p : E × E in 𝓝 (x,0), ∀ (c : ℝ) (v : E), p.2 = c • v →
        f (p.1+p.2) - f p.1 = c • J (p.1,p.2,v) := by
  obtain ⟨g,cg,same⟩ := extend_finite (n+1) f x (by simpa using hf)
  let D (p : E × E) := fderiv ℝ g p.1 p.2
  have cd : ContDiff ℝ n D := ((cg.fderiv_right (m := n) (by simp)).comp contDiff_fst).clm_apply contDiff_snd
  let J := meanPath ∘ PathCalculus.subst (liftField D cd.continuous) ∘ (affinePathL (E := E))
  refine ⟨J,meanPath.contDiff.comp ((PathCalculus.contDiff_subst_of_spatialOrder n _ (field_order n D cd)).comp
    (affinePathL (E := E)).contDiff),?_,?_⟩
  · filter_upwards [same.eventuallyEq_nhds] with y hy
    intro v
    change (∫ t in (0:ℝ)..1, fderiv ℝ g (y+((clamp t : Time):ℝ) • (0:E)) v) = _
    simp [hy.fderiv_eq]
  · have add : Tendsto (fun p : E × E => p.1+p.2) (𝓝 (x,0)) (𝓝 x) := by simpa using (continuous_fst.add continuous_snd).tendsto (x,(0:E))
    filter_upwards [continuous_fst.continuousAt.tendsto same,add same] with p h0 h1
    intro c v hv
    let l (t : ℝ) := p.1+t • p.2
    have dl (t : ℝ) : HasDerivAt l p.2 t := by
      simpa [l] using (hasDerivAt_id t).smul_const p.2 |>.const_add p.1
    have dg := (cg.differentiable (by simp))
    have deriv (t : ℝ) : HasDerivAt (g ∘ l) (fderiv ℝ g (l t) p.2) t := (dg _).hasFDerivAt.comp_hasDerivAt t (dl t)
    have cint : Continuous (fun t => fderiv ℝ g (l t) p.2) :=
      ((cg.continuous_fderiv (by simp)).comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
    have val := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := 1) (fun t _ => deriv t) (cint.intervalIntegrable _ _)
    rw [← h0,← h1,show g (p.1+p.2) - g p.1 = ∫ t in (0:ℝ)..1, fderiv ℝ g (l t) p.2 by simpa [l] using val.symm]
    change _ = c • ∫ t in (0:ℝ)..1, fderiv ℝ g (p.1+((clamp t : Time):ℝ) • p.2) v
    rw [← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    change fderiv ℝ g (l t) p.2 = c • fderiv ℝ g (p.1+((clamp t : Time):ℝ) • p.2) v
    rw [show clamp t = ⟨t,ht⟩ from projIcc_of_mem _ ht]
    exact (congrArg (fderiv ℝ g (l t)) hv).trans ((fderiv ℝ g (l t)).map_smul c v)

#print axioms smooth_scaled_difference

def wordEndpoint (k : ℕ) (X : State × ℝ → State) (p : State × ℝ) : State :=
  p.1 + p.2^k • X p

private theorem spatial_column {X : State × ℝ → State} {z : State}
    (dx : DifferentiableAt ℝ X (z,0)) (v : State) :
    fderiv ℝ X (z,0) (v,0) = fderiv ℝ (fun y : State => X (y,0)) z v := by
  have emb := (ContinuousLinearMap.inl ℝ State ℝ).hasFDerivAt (x := z)
  exact (congrArg (fun L : State →L[ℝ] State => L v) ((dx.hasFDerivAt.comp z emb).fderiv)).symm

/-- Exchanging the order of two unsigned words has an exact smooth coefficient at
order k+l. The coefficient on the entire zero-time germ is their Lie bracket. -/
theorem word_order_difference (k l n : ℕ) (hk : 0 < k) (hl : 0 < l)
    (X Y : State × ℝ → State) (q : State) (cx : ContDiffAt ℝ (n+1) X (q,0)) (cy : ContDiffAt ℝ (n+1) Y (q,0)) :
    ∃ R : State × ℝ → State, ContDiffAt ℝ n R (q,0) ∧
      (∀ᶠ z in 𝓝 q, R (z,0) = VectorField.lieBracket ℝ (fun y => X (y,0)) (fun y => Y (y,0)) z) ∧
      ∀ᶠ p in 𝓝 (q,(0:ℝ)), wordEndpoint l Y (wordEndpoint k X p,p.2) -
        wordEndpoint k X (wordEndpoint l Y p,p.2) = p.2^(k+l) • R p := by
  obtain ⟨Jx,cjx,jx0,ex⟩ := smooth_scaled_difference n X (q,0) cx
  obtain ⟨Jy,cjy,jy0,ey⟩ := smooth_scaled_difference n Y (q,0) cy
  let vx (p : State × ℝ) : State × ℝ := (X p,0)
  let vy (p : State × ℝ) : State × ℝ := (Y p,0)
  let dx (p : State × ℝ) := p.2^k • vx p
  let dy (p : State × ℝ) := p.2^l • vy p
  let Rx (p : State × ℝ) := Jx (p,dy p,vy p)
  let Ry (p : State × ℝ) := Jy (p,dx p,vx p)
  have hle : (n : WithTop ℕ∞) ≤ n+1 := by exact_mod_cast Nat.le_succ n
  have cvx : ContDiffAt ℝ n vx (q,0) := (cx.of_le hle).prodMk contDiffAt_const
  have cvy : ContDiffAt ℝ n vy (q,0) := (cy.of_le hle).prodMk contDiffAt_const
  have cdx : ContDiffAt ℝ n dx (q,0) := (contDiffAt_snd.pow k).smul cvx
  have cdy : ContDiffAt ℝ n dy (q,0) := (contDiffAt_snd.pow l).smul cvy
  have drx : ContDiffAt ℝ n Rx (q,0) := cjx.contDiffAt.comp (q,0) (contDiffAt_id.prodMk (cdy.prodMk cvy))
  have dry : ContDiffAt ℝ n Ry (q,0) := cjy.contDiffAt.comp (q,0) (contDiffAt_id.prodMk (cdx.prodMk cvx))
  refine ⟨fun p => Ry p - Rx p,dry.sub drx,?_,?_⟩
  · have zero : Tendsto (fun z : State => (z,(0:ℝ))) (𝓝 q) (𝓝 (q,0)) := tendsto_id.prodMk_nhds tendsto_const_nhds
    filter_upwards [zero jx0,zero jy0,zero (cx.eventually (by simp)),zero (cy.eventually (by simp))] with z hx hy fx fy
    change ContDiffAt ℝ (n+1) X (z,0) at fx
    change ContDiffAt ℝ (n+1) Y (z,0) at fy
    dsimp only [Ry,Rx,dx,dy]
    rw [zero_pow hk.ne',zero_pow hl.ne',zero_smul,zero_smul,hy,hx]
    exact congrArg₂ Sub.sub (spatial_column (fy.differentiableAt (by simp)) _) (spatial_column (fx.differentiableAt (by simp)) _)
  · have tx : Tendsto (fun p : State × ℝ => (p,dx p)) (𝓝 (q,0)) (𝓝 ((q,0),0)) := by
      simpa [dx,hk.ne'] using tendsto_id.prodMk_nhds cdx.continuousAt.tendsto
    have ty : Tendsto (fun p : State × ℝ => (p,dy p)) (𝓝 (q,0)) (𝓝 ((q,0),0)) := by
      simpa [dy,hl.ne'] using tendsto_id.prodMk_nhds cdy.continuousAt.tendsto
    filter_upwards [tx ey,ty ex] with p hy hx
    have gy := hy (p.2^k) (vx p) rfl
    have gx := hx (p.2^l) (vy p) rfl
    have pairX : p + dx p = (wordEndpoint k X p,p.2) := Prod.ext rfl (by change p.2+p.2^k*(0:ℝ)=p.2; simp)
    have pairY : p + dy p = (wordEndpoint l Y p,p.2) := Prod.ext rfl (by change p.2+p.2^l*(0:ℝ)=p.2; simp)
    change Y (p + dx p) - Y p = p.2^k • Ry p at gy
    change X (p + dy p) - X p = p.2^l • Rx p at gx
    rw [pairX] at gy
    rw [pairY] at gx
    rw [sub_eq_iff_eq_add] at gy gx
    dsimp only [wordEndpoint] at gy gx ⊢
    rw [gy,gx,pow_add,smul_sub,smul_add,smul_add,smul_smul,smul_smul,mul_comm (p.2^l) (p.2^k)]
    abel

/-- If U undoes one ordering, applying U after the opposite ordering gives a commutator
based at the original point. Its leading coefficient is the bracket, with no loss in
the order of vanishing. -/
theorem word_exchange_profile (k l n : ℕ) (hk : 0 < k) (hl : 0 < l)
    (X Y U : State × ℝ → State) (q : State)
    (cx : ContDiffAt ℝ (n+1) X (q,0)) (cy : ContDiffAt ℝ (n+1) Y (q,0))
    (cu : ContDiffAt ℝ (n+1) U (q,0))
    (undo : ∀ᶠ p in 𝓝 (q,(0:ℝ)), U (wordEndpoint k X (wordEndpoint l Y p,p.2),p.2) = p.1) :
    ∃ Z : State × ℝ → State, ContDiffAt ℝ n Z (q,0) ∧
      (∀ᶠ z in 𝓝 q, Z (z,0) = VectorField.lieBracket ℝ (fun y => X (y,0)) (fun y => Y (y,0)) z) ∧
      ∀ᶠ p in 𝓝 (q,(0:ℝ)), U (wordEndpoint l Y (wordEndpoint k X p,p.2),p.2) = wordEndpoint (k+l) Z p := by
  obtain ⟨R,cr,r0,exchange⟩ := word_order_difference k l n hk hl X Y q cx cy
  obtain ⟨J,cj,j0,delta⟩ := smooth_scaled_difference n U (q,0) cu
  let F := wordEndpoint k X
  let G := wordEndpoint l Y
  let A (p : State × ℝ) := (F (G p,p.2),p.2)
  let H (p : State × ℝ) := (G (F p,p.2),p.2)
  let V (p : State × ℝ) : State × ℝ := (R p,0)
  let D (p : State × ℝ) := p.2^(k+l) • V p
  have hle : (n : WithTop ℕ∞) ≤ n+1 := by exact_mod_cast Nat.le_succ n
  have az (z : State) : A (z,0) = (z,0) := by simp [A,F,G,wordEndpoint,hk.ne',hl.ne']
  have gz : (G (q,0), (0:ℝ)) = (q,0) := by simp [G,wordEndpoint,hl.ne']
  have cf : ContDiffAt ℝ n F (q,0) := contDiffAt_fst.add ((contDiffAt_snd.pow _).smul (cx.of_le hle))
  have cg : ContDiffAt ℝ n G (q,0) := contDiffAt_fst.add ((contDiffAt_snd.pow _).smul (cy.of_le hle))
  let T (p : State × ℝ) := (G p,p.2)
  have ct : ContDiffAt ℝ n T (q,0) := cg.prodMk contDiffAt_snd
  have cf' : ContDiffAt ℝ n F (T (q,0)) := by change ContDiffAt ℝ n F (G (q,0),0); rw [gz]; exact cf
  have cft : ContDiffAt ℝ n (F ∘ T) (q,0) := cf'.comp (q,0) ct
  have ca : ContDiffAt ℝ n A (q,0) := cft.prodMk contDiffAt_snd
  have cv : ContDiffAt ℝ n V (q,0) := cr.prodMk contDiffAt_const
  have cd : ContDiffAt ℝ n D (q,0) := (contDiffAt_snd.pow _).smul cv
  have dz (z : State) : D (z,0) = 0 := by simp [D,hk.ne']
  let Z (p : State × ℝ) := J (A p,D p,V p)
  refine ⟨Z,cj.contDiffAt.comp (q,0) (ca.prodMk (cd.prodMk cv)),?_,?_⟩
  · have zero : Tendsto (fun z : State => (z,(0:ℝ))) (𝓝 q) (𝓝 (q,0)) := tendsto_id.prodMk_nhds tendsto_const_nhds
    have uz : (fun z : State => U (z,0)) =ᶠ[𝓝 q] id := by
      filter_upwards [zero undo] with z h
      change U (A (z,0)) = z at h
      simpa only [az] using h
    filter_upwards [r0,zero j0,uz.eventuallyEq_nhds,zero (cu.eventually (by simp))] with z hr hj hu du
    change ContDiffAt ℝ (n+1) U (z,0) at du
    change J (A (z,0),D (z,0),V (z,0)) = _
    rw [az,dz,hj,spatial_column (du.differentiableAt (by simp)),hu.fderiv_eq,fderiv_id]
    exact hr
  · have tend : Tendsto (fun p => (A p,D p)) (𝓝 (q,0)) (𝓝 ((q,0),0)) := by
      simpa only [az,dz] using ca.continuousAt.tendsto.prodMk_nhds cd.continuousAt.tendsto
    filter_upwards [exchange,tend delta,undo] with p h hd back
    have d := hd (p.2^(k+l)) (V p) rfl
    have sum : A p + D p = H p := by
      apply Prod.ext
      · exact (eq_add_of_sub_eq' h).symm
      · change p.2 + p.2^(k+l)*0 = p.2
        simp
    change U (A p+D p)-U (A p) = p.2^(k+l) • Z p at d
    change U (A p) = p.1 at back
    rw [sum,back] at d
    exact eq_add_of_sub_eq' d

#print axioms word_order_difference
#print axioms word_exchange_profile
end MinimizingSard.Five
