module

public import SquaresInCircles.Eight.TableFree.PositiveSplitCalculus

/-!
# The whole positive split lies above the smaller scalar endpoint

Uncompiled source draft of Section 9 of the positive-GA core-E argument.
The curvature estimate is quantitative and holds on the entire interval.
Its scalar endpoints are not asserted to be geometrically feasible.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.PositiveSplitConcavity
open PositiveAngularEnvelope PositivePrimaryBaselines PositiveSplitComparison
open PositiveStressCoefficients PositiveSplitCalculus

private theorem weight_lt {η t : ℝ}
    (hη : η∈Icc (1/4) (7303/20000)) (ht : t∈Icc 0 frameCap) :
    0≤k*PositiveSplitCalculus.f η t ∧ k*PositiveSplitCalculus.f η t<23/25 := by
  obtain ⟨hc,_,hs,_,_⟩ := transport_trig ht
  have hf : 0≤PositiveSplitCalculus.f η t := by unfold PositiveSplitCalculus.f; nlinarith [hη.1]
  have hm : 0≤k*PositiveSplitCalculus.f η t := mul_nonneg (by norm_num [k]) hf
  have hη2 := pow_le_pow_left₀ (show 0≤η by linarith [hη.1]) hη.2 2
  have he := f_energy η t
  have hm2 : (k*PositiveSplitCalculus.f η t)^2<(23/25 : ℝ)^2 := by
    dsimp [k]
    nlinarith [sq_nonneg (df η t)]
  exact ⟨hm,by nlinarith⟩

private theorem ratio_bound {r η t a : ℝ} (hr : 0<r)
    (ha : 0<a) (hm : 0≤k*PositiveSplitCalculus.f η t)
    (hstrict : qCap*(k*PositiveSplitCalculus.f η t)^2<a^2*(r^2+(k*PositiveSplitCalculus.f η t)^2)) :
    Real.sqrt qCap*(k*PositiveSplitCalculus.f η t)/norm r k η t<a := by
  have hN := norm_pos hr k η t
  have hsq := norm_sq hr k η t
  have hR : (Real.sqrt qCap)^2=qCap := Real.sq_sqrt (by norm_num [qCap])
  have hleft : (Real.sqrt qCap*(k*PositiveSplitCalculus.f η t))^2=
      qCap*(k*PositiveSplitCalculus.f η t)^2 := by
    rw [mul_pow,hR]
  apply (div_lt_iff₀ hN).2
  dsimp [radicand] at hsq
  apply lt_of_pow_lt_pow_left₀ 2 (mul_pos ha hN).le
  rw [hleft,show (a*norm r k η t)^2=a^2*(norm r k η t)^2 by ring,hsq]
  exact hstrict

private theorem ratio_one_lt {η t : ℝ}
    (hη : η∈Icc (1/4) (7303/20000)) (ht : t∈Icc 0 frameCap) :
    Real.sqrt qCap*(k*PositiveSplitCalculus.f η t)/norm 1 k η t<29/20 := by
  obtain ⟨hm,hm1⟩ := weight_lt hη ht
  have hm2 := pow_le_pow_left₀ hm hm1.le 2
  apply ratio_bound (by norm_num) (by norm_num) hm
  norm_num [qCap] at *
  nlinarith

private theorem ratio_l_lt {d η t : ℝ} (hd : d∈Icc 0 frameCap)
    (hη : η∈Icc (1/4) (7303/20000)) (ht : t∈Icc 0 frameCap) :
    Real.sqrt qCap*(k*PositiveSplitCalculus.f η t)/norm (lP d) k η t<7/4 := by
  obtain ⟨hm,hm1⟩ := weight_lt hη ht
  have hl := (coefficient_bounds hd).1
  have hl2 : (1/2 : ℝ)^2≤(lP d)^2 := pow_le_pow_left₀ (by norm_num) hl.le 2
  have hm2 := pow_le_pow_left₀ hm hm1.le 2
  apply ratio_bound (by linarith) (by norm_num) hm
  norm_num [qCap] at *
  nlinarith

/-- The two sine coefficient bounds are positive square comparisons of
concave quadratics; both endpoint checks are contained in the same proof. -/
private theorem sine_coefficients {η : ℝ}
    (hη : η∈Icc (1/4) (7303/20000)) :
    Real.sqrt qCap*Real.sqrt (1+η^2)-1-(11/20 : ℝ)*η<907/1000 ∧
    Real.sqrt qCap*Real.sqrt (1+η^2)-1-(1/4 : ℝ)*η<1017/1000 := by
  have hη0 : 0≤η := by linarith [hη.1]
  have hfactor := mul_nonneg (sub_nonneg.mpr hη.1) (sub_nonneg.mpr hη.2)
  have hroot : (Real.sqrt qCap*Real.sqrt (1+η^2))^2=qCap*(1+η^2) := by
    rw [mul_pow,Real.sq_sqrt (by norm_num [qCap]),Real.sq_sqrt (by positivity)]
  have hnonneg := mul_nonneg (Real.sqrt_nonneg qCap) (Real.sqrt_nonneg (1+η^2))
  constructor
  · have hsq : qCap*(1+η^2)<((1907/1000 : ℝ)+(11/20 : ℝ)*η)^2 := by
      norm_num [qCap] at *
      nlinarith
    have := lt_of_pow_lt_pow_left₀ 2 (by positivity) (hroot ▸ hsq)
    linarith
  · have hsq : qCap*(1+η^2)<((2017/1000 : ℝ)+(1/4 : ℝ)*η)^2 := by
      norm_num [qCap] at *
      nlinarith
    have := lt_of_pow_lt_pow_left₀ 2 (by positivity) (hroot ▸ hsq)
    linarith

theorem g_one_second_le {d t : ℝ} (hd : d∈Icc 0 frameCap)
    (ht : t∈Icc 0 frameCap) :
    gSecond (Real.sqrt qCap) 1 k (etaP d) t≤
      k*(-(11/20 : ℝ)*Real.cos t+(907/1000 : ℝ)*Real.sin t) := by
  have hb := coefficient_bounds hd
  have hη : etaP d∈Icc (1/4) (7303/20000) := ⟨hb.2.2.2.2.2.2.1,hb.2.2.2.2.2.2.2.1⟩
  have hc := transport_cos_pos (by rw [abs_of_nonneg ht.1]; exact ht.2)
  have hs := (transport_trig ht).2.2.1
  refine (gSecond_le (a := 29/20) (c := 907/1000) (Real.sqrt_nonneg qCap)
    (by norm_num : (0:ℝ)<1) (by norm_num [k] : (0:ℝ)≤k) (by linarith [hη.1]) hc.le hs
    (ratio_one_lt hη ht).le (by linarith [(sine_coefficients hη).1])).trans_eq ?_
  ring

theorem g_l_second_le {d t : ℝ} (hd : d∈Icc 0 frameCap)
    (ht : t∈Icc 0 frameCap) :
    gSecond (Real.sqrt qCap) (lP d) k (etaP d) t≤
      k*(-(1/4 : ℝ)*Real.cos t+(1017/1000 : ℝ)*Real.sin t) := by
  have hb := coefficient_bounds hd
  have hη : etaP d∈Icc (1/4) (7303/20000) := ⟨hb.2.2.2.2.2.2.1,hb.2.2.2.2.2.2.2.1⟩
  have hc := transport_cos_pos (by rw [abs_of_nonneg ht.1]; exact ht.2)
  have hs := (transport_trig ht).2.2.1
  refine (gSecond_le (a := 7/4) (c := 1017/1000) (Real.sqrt_nonneg qCap)
    (by linarith [hb.1] : (0:ℝ)<lP d) (by norm_num [k] : (0:ℝ)≤k) (by linarith [hη.1]) hc.le hs
    (ratio_l_lt hd hη ht).le (by linarith [(sine_coefficients hη).2])).trans_eq ?_
  ring

def splitA (d : ℝ) : ℝ := -(11/20 : ℝ)-(1/4 : ℝ)*Real.cos d+
  (1017/1000 : ℝ)*Real.sin d
def splitB (d : ℝ) : ℝ := (907/1000 : ℝ)-(1/4 : ℝ)*Real.sin d-
  (1017/1000 : ℝ)*Real.cos d

theorem split_coefficients {d : ℝ} (hd : d∈Icc 0 frameCap) :
    splitA d< -(17/200 : ℝ) ∧ splitB d< -(3/100 : ℝ) := by
  obtain ⟨hc,_,hs0,hs,hslt⟩ := transport_trig hd
  constructor
  · unfold splitA
    linarith
  · let F : ℝ → ℝ := fun x => (1/4 : ℝ)*Real.sin x+(1017/1000 : ℝ)*Real.cos x
    have hconc : ConcaveOn ℝ (Icc 0 frameCap) F := by
      apply concave_of_deriv2
        (f' := fun x => (1/4 : ℝ)*Real.cos x-(1017/1000 : ℝ)*Real.sin x)
        (f'' := fun x => -(1/4 : ℝ)*Real.sin x-(1017/1000 : ℝ)*Real.cos x)
      · intro x _
        exact (((Real.hasDerivAt_sin x).const_mul (1/4 : ℝ)).fun_add
          ((Real.hasDerivAt_cos x).const_mul (1017/1000 : ℝ))).congr_deriv (by ring)
      · intro x _
        exact (((Real.hasDerivAt_cos x).const_mul (1/4 : ℝ)).fun_sub
          ((Real.hasDerivAt_sin x).const_mul (1017/1000 : ℝ))).congr_deriv (by ring)
      · intro x hx
        obtain ⟨hcx,_,hsx,_,_⟩ := transport_trig hx
        linarith
    have hleft : (937/1000 : ℝ)<F 0 := by norm_num [F]
    have hright : (937/1000 : ℝ)<F frameCap := by
      have hc7 := cos_lower_six (by norm_num : (0:ℝ)≤7/10)
      have hs7 := sin_lower_seven (by norm_num : (0:ℝ)≤7/10)
      dsimp [F,frameCap]
      norm_num at hc7 hs7
      linarith
    have h := concave_gt_of_endpoints hconc hd hleft hright
    dsimp [F,splitB] at *
    linarith

def split (d x : ℝ) : ℝ :=
  tdBaseline (Real.sqrt qCap) k (lP d) (etaP d) x (d-x)
def splitDeriv (d x : ℝ) : ℝ :=
  gDeriv (Real.sqrt qCap) 1 k (etaP d) x-
    gDeriv (Real.sqrt qCap) (lP d) k (etaP d) (d-x)
def splitSecond (d x : ℝ) : ℝ :=
  gSecond (Real.sqrt qCap) 1 k (etaP d) x+
    gSecond (Real.sqrt qCap) (lP d) k (etaP d) (d-x)

theorem split_eq (d x : ℝ) :
    split d x=3+2*lP d-Real.sqrt qCap*(pairNorm k (lP d) 0+pairNorm 1 k 0)+
      g (Real.sqrt qCap) 1 k (etaP d) x+
      g (Real.sqrt qCap) (lP d) k (etaP d) (d-x) := by
  simp only [split,tdBaseline,zeroNorms,g,PositiveSplitCalculus.norm,
    PositiveSplitCalculus.radicand,PositiveSplitCalculus.f,SecondaryEStress.tiltedWeight,
    pairNorm_zero]
  ring

theorem split_hasDerivAt {d : ℝ} (hd : d∈Icc 0 frameCap) (x : ℝ) :
    HasDerivAt (split d) (splitDeriv d x) x := by
  have hl : 0<lP d := by linarith [(coefficient_bounds hd).1]
  have h1 := g_hasDerivAt (by norm_num : (0:ℝ)<1) (Real.sqrt qCap) k (etaP d) x
  have h2 := (g_hasDerivAt hl (Real.sqrt qCap) k (etaP d) (d-x)).comp x
    ((hasDerivAt_const x d).sub (hasDerivAt_id x))
  have h := ((hasDerivAt_const x
    (3+2*lP d-Real.sqrt qCap*(pairNorm k (lP d) 0+pairNorm 1 k 0))).add h1).add h2
  convert h using 1
  · funext t
    exact split_eq d t
  · dsimp [splitDeriv]
    ring

theorem splitDeriv_hasDerivAt {d : ℝ} (hd : d∈Icc 0 frameCap) (x : ℝ) :
    HasDerivAt (splitDeriv d) (splitSecond d x) x := by
  have hl : 0<lP d := by linarith [(coefficient_bounds hd).1]
  have h1 := gDeriv_hasDerivAt (by norm_num : (0:ℝ)<1) (Real.sqrt qCap) k (etaP d) x
  have h2 := (gDeriv_hasDerivAt hl (Real.sqrt qCap) k (etaP d) (d-x)).comp x
    ((hasDerivAt_const x d).sub (hasDerivAt_id x))
  convert h1.fun_sub h2 using 1
  · funext t
    simp only [splitDeriv,Function.comp_apply]
  · simp only [splitSecond]
    ring

theorem splitSecond_le {d x : ℝ} (hd : d∈Icc 0 frameCap) (hx : x∈Icc 0 d) :
    splitSecond d x≤-k/20 := by
  have hx' : x∈Icc 0 frameCap := ⟨hx.1,hx.2.trans hd.2⟩
  have hz : d-x∈Icc 0 frameCap := ⟨by linarith [hx.2],by linarith [hx.1,hd.2]⟩
  have h1 := g_one_second_le hd hx'
  have h2 := g_l_second_le hd hz
  have hc := (transport_trig hx').1
  have hs := (transport_trig hx').2.2.1
  have hab := split_coefficients hd
  have ha := mul_le_mul_of_nonneg_right hab.1.le (show 0≤Real.cos x by linarith)
  have hb := mul_le_mul_of_nonneg_right hab.2.le hs
  have hid : -(11/20 : ℝ)*Real.cos x+(907/1000 : ℝ)*Real.sin x-
      (1/4 : ℝ)*Real.cos (d-x)+(1017/1000 : ℝ)*Real.sin (d-x)=
      splitA d*Real.cos x+splitB d*Real.sin x := by
    simp [splitA,splitB,Real.cos_sub,Real.sin_sub]
    ring
  have hsum : splitSecond d x≤k*(splitA d*Real.cos x+splitB d*Real.sin x) := by
    unfold splitSecond
    rw [← hid]
    nlinarith [h1,h2]
  norm_num [k] at *
  nlinarith

/-- A quantitative reserve is retained above the smaller endpoint. -/
theorem familyP_split_lower {d x : ℝ} (hd : d∈Icc 0 frameCap)
    (hx : x∈Icc 0 d) :
    familyPBaseline d+k/40*x*(d-x)≤ split d x := by
  have hg : ConcaveOn ℝ (Icc 0 d) (fun x => split d x+(k/20)/2*x^2) := by
    apply concave_of_deriv2
      (f' := fun x => splitDeriv d x+k/20*x)
      (f'' := fun x => splitSecond d x+k/20)
    · intro x _
      have hp : HasDerivAt (fun y : ℝ => y^2) (2*x) x := by
        simpa using hasDerivAt_pow 2 x
      exact ((split_hasDerivAt hd x).fun_add (hp.const_mul ((k/20)/2))).congr_deriv (by ring)
    · intro x _
      exact ((splitDeriv_hasDerivAt hd x).fun_add
        ((hasDerivAt_id' x).const_mul (k/20))).congr_deriv (by ring)
    · intro x hx
      linarith [splitSecond_le hd hx]
  have h := concave_endpoint_reserve (show 0≤k/20 by norm_num [k]) hx hg
  have hzero : split d 0=familyPBaseline d := by simp [split,familyPBaseline]
  have hend : split d 0≤split d d := by
    simpa [split,familyPBaseline] using familyP_endpoint_le hd
  rw [min_eq_left hend,hzero] at h
  convert h using 1 <;> ring

theorem tdBaseline_ge_familyP {d x z : ℝ} (hd : d∈Icc 0 frameCap)
    (hx : 0≤x) (hz : 0≤z) (hsum : x+z=d) :
    familyPBaseline d≤tdBaseline (Real.sqrt qCap) k (lP d) (etaP d) x z := by
  have hx' : x∈Icc 0 d := ⟨hx,by linarith⟩
  have h := familyP_split_lower hd hx'
  have hz' : z=d-x := by linarith
  have hp : 0≤k/40*x*(d-x) :=
    mul_nonneg (mul_nonneg (by norm_num [k]) hx) (sub_nonneg.mpr hx'.2)
  rw [hz']
  exact le_trans (by linarith) h

theorem btBaseline_ge_familyP {d x z : ℝ} (hd : d∈Icc 0 frameCap)
    (hx : 0≤x) (hz : 0≤z) (hsum : x+z=d) :
    familyPBaseline d≤btBaseline (Real.sqrt qCap) k (lP d) (etaP d) x z :=
  (tdBaseline_ge_familyP hd hx hz hsum).trans
    (familyP_bt_ge_td hd ⟨hz,by linarith⟩)

end SquaresInCircles.Eight.TableFree.PositiveSplitConcavity
