module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2LowPositiveCoefficients
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2AffectedNegativeCurves
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2Polynomial
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2PolynomialData
public import SquaresInCircles.Eight.Owners.GA.Negative.EHSlopes
public import SquaresInCircles.Eight.Owners.GA.Positive.TDLowTransfer
public import SquaresInCircles.Eight.Owners.GA.Two.PositiveAEnvelope

/-!
# Eight squares: the high negative-DE baseline and its positive-surplus branch

The actual baseline is a constant plus the exact secant gain.  The
reserve .96 dominates every original positive ordinary slope, so the
positive-surplus branch reduces to the equal-angle endpoint.
-/

section
/-!
## The sixth-power A support allowance for negative DE

The exact sorted-support loss
is bounded on the complete intrinsic interval [1/2,7/10]; its ratio to
(a-1/6)^6 increases there.  There is no auxiliary angle subdivision.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.AEnvelope
open Candidate Secondary TwoPositive.ASupport

def ratio (a : ℝ) : ℝ := a*(a-1/2)^2/(a-1/6)^6

theorem ratio_derivative {a : ℝ} (ha : (1/2:ℝ)≤a) :
    HasDerivAt ratio ((a-1/2)*(-3*a^2+2*a+1/12)/(a-1/6)^7) a := by
  have hne : a-1/6≠0 := by linarith
  have hp2 : HasDerivAt (fun y : ℝ => (y-1/2)^2) (2*(a-1/2)) a :=
    (((hasDerivAt_id' a).sub_const (1/2:ℝ)).pow 2).congr_deriv (by norm_num)
  have hp6 : HasDerivAt (fun y : ℝ => (y-1/6)^6) (6*(a-1/6)^5) a :=
    (((hasDerivAt_id' a).sub_const (1/6:ℝ)).pow 6).congr_deriv (by norm_num)
  have hd := ((hasDerivAt_id' a).fun_mul hp2).fun_div hp6 (pow_ne_zero 6 hne)
  have hf : ratio=fun y : ℝ => y*(y-1/2)^2/(y-1/6)^6 := rfl
  rw [hf]
  refine hd.congr_deriv ?_
  field_simp
  ring

theorem ratio_monotone : MonotoneOn ratio (Icc (1/2:ℝ) frameCap) := by
  apply monoOn_of_hasDeriv_nonneg
  · intro a ha
    exact (ratio_derivative ha.1).continuousAt.continuousWithinAt
  · intro a ha
    exact ratio_derivative ha.1.le
  · intro a ha
    have ha0 : 0≤a := by linarith [ha.1]
    have hcap : a≤7/10 := by simpa only [frameCap] using ha.2.le
    have hsq : a^2≤(7/10)*a := by nlinarith [mul_nonneg ha0 (sub_nonneg.mpr hcap)]
    have hnum : 0≤-3*a^2+2*a+1/12 := by nlinarith
    exact div_nonneg (mul_nonneg (by linarith [ha.1]) hnum)
      (pow_nonneg (by linarith [ha.1]) 7)

theorem loss_bound {a : ℝ} (ha : a∈Icc (1/2:ℝ) frameCap) :
    (R/8)*a*(a-1/2)^2≤(151/500)*(a-1/6)^6 := by
  have hp : 0<(a-1/6)^6 := pow_pos (by linarith [ha.1]) 6
  have hm := ratio_monotone ha (by norm_num [frameCap]) ha.2
  have he : ratio frameCap=637875/524288 := by norm_num [ratio,frameCap]
  rw [he] at hm
  have hclear := (div_le_iff₀ hp).mp hm
  have hx : 0≤a*(a-1/2)^2 := mul_nonneg (by linarith [ha.1]) (sq_nonneg _)
  have hR : R≤(494696877/250000000:ℝ) := by
    have h := PositiveTD.Certificate.radius_le_Rbar
    rw [show ((PositiveTD.Certificate.Rbar:ℚ):ℝ)=494696877/250000000 by
      norm_num [PositiveTD.Certificate.Rbar]] at h
    exact h
  have hfirst := mul_le_mul_of_nonneg_right hR hx
  have hsecond := mul_le_mul_of_nonneg_left hclear
    (show (0:ℝ)≤494696877/250000000 by norm_num)
  linarith only [hfirst,hsecond,hp]

theorem charge_lower {a : ℝ} (ha : a∈Icc (1/6:ℝ) frameCap) :
    axialCharge a-(151/500)*(a-1/6)^6≤TwoPositive.ASupport.charge a := by
  by_cases hcut : a≤GlobalGA.TwoPositive.ASupport.alpha
  · rw [TwoPositive.ASupport.charge,ite_eq_left hcut]
    have hh : 0≤(151/500:ℝ)*(a-1/6)^6 := by positivity
    linarith
  · have hcircle := circle_loss_bound ⟨(lt_of_not_ge hcut).le,ha.2⟩
    have hr := loss_bound (a:=a) ⟨by linarith [alpha_bounds.1,lt_of_not_ge hcut],ha.2⟩
    rw [TwoPositive.ASupport.charge,ite_eq_right hcut]
    linarith

theorem low_polynomial_charge {a : ℝ} (ha : a∈Icc (0:ℝ) (1/6)) :
    Polynomial.aeval a Certificate.J0≤TwoPositive.ASupport.charge a := by
  simpa only [Certificate.J0,Certificate.abar,TwoPositive.Certificate.lowJ,
    TwoPositive.Certificate.abar] using TwoPositive.ASupport.low_polynomial_charge ha

theorem high_polynomial_charge {a : ℝ} (ha : a∈Icc (1/6:ℝ) frameCap) :
    Polynomial.aeval a Certificate.J1≤TwoPositive.ASupport.charge a := by
  have ha' : a∈Icc 0 frameCap := ⟨by linarith [ha.1],ha.2⟩
  have ht := PositiveTD.Certificate.taylor_bounds ha'
  have hs : 0≤Real.sin a := (transport_trig ha').2.2.1
  have hcoef : (1/2:ℝ)-(Certificate.abar:ℝ)≤0 := by norm_num [Certificate.abar]
  have h₁ := mul_le_mul_of_nonpos_left ht.2.2.1 hcoef
  have hax : axial≤(Certificate.abar:ℝ) := axial_le_abar
  have h₂ := mul_le_mul_of_nonneg_right hax hs
  have hmain := charge_lower ha
  have hJ : Polynomial.aeval a Certificate.J1=(1/2)*(Polynomial.aeval a PositiveTD.Certificate.C10-1)+
      ((1/2:ℝ)-(Certificate.abar:ℝ))*Polynomial.aeval a PositiveTD.Certificate.S9-
        (151/500)*(a-1/6)^6 := by
    simp only [Certificate.J1,Certificate.J0,map_add,map_sub,map_mul,map_pow,map_one,
      Polynomial.aeval_C,Polynomial.aeval_X,eq_ratCast]
    rw [show ((1/2:ℚ):ℝ)=1/2 by norm_num,show ((151/500:ℚ):ℝ)=151/500 by norm_num,
      show ((PositiveTD.Certificate.L:ℚ):ℝ)=1/6 by norm_num [PositiveTD.Certificate.L]]
  rw [hJ]
  dsimp [axialCharge] at hmain
  generalize ((Certificate.abar:ℚ):ℝ)=A at h₁ h₂ ⊢
  linarith only [hmain,ht.2.2.2.2.1,h₁,h₂]

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.AEnvelope
end
end
end

section
/-!
## Actual nonradical and force-norm bounds at the A/TD split endpoints

The equal-angle endpoints retain the actual positive cosine multiplier,
and the DE secant remains in the D force until that multiplication.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.Certificate
open Candidate Secondary Polynomial PositiveAngularEnvelope OrdinaryAngleConcavity
open PositiveTD.Certificate (C10 C12 S9 S11 C4 S5 ch Ch sh h cbar sigmabar
  taylor_bounds zero_norm_sq negative_norm_sq_le pairNorm_nonneg)

private lemma r73_explicit_dom (f : Family) {θ : ℝ} (hθ : θ∈Icc (left f:ℝ) (right f:ℝ)) :
    θ∈Icc (Explicit.left f) (Explicit.right f) := by
  cases f <;> norm_num [left,right,Explicit.left,Explicit.right,Explicit.L,
    PositiveTD.Certificate.L,PositiveTD.Certificate.h,frameCap] at hθ ⊢ <;> exact hθ

private lemma r73_dom_low {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) : θ∈Icc (left .low:ℝ) (right .low:ℝ) := by
  norm_num [left,right,PositiveTD.Certificate.L]
  exact hθ

private lemma r73_dom_high {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    θ∈Icc (left .high:ℝ) (right .high:ℝ) := by
  norm_num [left,right,PositiveTD.Certificate.L,PositiveTD.Certificate.h]
  exact hθ

theorem family_frame_domain (f : Family) {θ : ℝ}
    (hθ : θ∈Icc (left f:ℝ) (right f:ℝ)) : θ∈Icc 0 frameCap := by
  exact Explicit.family_frame_domain f (r73_explicit_dom f hθ)

theorem split_angles (e : Split) {θ : ℝ} (hθ : θ∈Icc 0 frameCap) :
    Explicit.splitA e θ∈Icc 0 θ ∧ Explicit.splitT e θ∈Icc 0 θ ∧
      Explicit.splitA e θ+Explicit.splitT e θ=θ := by
  cases e <;> simp only [Explicit.splitA,Explicit.splitT] <;>
    refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,?_⟩ <;> linarith [hθ.1]

theorem split_positive (f : Family) (e : Split) {θ : ℝ}
    (hθ : θ∈Icc (left f:ℝ) (right f:ℝ)) :
    0<Explicit.k f θ ∧ 0<Explicit.l f θ ∧ 0<Explicit.c f θ ∧ 0<Explicit.splitM f e θ := by
  exact Explicit.family_positive f (r73_explicit_dom f hθ)
    (split_angles e (family_frame_domain f hθ)).2.1

theorem tilted_bounds (f : Family) (e : Split) {θ : ℝ}
    (hθ : θ∈Icc (left f:ℝ) (right f:ℝ)) :
    0<aeval θ (mLo f e) ∧ aeval θ (mLo f e)≤Explicit.splitM f e θ ∧
      Explicit.splitM f e θ≤aeval θ (mHi f e) := by
  have hc := (split_positive f e hθ).2.2.1
  cases e
  · have ht := PositiveTD.Certificate.tilted_polynomial_bounds (c:=c f)
      (family_frame_domain f hθ) (by simpa using hc)
    simpa [mLo,mHi,Explicit.splitM,Explicit.splitT,Explicit.m,Explicit.eta,
      PositiveTD.tilted,PositiveTD.eta,PositiveTD.Certificate.mMinus,
      PositiveTD.Certificate.mPlus] using ht
  · simpa [mLo,mHi,Explicit.splitM,Explicit.splitT,Explicit.m] using
      (show 0<Explicit.c f θ ∧ Explicit.c f θ≤Explicit.c f θ ∧
        Explicit.c f θ≤Explicit.c f θ from ⟨hc,le_rfl,le_rfl⟩)

def lowNonradical (e : Split) (θ : ℝ) : ℝ :=
  2*Explicit.k .low θ+3*Explicit.l .low θ+(3/2)*Explicit.splitM .low e θ+5/2+
    Explicit.c .low θ*edgeWidth (Explicit.splitT e θ)-
    Explicit.c .low θ*Explicit.sigma*Real.sin (Explicit.splitT e θ)+
    Explicit.l .low θ*TwoPositive.ASupport.charge (Explicit.splitA e θ)-
    (1+Explicit.c .low θ)*GlobalGA.Secondary.diagonal
def highNonradical (e : Split) (θ : ℝ) : ℝ :=
  2*Explicit.k .high θ+3*Explicit.l .high θ+(3/2)*Explicit.splitM .high e θ+
    Explicit.c .high θ/2+3+Explicit.c .high θ*edgeWidth (Explicit.splitT e θ)-
    Explicit.c .high θ*Explicit.sigma*Real.sin (Explicit.splitT e θ)+
    Explicit.l .high θ*TwoPositive.ASupport.charge (Explicit.splitA e θ)

theorem low_nonradical_lower (e : Split) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    aeval θ (lowB e)≤lowNonradical e θ := by
  obtain ⟨hk,hl,hc,hm⟩ := split_positive .low e (r73_dom_low hθ)
  have ht := taylor_bounds (family_frame_domain .low (r73_dom_low hθ))
  have htilt := (tilted_bounds .low e (r73_dom_low hθ)).2.1
  have hD := mul_le_mul_of_nonneg_left PositiveTD.Certificate.diagonal_le_cbar
    (show 0≤1+Explicit.c .low θ by linarith)
  rw [show ((cbar:ℚ):ℝ)=449607033/500000000 by norm_num [cbar]] at hD
  have hsig : Explicit.sigma=PositiveTD.sigma := rfl
  cases e
  · have hs := PositiveTD.Certificate.sigma_sine_upper (family_frame_domain .low (r73_dom_low hθ)) hc.le
    rw [show ((sigmabar:ℚ):ℝ)=1415477291/1000000000 by norm_num [sigmabar]] at hs
    have hW0 := mul_le_mul_of_nonneg_left (add_le_add ht.2.2.2.2.1 ht.2.1) hc.le
    have hW : Explicit.c .low θ/2*(1+aeval θ C10+aeval θ S11)≤
        Explicit.c .low θ*edgeWidth θ := by
      rw [edgeWidth_positive_formula (family_frame_domain .low (r73_dom_low hθ))]
      nlinarith only [hW0]
    have hj : TwoPositive.ASupport.charge 0=0 := by
      rw [TwoPositive.ASupport.charge_low (by norm_num)]
      norm_num [TwoPositive.ASupport.axialCharge]
    norm_num only [lowB,lowE,map_add,map_sub,map_mul,map_one,aeval_C,k_eval,l_eval,c_eval,
      eq_ratCast]
    simp only [lowNonradical,Explicit.splitA,Explicit.splitT,hj,mul_zero,add_zero,hsig]
    linarith only [htilt,hD,hs,hW]
  · have hJ := mul_le_mul_of_nonneg_left (AEnvelope.low_polynomial_charge hθ) hl.le
    have hW : edgeWidth 0=1 := by norm_num [edgeWidth,pairWidth]
    norm_num only [lowB,lowE,map_add,map_sub,map_mul,map_one,aeval_C,k_eval,l_eval,c_eval,
      eq_ratCast]
    simp only [lowNonradical,Explicit.splitA,Explicit.splitT,Explicit.splitM,Explicit.m,
      Real.cos_zero,Real.sin_zero,mul_zero,mul_one,add_zero,sub_zero,hW]
    linarith only [hD,hJ]

theorem high_nonradical_lower (e : Split) {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    aeval θ (highB e)≤highNonradical e θ := by
  obtain ⟨hk,hl,hc,hm⟩ := split_positive .high e (r73_dom_high hθ)
  have ht := taylor_bounds (family_frame_domain .high (r73_dom_high hθ))
  have htilt := (tilted_bounds .high e (r73_dom_high hθ)).2.1
  have hsig : Explicit.sigma=PositiveTD.sigma := rfl
  cases e
  · have hs := PositiveTD.Certificate.sigma_sine_upper (family_frame_domain .high (r73_dom_high hθ)) hc.le
    rw [show ((sigmabar:ℚ):ℝ)=1415477291/1000000000 by norm_num [sigmabar]] at hs
    have hW0 := mul_le_mul_of_nonneg_left (add_le_add ht.2.2.2.2.1 ht.2.1) hc.le
    have hW : Explicit.c .high θ/2*(1+aeval θ C10+aeval θ S11)≤
        Explicit.c .high θ*edgeWidth θ := by
      rw [edgeWidth_positive_formula (family_frame_domain .high (r73_dom_high hθ))]
      nlinarith only [hW0]
    have hj : TwoPositive.ASupport.charge 0=0 := by
      rw [TwoPositive.ASupport.charge_low (by norm_num)]
      norm_num [TwoPositive.ASupport.axialCharge]
    norm_num only [highB,map_add,map_sub,map_mul,map_one,aeval_C,k_eval,l_eval,c_eval,eq_ratCast]
    simp only [highNonradical,Explicit.splitA,Explicit.splitT,hj,mul_zero,add_zero,hsig]
    linarith only [htilt,hs,hW]
  · have hJ := mul_le_mul_of_nonneg_left (AEnvelope.high_polynomial_charge hθ) hl.le
    have hW : edgeWidth 0=1 := by norm_num [edgeWidth,pairWidth]
    norm_num only [highB,map_add,map_sub,map_mul,map_one,aeval_C,k_eval,l_eval,c_eval,eq_ratCast]
    simp only [highNonradical,Explicit.splitA,Explicit.splitT,Explicit.splitM,Explicit.m,
      Real.cos_zero,Real.sin_zero,mul_zero,mul_one,add_zero,sub_zero,hW]
    linarith only [hJ]

theorem ordinary_norm_bounds (f : Family) (e : Split) {θ : ℝ}
    (hθ : θ∈Icc (left f:ℝ) (right f:ℝ)) :
    (pairNorm (Explicit.k f θ) 1 0)^2≤aeval θ (PH f) ∧
    (pairNorm (Explicit.k f θ) (Explicit.l f θ) 0)^2≤aeval θ (PG f) ∧
    (pairNorm (Explicit.l f θ) (Explicit.splitM f e θ) 0)^2≤aeval θ (PB f e) ∧
    (pairNorm 1 (Explicit.c f θ) 0)^2≤aeval θ (PD f) ∧
    (pairNorm (Explicit.k f θ) 1 (-θ))^2≤aeval θ (PHminus f) ∧
    (pairNorm (Explicit.k f θ) (Explicit.l f θ) (-θ))^2≤aeval θ (PGminus f) ∧
    (pairNorm (Explicit.l f θ) (Explicit.splitM f e θ) (-θ))^2≤aeval θ (PBminus f e) := by
  obtain ⟨hk,hl,hc,hm⟩ := split_positive f e hθ
  have hθ' := family_frame_domain f hθ
  have ht := taylor_bounds hθ'
  obtain ⟨hmLo0,hmLo,hmHi⟩ := tilted_bounds f e hθ
  have hm2 : (Explicit.splitM f e θ)^2≤(aeval θ (mHi f e))^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hmHi)
      (show 0≤aeval θ (mHi f e)+Explicit.splitM f e θ by linarith)]
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · rw [zero_norm_sq]; simp [PH,add_comm]
  · rw [zero_norm_sq]; simp [PG]
  · rw [zero_norm_sq]; simp only [PB,map_add,map_pow,l_eval]; linarith
  · rw [zero_norm_sq]; simp [PD]
  · have hh := negative_norm_sq_le (q:=1) hk (by norm_num) hθ' ht.2.1
    norm_num only [PHminus,PH,map_add,map_sub,map_mul,map_pow,map_one,aeval_C,k_eval,eq_ratCast]
    nlinarith only [hh]
  · have hh := negative_norm_sq_le hk hl hθ' ht.2.1
    norm_num only [PGminus,PG,map_add,map_sub,map_mul,map_pow,aeval_C,k_eval,l_eval,eq_ratCast]
    nlinarith only [hh]
  · have hh := negative_norm_sq_le hl hm hθ' ht.2.1
    have hp := mul_le_mul_of_nonneg_left hmLo
      (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hl.le) ht.1)
    norm_num only [PBminus,PB,map_add,map_sub,map_mul,map_pow,aeval_C,l_eval,eq_ratCast]
    nlinarith only [hh,hp,hm2]

theorem cap_norm_bounds {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    (pairNorm (Explicit.k .low θ) 1 (-frameCap))^2≤aeval θ PHcap ∧
    (pairNorm (Explicit.k .low θ) (Explicit.l .low θ) (-frameCap))^2≤aeval θ PGcap := by
  obtain ⟨hk,hl,_,_⟩ := split_positive .low .atT (r73_dom_low hθ)
  have hc : frameCap∈Icc 0 frameCap := ⟨by norm_num [frameCap],le_rfl⟩
  have hs := (taylor_bounds hc).2.1
  constructor
  · have hh := negative_norm_sq_le (q:=1) hk (by norm_num) hc hs
    simp only [PHcap,PH,map_sub,map_add,map_mul,map_pow,map_one,aeval_C,
      k_eval,eq_ratCast,Rat.cast_ofNat,PositiveTD.Certificate.sh_cast]
    linarith only [hh]
  · have hh := negative_norm_sq_le hk hl hc hs
    simp only [PGcap,PG,map_sub,map_add,map_mul,map_pow,aeval_C,
      k_eval,l_eval,eq_ratCast,Rat.cast_ofNat,PositiveTD.Certificate.sh_cast]
    linarith only [hh]

theorem cosine_square_upper {θ : ℝ} (hθ : θ∈Icc 0 frameCap) :
    (Real.cos θ)^2≤(aeval θ C12)^2 := by
  have ht := taylor_bounds hθ
  have hc : 0≤Real.cos θ := by linarith [(transport_trig hθ).1]
  nlinarith [mul_nonneg (sub_nonneg.mpr ht.2.2.2.2.2)
    (show 0≤aeval θ C12+Real.cos θ by linarith [ht.2.2.2.2.2])]

theorem scaled_norm_bound {θ n : ℝ} {P : ℚ[X]} (hθ : θ∈Icc 0 frameCap)
    (hn : n^2≤aeval θ P) : (Real.cos θ*n)^2≤aeval θ (C12^2*P) := by
  have hh := mul_le_mul (cosine_square_upper hθ) hn (sq_nonneg n) (sq_nonneg _)
  simpa only [mul_pow,map_mul,map_pow] using hh

theorem scaled_secant_norm_bound {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    (Real.cos θ*pairNorm (Explicit.secant θ) (Explicit.c .high θ) 0)^2≤
      aeval θ (1+(c .high)^2*C12^2) := by
  have hc : 0<Real.cos θ := by linarith [(transport_trig (family_frame_domain .high (r73_dom_high hθ))).1]
  have he : (Real.cos θ*pairNorm (Explicit.secant θ) (Explicit.c .high θ) 0)^2=
      1+(Explicit.c .high θ)^2*(Real.cos θ)^2 := by
    rw [mul_pow,zero_norm_sq]
    dsimp [Explicit.secant]
    field_simp [hc.ne']
  rw [he]
  have hh := mul_le_mul_of_nonneg_left (cosine_square_upper (family_frame_domain .high (r73_dom_high hθ)))
    (sq_nonneg (Explicit.c .high θ))
  simp only [map_add,map_one,map_mul,map_pow,c_eval]
  linarith [hh]

theorem qStar_lower (e : Split) {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    max (Explicit.l .high θ) (Explicit.splitM .high e θ)≤aeval θ qStar := by
  have hl : Explicit.l .high θ≤aeval θ qStar := by
    simp only [qStar,map_add,map_mul,map_sub,aeval_C,aeval_X,l_eval]
    norm_num [PositiveTD.Certificate.h]
    linarith [hθ.2]
  apply max_le hl
  cases e
  · have hc := (split_positive .high .atT (r73_dom_high hθ)).2.2.1
    have hθ' := family_frame_domain .high (r73_dom_high hθ)
    have hs := sin_upper_five hθ'.1
    have hcos := cos_upper_four hθ'.1
    have happrox : Explicit.splitM .high .atT θ≤aeval θ (mu .high .atT) := by
      have hh := mul_le_mul_of_nonneg_left
        (show Real.cos θ+(293/1000)*Real.sin θ≤
          (1-θ^2/2+θ^4/24)+(293/1000)*(θ-θ^3/6+θ^5/120) by
            linarith) hc.le
      have hmu : aeval θ (mu .high .atT)=Explicit.c .high θ*
          ((1-θ^2/2+θ^4/24)+(293/1000)*(θ-θ^3/6+θ^5/120)) := by
        simp only [mu,C4,S5,PositiveTD.Certificate.etaQ,map_mul,map_add,map_sub,map_one,
          map_pow,aeval_C,aeval_X,c_eval,eq_ratCast,reduceCtorEq,↓reduceIte]
        push_cast
        ring
      rw [hmu]
      exact hh
    have hcert := quadratic_positive .highQStar (r73_dom_high hθ)
    simp only [quadraticReserveValue,quadraticPolynomial,map_sub] at hcert
    have hpos : (0:ℝ)≤((51799/10000000:ℚ):ℝ) := by norm_num
    exact happrox.trans (by linarith)
  · have hcert := qStar_A_positive hθ
    simp only [map_sub,c_eval] at hcert
    simpa [Explicit.splitM,Explicit.splitT,Explicit.m] using (le_of_lt (sub_pos.mp hcert))

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.Certificate
end
end
end

section
/-!
## The ordinary slope reserves used by the negative-E concentrations

A
single decreasing normalized lower function proves each positive slope
bound.  The negative slope uses the intrinsic ratio endpoint 2/3 and
the original angle endpoint 8/15.  All bounds apply on whole intervals.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.OrdinarySlope
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open NegativeAPositiveTD.PositiveSlope OrdinaryNegativeSlope

def endpoint : Bool → ℝ | false => frameCap | true => 8/15
def linearCoefficient : Bool → ℝ | false => 3/25 | true => 7/20
def numeratorBound : Bool → ℝ | false => 757/500 | true => 853/500
def sineCoefficient : Bool → ℝ | false => 161/125 | true => 127/125
def rootUpper : Bool → ℝ | false => 907/500 | true => 869/500
def rootLower : Bool → ℝ | false => 1813/1000 | true => 217/125
def allowance : Bool → ℝ | false => 18/25 | true => 16/25
def modelRoot (short : Bool) (r : ℝ) : ℝ := Real.sqrt (1+r^2+sineCoefficient short*r)
def model (short : Bool) (r : ℝ) : ℝ :=
  linearCoefficient short*r-numeratorBound short*r/modelRoot short r

theorem coefficient_signs (short : Bool) :
    0<linearCoefficient short ∧ 0<numeratorBound short ∧
      0<sineCoefficient short ∧ 0<rootUpper short ∧ 0<rootLower short := by
  cases short <;> norm_num [linearCoefficient,numeratorBound,sineCoefficient,rootUpper,rootLower]

theorem endpoint_domain (short : Bool) : endpoint short∈Icc 0 frameCap := by
  cases short <;> norm_num [endpoint,frameCap]

theorem endpoint_trig (short : Bool) :
    linearCoefficient short<Real.cos (endpoint short)-Real.sin (endpoint short) ∧
      R*Real.cos (endpoint short)<numeratorBound short ∧
      sineCoefficient short<2*Real.sin (endpoint short) := by
  have hcl := Arithmetic.cos10_le_cos (show 0≤endpoint short from (endpoint_domain short).1)
  have hch := HighOrderTaylor.cos_le_C12 (show 0≤endpoint short from (endpoint_domain short).1)
  have hsl := HighOrderTaylor.S11_le_sin (show 0≤endpoint short from (endpoint_domain short).1)
  have hsh := Arithmetic.sin_le_sin9 (show 0≤endpoint short from (endpoint_domain short).1)
  have hc0 : 0≤Real.cos (endpoint short) := by linarith [(transport_trig (endpoint_domain short)).1]
  have hprod := mul_le_mul PositiveTD.Certificate.radius_le_Rbar hch hc0
    (by norm_num [PositiveTD.Certificate.Rbar] : (0:ℝ)≤(PositiveTD.Certificate.Rbar:ℝ))
  cases short <;>
    norm_num [endpoint,linearCoefficient,numeratorBound,sineCoefficient,frameCap,
      HighOrderTaylor.S11,HighOrderTaylor.C12,Arithmetic.sin9,Arithmetic.sin7,
      Arithmetic.cos10,Arithmetic.cos8,PositiveTD.Certificate.Rbar]
      at hcl hch hsl hsh hprod ⊢ <;>
    exact ⟨by linarith,by linarith,by linarith⟩

theorem model_root_data (short : Bool) {r : ℝ} (hr : r∈Icc (1/2:ℝ) 1) :
    0< modelRoot short r ∧ (modelRoot short r)^2=1+r^2+sineCoefficient short*r ∧
      modelRoot short r<rootUpper short := by
  have hc := coefficient_signs short
  have hr0 : 0<r := by linarith [hr.1]
  have hsr := mul_pos hc.2.2.1 hr0
  have hs : 0<1+r^2+sineCoefficient short*r := by linarith [sq_nonneg r]
  have hn : 0 < modelRoot short r := Real.sqrt_pos.mpr hs
  have he : (modelRoot short r)^2=1+r^2+sineCoefficient short*r := Real.sq_sqrt hs.le
  have hr2 : r^2≤1 := by nlinarith [hr.2]
  refine ⟨hn,he,?_⟩
  cases short <;> norm_num [sineCoefficient,rootUpper] at he ⊢ <;>
    nlinarith [hr.2,hn]

theorem model_root_derivative (short : Bool) {r : ℝ} (hr : r∈Icc (1/2:ℝ) 1) :
    HasDerivAt (modelRoot short) ((2*r+sineCoefficient short)/(2*modelRoot short r)) r := by
  have hn := model_root_data short hr
  have hh := (((hasDerivAt_const r (1:ℝ)).add ((hasDerivAt_id r).pow 2)).add
    ((hasDerivAt_id r).const_mul (sineCoefficient short))).sqrt
    (by nlinarith [hn.1,hn.2.1] : 1+r^2+sineCoefficient short*r≠0)
  convert hh using 1
  · rfl
  · dsimp [modelRoot]
    ring

theorem model_derivative (short : Bool) {r : ℝ} (hr : r∈Icc (1/2:ℝ) 1) :
    HasDerivAt (model short)
      (linearCoefficient short-numeratorBound short*(1+sineCoefficient short*r/2)/
        (modelRoot short r)^3) r := by
  have hn := model_root_data short hr
  have hh := ((hasDerivAt_id r).const_mul (linearCoefficient short)).sub
    (((hasDerivAt_id r).const_mul (numeratorBound short)).div
      (model_root_derivative short hr) hn.1.ne')
  convert hh using 1
  · rfl
  · have hm := hn.1.ne'
    simp only [id]
    field_simp
    linear_combination (2*numeratorBound short)*hn.2.1

theorem model_antitone (short : Bool) : AntitoneOn (model short) (Icc (1/2:ℝ) 1) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun r hr => (model_derivative short hr).continuousAt.continuousWithinAt)
    (fun r hr => model_derivative short (Ioo_subset_Icc_self hr))
  intro r hr
  have hn := model_root_data short (Ioo_subset_Icc_self hr)
  have hc := coefficient_signs short
  have hp := pow_le_pow_left₀ hn.1.le hn.2.2.le 3
  have hscaled := mul_le_mul_of_nonneg_left hp hc.1.le
  have hright : linearCoefficient short*(modelRoot short r)^3≤
      numeratorBound short*(1+sineCoefficient short*r/2) := by
    cases short <;> norm_num [linearCoefficient,rootUpper,numeratorBound,sineCoefficient] at hscaled ⊢ <;>
      nlinarith [hr.1]
  have hh := (le_div_iff₀ (pow_pos hn.1 3)).2 hright
  linarith

theorem model_endpoint (short : Bool) : -allowance short< model short 1 := by
  have hn := model_root_data short (r:=1) (by norm_num)
  have hc := coefficient_signs short
  have hl : rootLower short< modelRoot short 1 := by
    cases short <;> norm_num [rootLower,sineCoefficient] at hn ⊢ <;> nlinarith
  have hcross : numeratorBound short<
      (linearCoefficient short+allowance short)*modelRoot short 1 := by
    cases short <;> norm_num [rootLower,numeratorBound,linearCoefficient,allowance] at hl ⊢ <;>
      linarith
  have hh := (div_lt_iff₀ hn.1).2 hcross
  dsimp [model]
  simp only [mul_one]
  linarith

theorem normalized_endpoint (short : Bool) {r : ℝ} (hr : r∈Icc (1/2:ℝ) 1) :
    -allowance short<r*(Real.cos (endpoint short)-Real.sin (endpoint short))-
      R*r*Real.cos (endpoint short)/pairNorm r 1 (endpoint short) := by
  have hr0 : 0<r := by linarith [hr.1]
  have hn := model_root_data short hr
  have hN := pairNorm_pos hr0 (by norm_num : (0:ℝ)<1)
    (by rw [abs_of_nonneg (endpoint_domain short).1]; exact (endpoint_domain short).2)
  have hN2 := pairNorm_sq hr0 (by norm_num : (0:ℝ)<1)
    (by rw [abs_of_nonneg (endpoint_domain short).1]; exact (endpoint_domain short).2)
  norm_num only [pairEnergy,pairProduct,one_pow,mul_one] at hN2
  obtain ⟨hphi,hcos,hsin⟩ := endpoint_trig short
  have hroot : modelRoot short r≤pairNorm r 1 (endpoint short) := by
    have hh := mul_le_mul_of_nonneg_right hsin.le hr0.le
    nlinarith [hn.2.1]
  have hnum : R*r*Real.cos (endpoint short)≤numeratorBound short*r := by
    nlinarith only [mul_le_mul_of_nonneg_right hcos.le hr0.le]
  have hquot := div_le_div₀ (by have hc := (coefficient_signs short).2.1; positivity)
    hnum hn.1 hroot
  have hlin := mul_le_mul_of_nonneg_right hphi.le hr0.le
  have hlower : model short r≤r*(Real.cos (endpoint short)-Real.sin (endpoint short))-
      R*r*Real.cos (endpoint short)/pairNorm r 1 (endpoint short) := by
    dsimp [model]
    nlinarith only [hquot,hlin]
  exact (model_endpoint short).trans_le
    ((model_antitone short hr (by norm_num) hr.2).trans hlower)

theorem positive_derivative (short : Bool) {p q x : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) (hx : x∈Icc 0 (endpoint short)) :
    -allowance short*q<Ud p q x := by
  have hq := hp.trans_le hpq
  have hr : p/q∈Icc (1/2:ℝ) 1 :=
    ⟨(le_div_iff₀ hq).2 (by linarith),(div_le_one hq).2 hpq⟩
  have he : -allowance short*q<Ud p q (endpoint short) := by
    rw [Ud_normalized hq]
    simpa [mul_comm] using mul_lt_mul_of_pos_left (normalized_endpoint short hr) hq
  exact he.trans_le (Ud_antitone hp hpq hqp ⟨hx.1,hx.2.trans (endpoint_domain short).2⟩
    (endpoint_domain short) hx.2)

theorem positive_derivative_whole {p q x : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) (hx : x∈Icc 0 frameCap) :
    -(18/25)*q<Ud p q x := positive_derivative false hp hpq hqp hx

theorem positive_derivative_short {p q x : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) (hx : x∈Icc 0 (8/15:ℝ)) :
    -(16/25)*q<Ud p q x := positive_derivative true hp hpq hqp hx

theorem negative_short_endpoint :
    (39/50:ℝ)< -Real.sin (8/15:ℝ)+
      R*(2/3)*Real.cos (8/15:ℝ)/VaryingBFunctions.root (2/3) (Real.sin (8/15:ℝ)) := by
  have hx : (8/15:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hN := VaryingBFunctions.root_pos (2/3) (VaryingBFunctions.sin_mem hx)
  have hN2 := VaryingBFunctions.root_sq (2/3) (VaryingBFunctions.sin_mem hx)
  have hsl := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤8/15 by norm_num)
  have hsh := Arithmetic.sin_le_sin9 (show (0:ℝ)≤8/15 by norm_num)
  have hcl := Arithmetic.cos10_le_cos (show (0:ℝ)≤8/15 by norm_num)
  have ht : (5084/10000:ℝ)<Real.sin (8/15:ℝ) ∧
      Real.sin (8/15:ℝ)<5085/10000 ∧ (8611/10000:ℝ)<Real.cos (8/15:ℝ) := by
    norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
      Arithmetic.cos10,Arithmetic.cos8] at hsl hsh hcl
    exact ⟨by linarith,by linarith,by linarith⟩
  have hNu : VaryingBFunctions.root (2/3) (Real.sin (8/15:ℝ))<(219/250:ℝ) := by
    nlinarith [ht.1]
  have hR : (19787/10000:ℝ)<R := by linarith [radius_bounds.1]
  have hprod := mul_lt_mul'' hR ht.2.2 (by norm_num) (by norm_num)
  have hupper := mul_lt_mul_of_pos_left hNu
    (show 0<(39/50:ℝ)+Real.sin (8/15:ℝ) by linarith [ht.1])
  have hupper2 := mul_lt_mul_of_pos_right ht.2.1 (by norm_num : (0:ℝ)<219/250)
  have hcross : ((39/50:ℝ)+Real.sin (8/15:ℝ))*
      VaryingBFunctions.root (2/3) (Real.sin (8/15:ℝ))<R*(2/3)*Real.cos (8/15:ℝ) := by
    nlinarith
  have hdiv := (lt_div_iff₀ hN).2 hcross
  linarith

theorem negative_derivative_short {p q x : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : (2/3)*q≤p) (hx : x∈Icc 0 (8/15:ℝ)) :
    (39/50)*q<Vd R p q x := by
  have hq := hp.trans_le hpq
  have harg : (8/15:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hfrac := normalized_fraction_mono (by norm_num : (0:ℝ)≤2/3)
    ((le_div_iff₀ hq).2 hqp) ((div_le_one hq).2 hpq) (VaryingBFunctions.sin_mem harg)
  have hm := mul_le_mul_of_nonneg_left hfrac
    (show 0≤R*Real.cos (8/15:ℝ) by
      exact mul_nonneg (Real.sqrt_nonneg _) (by linarith [(transport_trig harg).1]))
  have hs : (39/50:ℝ) < -Real.sin (8/15:ℝ)+
      R*(p/q)*Real.cos (8/15:ℝ)/VaryingBFunctions.root (p/q) (Real.sin (8/15:ℝ)) := by
    have hbase := negative_short_endpoint
    have e1 : R*(p/q)*Real.cos (8/15:ℝ)/VaryingBFunctions.root (p/q) (Real.sin (8/15:ℝ))=
        R*Real.cos (8/15:ℝ)*(p/q/VaryingBFunctions.root (p/q) (Real.sin (8/15:ℝ))) := by ring
    have e2 : R*(2/3)*Real.cos (8/15:ℝ)/VaryingBFunctions.root (2/3) (Real.sin (8/15:ℝ))=
        R*Real.cos (8/15:ℝ)*(2/3/VaryingBFunctions.root (2/3) (Real.sin (8/15:ℝ))) := by ring
    rw [e1]
    rw [e2] at hbase
    linarith
  have he : (39/50)*q<Vd R p q (8/15:ℝ) := by
    rw [Vd_normalized hq]
    nlinarith only [mul_lt_mul_of_pos_left hs hq]
  exact he.trans_le (Vd_antitone (Real.sqrt_nonneg qCap) radius_sq.le hp hpq
    (by linarith) ⟨hx.1,by norm_num [frameCap]; linarith [hx.2]⟩ harg hx.2)

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.OrdinarySlope
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.HighSecant
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

private theorem r74_high {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    θ∈Icc ((Certificate.left .high:ℚ):ℝ) ((Certificate.right .high:ℚ):ℝ) := by
  simpa [Certificate.left,Certificate.right,PositiveTD.Certificate.L,
    PositiveTD.Certificate.h] using hθ

theorem full_gain_identity (f : Family) (a z : ℝ) {s : ℝ}
    (hs : s∈Icc 0 frameCap) :
    Explicit.fullBaseline f a z s=Explicit.fullBaseline f a z 0+
      secantGain qCap (Explicit.c f (a+z)) s := by
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  rw [secantGain_eq_secant_expression qCap (Explicit.c f (a+z)) hc]
  simp only [Explicit.fullBaseline,Explicit.baseline,fullSupport_pair,
    Explicit.secant,Real.cos_zero,Real.tan_zero,div_one,mul_zero,sub_self,
    add_zero]
  simp only [pairNorm,Real.sin_zero,mul_zero,add_zero,one_pow]
  rw [show (Explicit.c f (a+z))^2+(1/Real.cos s)^2=
    (1/Real.cos s)^2+(Explicit.c f (a+z))^2 by ring,
    show (Explicit.c f (a+z))^2+1=1+(Explicit.c f (a+z))^2 by ring]
  dsimp [Explicit.K]
  ring

theorem full_derivative_lower {c s : ℝ} (hc : (43/50:ℝ)≤c)
    (hs : s∈Icc 0 frameCap) : (24/25:ℝ)<secantGainDeriv qCap c s := by
  have ht := transport_trig hs
  have hcos : 0<Real.cos s := by linarith [ht.1]
  have hcoeff := NegativeAPositiveTD.SecantBaseline.coefficient_upper
    (r:=c) (s:=s) (r₀:=43/50) (c₀:=478/625) (D:=83/50)
    (by norm_num) (by norm_num) (by norm_num) hc (by linarith [ht.1])
    (by norm_num [qCap])
  have hm := mul_le_mul_of_nonneg_right hcoeff.le ht.2.2.1
  have he : R*Real.sin s/NegativeAPositiveTD.SecantBaseline.denominator c s=
      (R/NegativeAPositiveTD.SecantBaseline.denominator c s)*Real.sin s := by ring
  change (24/25:ℝ)<(13/12+Real.sin s-
    R*Real.sin s/NegativeAPositiveTD.SecantBaseline.denominator c s)/Real.cos s^2
  apply (lt_div_iff₀ (sq_pos_of_pos hcos)).2
  rw [he]
  nlinarith [Real.sin_sq_add_cos_sq s,sq_nonneg (Real.sin s-11/32)]

theorem high_gain_derivative_lower {θ s : ℝ}
    (hθ : θ∈Icc (1/6:ℝ) (7/10)) (hs : s∈Icc 0 frameCap) :
    (24/25:ℝ)<secantGainDeriv qCap (Explicit.c .high θ) s := by
  apply full_derivative_lower _ hs
  linarith [(Explicit.high_ranges hθ).2.2.2.2.1]

theorem positive_surplus_mono {θ z : ℝ}
    (hθ : θ∈Icc (1/6:ℝ) (7/10)) (hz : z∈Icc 0 θ) (i : Fin 3) :
    MonotoneOn (fun s => secantGain qCap (Explicit.c .high θ) s+
      Explicit.U .high θ z i (s-θ)) (Icc θ frameCap) := by
  have hp := Explicit.high_pairs hθ hz i
  have hq := hp.1.trans_le hp.2.1
  have hqp : Explicit.q .high θ z i≤2*Explicit.p .high θ z i := by
    linarith [hp.2.2.1]
  have hd (s : ℝ) (hs : s∈Icc θ frameCap) :
      HasDerivAt (fun s => secantGain qCap (Explicit.c .high θ) s+
        Explicit.U .high θ z i (s-θ))
      (secantGainDeriv qCap (Explicit.c .high θ) s+
        NegativeAPositiveTD.PositiveSlope.Ud (Explicit.p .high θ z i) (Explicit.q .high θ z i) (s-θ)) s := by
    have hsf : s∈Icc 0 frameCap := ⟨by linarith [hθ.1,hs.1],hs.2⟩
    have hx : s-θ∈Icc 0 frameCap := ⟨by linarith [hs.1],by linarith [hs.2,hθ.1]⟩
    have hg := secantGain_hasDerivAt qCap (Explicit.c .high θ)
      (show Real.cos s≠0 by linarith [(transport_trig hsf).1])
    have hu : HasDerivAt (fun s => Explicit.U .high θ z i (s-θ))
        (NegativeAPositiveTD.PositiveSlope.Ud (Explicit.p .high θ z i)
          (Explicit.q .high θ z i) (s-θ)) s := by
      have hc := (NegativeAPositiveTD.PositiveSlope.U_hasDerivAt hp.1 hq hx).comp s
        ((hasDerivAt_id s).sub_const θ)
      simpa only [Explicit.U,mul_one,Function.comp_def,id] using hc
    exact hg.add hu
  apply monoOn_of_hasDeriv_nonneg
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs => hd s (Ioo_subset_Icc_self hs))
  intro s hs
  have hsf : s∈Icc 0 frameCap := ⟨by linarith [hθ.1,hs.1],hs.2.le⟩
  have hx : s-θ∈Icc 0 frameCap :=
    ⟨by linarith [hs.1],by linarith [hs.2,hθ.1]⟩
  have hg := high_gain_derivative_lower hθ hsf
  have hu := OrdinarySlope.positive_derivative_whole hp.1 hp.2.1 hqp hx
  linarith [hp.2.2.2.2]

theorem high_equal_le_positive_surplus {a z s : ℝ}
    (hθ : a+z∈Icc (1/6:ℝ) (7/10)) (hz : z∈Icc 0 (a+z))
    (hs : s∈Icc (a+z) frameCap) (i : Fin 3) :
    Explicit.fullBaseline .high a z (a+z)≤Explicit.fullBaseline .high a z s+
      Explicit.U .high (a+z) z i (s-(a+z)) := by
  have hf := Certificate.family_frame_domain .high (r74_high hθ)
  have hsf : s∈Icc 0 frameCap := ⟨hf.1.trans hs.1,hs.2⟩
  have hh := positive_surplus_mono hθ hz i ⟨le_rfl,hf.2⟩ hs hs.1
  simp only [sub_self,Explicit.U,U_zero,add_zero] at hh
  rw [full_gain_identity .high a z hf,full_gain_identity .high a z hsf]
  dsimp only [Explicit.U]
  linarith

theorem pure_at_original {a z s : ℝ} (hs : s∈Icc 0 frameCap) (i : Fin 3) :
    NegativeAPositiveTD.SecantCoordinate.pure (Explicit.fullBaseline .high a z 0) 1
      (Explicit.c .high (a+z)) (Explicit.p .high (a+z) z i)
      (Explicit.q .high (a+z) z i) (a+z) (Real.tan s)=
      Explicit.fullBaseline .high a z s+Explicit.V .high (a+z) z i (a+z-s) := by
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  have hnorm := NegativeAPositiveTD.SecantCoordinate.normalized_arctan (Explicit.c .high (a+z)) (Real.tan s)
  rw [NegativeAPositiveTD.SecantCoordinate.arctan_tan hs] at hnorm
  have hg : SecantNormCurvature.normalized R (Explicit.c .high (a+z)) s=
      secantGain qCap (Explicit.c .high (a+z)) s := by
    rw [secantGain_eq_secant_expression qCap (Explicit.c .high (a+z)) hc]
    dsimp [SecantNormCurvature.normalized,SecantNormCurvature.secant,
      SecantNormCurvature.supportNorm]
    rw [add_comm ((Explicit.c .high (a+z))^2) ((1/Real.cos s)^2),
      add_comm ((Explicit.c .high (a+z))^2) 1]
    ring
  dsimp [NegativeAPositiveTD.SecantCoordinate.pure,Explicit.V]
  rw [NegativeAPositiveTD.SecantCoordinate.arctan_tan hs,←hnorm,hg,full_gain_identity .high a z hs]
  ring

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.HighSecant
end
end
end
