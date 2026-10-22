module

public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveBT3DEndpointBounds

/-!
# Strict sorted-D endpoint positivity at c=1 and c=1.1642

Uncompiled transcription of the endpoint note's radical comparisons.
The full-circle comparison is used on its two certified domains; the
remaining c=1 domain uses the proved tangent-zero support formula.
These endpoints are independent of the later signed-D minorant.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveBT3.DEndpoint
open Candidate Secondary Polynomial PositiveAngularEnvelope OrdinaryAngleConcavity
open PositiveTD.Certificate (S9 S11 C10 C12 taylor_bounds)

theorem phi_lower : (phiLower:ℝ)≤Real.cos frameCap+Real.sin frameCap := by
  have hh := taylor_bounds (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
  rw [phiLower,Rat.cast_add,← rational_aeval,← rational_aeval]
  change aeval frameCap C10+aeval frameCap S11≤_
  linarith [hh.2.2.2.2.1,hh.2.1]

theorem full_lower (e : End) {n : ℝ} (hn : n∈Icc 0 frameCap) :
    (constant e:ℝ)-R*Real.sqrt (aeval n (P e))+R*Real.sqrt (aeval n H)≤
      D (coefficient e:ℝ) frameCap (-n)+slope*frameCap-vstar n := by
  have hc := coefficient_domain e
  have hR : 0≤R := Real.sqrt_nonneg qCap
  have hnpoly := norm_polynomial_bounds e hn
  have hnormP := mul_le_mul_of_nonneg_left hnpoly.2.2.1 hR
  have hnormH := mul_le_mul_of_nonneg_left hnpoly.2.2.2 hR
  have hphi := mul_le_mul_of_nonneg_left phi_lower (by linarith [hc.1] : 0≤(coefficient e:ℝ))
  have hd := mul_le_mul_of_nonneg_left radical_bounds.1.le
    (by linarith [hc.1] : 0≤1+(coefficient e:ℝ))
  have hzero := radical_bounds.2.2
  have hfull := fullD_lower (c:=(coefficient e:ℝ))
    (by norm_num [frameCap]) (by rw [abs_neg,abs_of_nonneg hn.1]; exact hn.2)
  rw [fullD_mixed (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) hn] at hfull
  have hcst : (constant e:ℝ)=
      (coefficient e:ℝ)*(phiLower:ℝ)+1+
        ((coefficient e:ℝ)+1)*((cLower:ℝ)-1/2)+slope*frameCap-(Tzero:ℝ) := by
    simp [constant,slope,h,frameCap]
  rw [hcst]
  dsimp [vstar,V]
  nlinarith

/-- The squared comparison does not require a sign on the isolated
polynomial difference Q(P-H)-A². -/
theorem radical_gap_positive {A P H : ℝ} (hA : 0<A) (hP : 0≤P) (hH : 0<H)
    (hZ : 0<4*A^2*qCap*H-(qCap*(P-H)-A^2)^2) :
    0<A-R*Real.sqrt P+R*Real.sqrt H := by
  have hR : 0<R := by linarith [radius_bounds.1]
  have hX : 0≤R*Real.sqrt P := mul_nonneg hR.le (Real.sqrt_nonneg _)
  have hY : 0<R*Real.sqrt H := mul_pos hR (Real.sqrt_pos.mpr hH)
  have hX2 : (R*Real.sqrt P)^2=qCap*P := by rw [mul_pow,radius_sq,Real.sq_sqrt hP]
  have hY2 : (R*Real.sqrt H)^2=qCap*H := by rw [mul_pow,radius_sq,Real.sq_sqrt hH.le]
  have hright : 0≤2*A*(R*Real.sqrt H) := by positivity
  have hright2 : (2*A*(R*Real.sqrt H))^2=4*A^2*qCap*H := by
    rw [mul_pow,mul_pow,hY2]
    ring
  have hmiddle : qCap*(P-H)-A^2<2*A*(R*Real.sqrt H) := by
    by_contra hh
    have hs := pow_le_pow_left₀ hright (le_of_not_gt hh) 2
    nlinarith only [hs,hright2,hZ]
  have hsum : 0≤A+R*Real.sqrt H := by linarith
  have hcross : R*Real.sqrt P<A+R*Real.sqrt H := by
    by_contra hh
    have hs := pow_le_pow_left₀ hsum (le_of_not_gt hh) 2
    nlinarith only [hs,hX2,hY2,hmiddle]
  linarith

theorem axis_gap_positive {A H : ℝ} (hH : 0<H) (hY : 0<qCap*H-A^2) :
    0<A+R*Real.sqrt H := by
  have hR : 0<R := by linarith [radius_bounds.1]
  have hroot : 0<R*Real.sqrt H := mul_pos hR (Real.sqrt_pos.mpr hH)
  have hsquare : (R*Real.sqrt H)^2=qCap*H := by
    rw [mul_pow,radius_sq,Real.sq_sqrt hH.le]
  by_contra hh
  have hle : R*Real.sqrt H≤-A := by linarith
  have hpow := pow_le_pow_left₀ hroot.le hle 2
  nlinarith

theorem full_certificate_positive (e : End) {n : ℝ}
    (hn : n∈Icc 0 frameCap) (hZ : 0<aeval n (Z e)) :
    0<D (coefficient e:ℝ) frameCap (-n)+slope*frameCap-vstar n := by
  have hA : (0:ℝ)<(constant e:ℝ) := by
    have hh : (32/25:ℝ)<(constant e:ℝ) := by exact_mod_cast positive_constants e
    linarith
  have hpoly := norm_polynomial_bounds e hn
  have hZ' : 0<4*(constant e:ℝ)^2*qCap*aeval n H-
      (qCap*(aeval n (P e)-aeval n H)-(constant e:ℝ)^2)^2 := by
    simpa [Z,Q,qCap] using hZ
  exact (radical_gap_positive hA hpoly.1 (by linarith [hpoly.2.1]) hZ').trans_le
    (full_lower e hn)

theorem axis_identity {n : ℝ} (hn : n∈Icc (3/8:ℝ) frameCap) :
    D 1 frameCap (-n)+slope*frameCap-vstar n=
      (Real.cos frameCap+Real.sin frameCap-1)/2-axial*Real.sin frameCap+
      2*diagonal+slope*frameCap+1/2-R*pairNorm K 1 0-
      (axial+1/2)*Real.cos n+(1/2)*Real.sin n+R*pairNorm K 1 (-n) := by
  have hn0 : n∈Icc 0 frameCap := ⟨by linarith [hn.1],hn.2⟩
  rw [D,axis_support hn,edgeWidth_positive_formula
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap]),edgeWidth_negative_formula hn0]
  simp only [forceA,Real.cos_neg,one_mul]
  dsimp [vstar,V]
  ring

theorem axis_lower {n : ℝ} (hn : n∈Icc (3/8:ℝ) frameCap) :
    aeval n axisA+R*Real.sqrt (aeval n H)≤
      D 1 frameCap (-n)+slope*frameCap-vstar n := by
  have hn0 : n∈Icc 0 frameCap := ⟨by linarith [hn.1],hn.2⟩
  have hh := taylor_bounds (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
  have hnT := taylor_bounds hn0
  have hR : 0≤R := Real.sqrt_nonneg qCap
  have hnorm := mul_le_mul_of_nonneg_left (norm_polynomial_bounds .one hn0).2.2.2 hR
  have hsinH := (transport_trig
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap])).2.2.1
  have hcosN : 0≤Real.cos n := by linarith [(transport_trig hn0).1]
  have haSin := mul_le_mul_of_nonneg_right radical_bounds.2.1.le hsinH
  have hSin := mul_le_mul_of_nonneg_left hh.2.2.1
    (show 0≤(aUpper:ℝ) by norm_num [aUpper])
  have haCos := mul_le_mul_of_nonneg_right radical_bounds.2.1.le hcosN
  have hCos := mul_le_mul_of_nonneg_left hnT.2.2.2.2.2
    (show 0≤(aUpper:ℝ)+1/2 by norm_num [aUpper])
  have heval : aeval n axisA=(axisConstant:ℝ)-
      ((aUpper:ℝ)+1/2)*aeval n C12+(1/2)*aeval n S11 := by simp [axisA]
  have hconst : (axisConstant:ℝ)=((phiLower:ℝ)-1)/2-
      (aUpper:ℝ)*aeval frameCap S9+2*(cLower:ℝ)+slope*frameCap+1/2-(Tzero:ℝ) := by
    rw [axisConstant]
    push_cast
    rw [← rational_aeval]
    rfl
  rw [heval,hconst,axis_identity hn]
  nlinarith [phi_lower,radical_bounds.1,radical_bounds.2.2,hnT.2.1]

theorem axis_certificate_positive {n : ℝ} (hn : n∈Icc (3/8:ℝ) frameCap) :
    0<D 1 frameCap (-n)+slope*frameCap-vstar n := by
  have hn0 : n∈Icc 0 frameCap := ⟨by linarith [hn.1],hn.2⟩
  have hpoly := axis_positive hn
  have hH := (norm_polynomial_bounds .one hn0).2.1
  have hY : 0<qCap*aeval n H-(aeval n axisA)^2 := by
    have hh : 0<aeval n Y := by linarith
    simpa [Y,Q,qCap] using hh
  exact (axis_gap_positive (by linarith) hY).trans_le (axis_lower hn)

/-- The two intrinsic endpoints of the c-concavity argument, including
the complete closed n interval and the tangent-zero transition. -/
theorem endpoint (e : End) {n : ℝ} (hn : n∈Icc 0 frameCap) :
    0<D (coefficient e:ℝ) frameCap (-n)+slope*frameCap-vstar n := by
  cases e
  · by_cases hcut : n≤3/8
    · exact full_certificate_positive .one hn (by linarith [one_positive ⟨hn.1,hcut⟩])
    · exact axis_certificate_positive ⟨(le_of_not_ge hcut),hn.2⟩
  · exact full_certificate_positive .upper hn (by linarith [upper_positive hn])

end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveBT3.DEndpoint
