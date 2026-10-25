module

public import SquaresInCircles.Eight.Owners.GA.Positive.BT3DEnvelopeGeometry
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3DMixedEnvelope
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3Data

/-!
# Eight squares: the wider D minorant at a sorted outer point

The support of the forces at a sorted point `P` of the disk with `P.y ≤ 0` is at most
`sortedSupport` (`actual_support`). A negative first force in the reversed mixed quadrant is
treated by the diagonal support inequality, which only requires a nonnegative total force. The
other three quadrants use their positive forces.
-/

section
/-!
## Signed D support through coefficient seven fifths

The
constants are k*=.6692, alpha=.65 and C*=1.4. Both force components
are positive in the forward and equal-sign quadrants. The reversed
mixed quadrant is handled directly by its diagonal support formula.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.SortedDSevenFifths
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PositiveBT3

abbrev K : ℝ := 1673/2500
abbrev Cmax : ℝ := 7/5
abbrev slope : ℝ := 13/20
def vstar (n : ℝ) : ℝ := V R K 1 n

theorem forward_force_positive {c t n : ℝ} (hc : c∈Icc 1 Cmax)
    (ht : t∈Icc 0 frameCap) (hn : n∈Icc 0 frameCap) :
    0<forceA c t (-n) ∧ 0<forceB c t (-n) := by
  have ht' := transport_trig ht
  have hn' := transport_trig hn
  have hs := mul_nonneg (by linarith [hc.1] : 0≤c) ht'.2.2.1
  have hcos := mul_le_mul_of_nonneg_right hc.1 (by linarith [ht'.1] : 0≤Real.cos t)
  dsimp [forceA,forceB]
  rw [Real.cos_neg,Real.sin_neg]
  constructor <;> linarith [ht'.1,hn'.1,hn'.2.2.2.1]

theorem positive_force_positive {c x y : ℝ} (hc : c∈Icc 1 Cmax)
    (hx : x∈Icc 0 frameCap) (hy : y∈Icc 0 frameCap) :
    0<forceA c x y ∧ 0<forceB c x y := by
  have hx' := transport_trig hx
  have hy' := transport_trig hy
  have hs := mul_nonneg (by linarith [hc.1] : 0≤c) hx'.2.2.1
  have hcos := mul_pos (by linarith [hc.1] : 0<c) (by linarith [hx'.1] : 0<Real.cos x)
  dsimp [forceA,forceB]
  constructor <;> linarith [hy'.1,hy'.2.2.1]

theorem negative_force_positive {c n t : ℝ} (hc : c∈Icc 1 Cmax)
    (hn : n∈Icc 0 frameCap) (ht : t∈Icc 0 n) :
    0<forceA c (-t) (-(n-t)) ∧ 0<forceB c (-t) (-(n-t)) := by
  have ht' : t∈Icc 0 frameCap := ⟨ht.1,ht.2.trans hn.2⟩
  have hy : n-t∈Icc 0 frameCap := ⟨by linarith [ht.2],by linarith [ht.1,hn.2]⟩
  have hnt := transport_trig hn
  have htt := transport_trig ht'
  have hyt := transport_trig hy
  have hcos := mul_le_mul_of_nonneg_right hc.1 (by linarith [htt.1] : 0≤Real.cos t)
  have hlast : 0<1-c*Real.sin n := by
    have hm := mul_le_mul_of_nonneg_right hc.2 hnt.2.2.1
    dsimp [Cmax] at hm
    linarith [hnt.2.2.2.1]
  have hf : 0<Real.cos (n-t)-c*Real.sin t := by
    by_cases ht0 : t=0
    · simpa [ht0] using (show 0<Real.cos n by linarith [hnt.1])
    have hst : 0<Real.sin t := Real.sin_pos_of_pos_of_lt_pi
      (lt_of_le_of_ne ht.1 (Ne.symm ht0))
      (by dsimp [frameCap] at ht'; linarith [ht'.2,Real.pi_gt_three])
    have hsn : 0<Real.sin n := Real.sin_pos_of_pos_of_lt_pi
      (by linarith [ht.2,lt_of_le_of_ne ht.1 (Ne.symm ht0)])
      (by dsimp [frameCap] at hn; linarith [hn.2,Real.pi_gt_three])
    have hid : Real.sin n*(Real.cos (n-t)-c*Real.sin t)=
        Real.cos n*Real.sin (n-t)+(1-c*Real.sin n)*Real.sin t := by
      rw [Real.cos_sub,Real.sin_sub]
      nlinarith [congrArg (fun z : ℝ => z*Real.sin t) (Real.sin_sq_add_cos_sq n)]
    have hfirst := mul_nonneg (by linarith [hnt.1] : 0≤Real.cos n) hyt.2.2.1
    have hsecond := mul_pos hlast hst
    have hprod : 0<Real.sin n*(Real.cos (n-t)-c*Real.sin t) := by linarith
    by_contra hh
    have hm := mul_nonpos_of_nonneg_of_nonpos hsn.le (le_of_not_gt hh)
    linarith
  dsimp [forceA,forceB]
  simp only [Real.sin_neg,Real.cos_neg]
  exact ⟨by linarith,by linarith [htt.1,hyt.2.2.2.1]⟩

theorem one_angle_lower {c n : ℝ} (hc : c∈Icc 1 Cmax)
    (hn : n∈Icc 0 frameCap) : vstar n≤D c 0 (-n) := by
  have hp := forward_force_positive (t:=0) hc (by norm_num [frameCap]) hn
  have hsup := sortedSupport_le_clipped hp.1.le hp.2.le
  have hminor := PositiveTD.negative_D_support_minorant
    (k:=K) (c:=c) (by norm_num [K])
    (by constructor <;> dsimp [Cmax,K] at hc ⊢ <;> linarith [hc.1,hc.2]) hn
  have h1c : clippedSupport 1 c=(1+c)*GlobalGA.Secondary.diagonal := by
    simp only [clippedSupport,diagonalSupport,hc.1,ite_true]
  dsimp only [PositiveBT3.D,vstar,PositiveTD.dSupportIncrement] at ⊢ hminor
  simp only [forceA,forceB,Real.sin_zero,Real.cos_zero,mul_zero,zero_add,mul_one,
    edgeWidth_zero,sub_self] at hsup ⊢
  rw [h1c] at hminor
  linarith

end SquaresInCircles.Eight.GlobalGA.SortedDSevenFifths
end
end
end

section
/-!
## The additional intrinsic D endpoint at c=7/5

Its single degree
eighteen certificate is the prescribed coefficient norm on [0,.7].
The c=1 endpoint is the unchanged earlier theorem. Both signs of the
isolated radical difference are covered by the squared certificate.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.GlobalGA.SortedDSevenFifths.DEndpoint
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PositiveBT3
open WholeIntervalPolynomial
open PositiveTD.Certificate (S9 S11 C10 C12 taylor_bounds)

abbrev End := PositiveBT3.DEndpoint.End
def coefficient : End→ℚ | .one=>1 | .upper=>7/5
abbrev Q : ℚ := 9789/2500
abbrev h : ℚ := 7/10
abbrev cLower := PositiveBT3.DEndpoint.cLower
abbrev Tzero := PositiveBT3.DEndpoint.Tzero
abbrev phiLower := PositiveBT3.DEndpoint.phiLower
abbrev H := PositiveBT3.DEndpoint.H
def constant : ℚ := (7/5)*phiLower+1+(7/5+1)*(cLower-1/2)+(13/20)*h-Tzero
def P : ℚ[X] := C (1+(7/5)^2)+C (2*(7/5))*S9.comp (C h-X)
def Z : ℚ[X] := C (4*constant^2*Q)*H-(C Q*(P-H)-C (constant^2))^2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem constant_positive : (1253/625:ℚ)<constant := by
  norm_num [constant,phiLower,PositiveBT3.DEndpoint.phiLower,C10,PositiveTD.Certificate.C4,
    S11,S9,PositiveTD.Certificate.S5,h,PositiveBT3.DEndpoint.h,cLower,
    PositiveBT3.DEndpoint.cLower,Tzero,PositiveBT3.DEndpoint.Tzero]

/-! ### Kernel certificate for `Z`

`Z` is represented as a scaled integer coefficient list
(`WholeIntervalPolynomial.Certificate`), mirroring its definition. -/

open WholeIntervalPolynomial.Certificate in
/-- The degree-nine sine polynomial composed with a represented polynomial. -/
private def r45_S9of (v : Scaled) : Scaled :=
  (((v.sub ((Scaled.const (1/6)).mul (v.pow 3))).add
    ((Scaled.const (1/120)).mul (v.pow 5))).sub
    ((Scaled.const (1/5040)).mul (v.pow 7))).add
    ((Scaled.const (1/362880)).mul (v.pow 9))

open WholeIntervalPolynomial.Certificate in
private theorem r45_rep_S9of {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) :
    (r45_S9of v).Rep (S9.comp q) := by
  have e : S9.comp q=q-C (1/6)*q^3+C (1/120)*q^5-C (1/5040)*q^7+C (1/362880)*q^9 := by
    simp only [S9,PositiveTD.Certificate.S5,sub_comp,add_comp,mul_comp,C_comp,X_comp,
      pow_comp]
  rw [e]
  exact (((hv.sub ((Scaled.rep_const _).mul (hv.pow 3))).add
    ((Scaled.rep_const _).mul (hv.pow 5))).sub
    ((Scaled.rep_const _).mul (hv.pow 7))).add
    ((Scaled.rep_const _).mul (hv.pow 9))

open WholeIntervalPolynomial.Certificate in
private theorem r45_rep_S9 : (r45_S9of Scaled.var).Rep S9 := by
  simpa only [comp_X] using r45_rep_S9of Scaled.rep_var

open WholeIntervalPolynomial.Certificate in
private def r45_HS : Scaled :=
  (Scaled.const (1+PositiveBT3.DEndpoint.kstar^2)).sub
    ((Scaled.const (2*PositiveBT3.DEndpoint.kstar)).mul (r45_S9of Scaled.var))

open WholeIntervalPolynomial.Certificate in
private theorem r45_rep_H : r45_HS.Rep H :=
  (Scaled.rep_const _).sub ((Scaled.rep_const _).mul r45_rep_S9)

open WholeIntervalPolynomial.Certificate in
private def r45_PS : Scaled :=
  (Scaled.const (1+(7/5)^2)).add
    ((Scaled.const (2*(7/5))).mul (r45_S9of ((Scaled.const h).sub Scaled.var)))

open WholeIntervalPolynomial.Certificate in
private theorem r45_rep_P : r45_PS.Rep P :=
  (Scaled.rep_const _).add ((Scaled.rep_const _).mul
    (r45_rep_S9of ((Scaled.rep_const _).sub Scaled.rep_var)))

open WholeIntervalPolynomial.Certificate in
private def r45_ZS (k : ℚ) : Scaled :=
  ((Scaled.const (4*k^2*Q)).mul r45_HS).sub
    ((((Scaled.const Q).mul (r45_PS.sub r45_HS)).sub (Scaled.const (k^2))).pow 2)

open WholeIntervalPolynomial.Certificate in
private theorem r45_rep_Z {k : ℚ} (hk : constant=k) : (r45_ZS k).Rep Z := by
  rw [Z,hk]
  exact ((Scaled.rep_const _).mul r45_rep_H).sub
    ((((Scaled.rep_const _).mul (r45_rep_P.sub r45_rep_H)).sub
      (Scaled.rep_const _)).pow 2)

private theorem r45_constant : constant=5716104265110662867/2851200000000000000 := by
  norm_num [constant,phiLower,PositiveBT3.DEndpoint.phiLower,C10,PositiveTD.Certificate.C4,
    S11,S9,PositiveTD.Certificate.S5,h,PositiveBT3.DEndpoint.h,cLower,
    PositiveBT3.DEndpoint.cLower,Tzero,PositiveBT3.DEndpoint.Tzero]

open WholeIntervalPolynomial.Certificate in
private theorem r45_rep_centered :
    ((r45_ZS (5716104265110662867/2851200000000000000)).center 7 20 1 1).Rep
      (centered 0 h Z) :=
  (r45_rep_Z r45_constant).centered 7 20 1 1 (by norm_num) (by norm_num [h])
    (by norm_num [h])

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem expansion_certificate : centered 0 h Z=expansion 18 (centered 0 h Z) :=
  r45_rep_centered.eq_expansion (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem reserve_certificate : (317/200:ℚ)<lowerOn 18 0 h Z := by
  rw [Certificate.lowerOn_eq_of_rep r45_rep_centered (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem polynomial_positive {n : ℝ} (hn : n∈Icc 0 frameCap) : (317/200:ℝ)<aeval n Z := by
  have hn' : n∈Icc ((0:ℚ):ℝ) ((h:ℚ):ℝ) := by
    norm_num [h]
    exact hn
  have hh := positive_on_interval (by norm_num [h]) expansion_certificate reserve_certificate hn'
  norm_num at hh
  exact hh

theorem norm_bounds {n : ℝ} (hn : n∈Icc 0 frameCap) :
    0≤aeval n P ∧ (29/50:ℝ)<aeval n H ∧
    pairNorm 1 Cmax (frameCap-n)≤Real.sqrt (aeval n P) ∧
    Real.sqrt (aeval n H)≤pairNorm K 1 (-n) := by
  have hother : frameCap-n∈Icc 0 frameCap := ⟨by linarith [hn.2],by linarith [hn.1]⟩
  have hs := PositiveBT3.DEndpoint.sine9_range hother
  have ht := (taylor_bounds hother).2.2.1
  have hH := PositiveBT3.DEndpoint.norm_polynomial_bounds .one hn
  have hP : aeval n P=1+Cmax^2+2*Cmax*aeval (frameCap-n) S9 := by
    simp [P,aeval_comp,h,frameCap,Cmax]
  have hP0 : 0≤aeval n P := by
    rw [hP]
    have := mul_nonneg (show 0≤2*Cmax by norm_num [Cmax]) hs.1
    nlinarith [sq_nonneg Cmax]
  refine ⟨hP0,hH.2.1,?_,hH.2.2.2⟩
  apply Real.sqrt_le_sqrt
  rw [hP]
  have hm := mul_le_mul_of_nonneg_left ht (by norm_num [Cmax] : (0:ℝ)≤2*Cmax)
  linarith

theorem full_lower {n : ℝ} (hn : n∈Icc 0 frameCap) :
    (constant:ℝ)-R*Real.sqrt (aeval n P)+R*Real.sqrt (aeval n H)≤
      D Cmax frameCap (-n)+slope*frameCap-vstar n := by
  have hR : 0≤R := Real.sqrt_nonneg qCap
  have hb := norm_bounds hn
  have hnormP := mul_le_mul_of_nonneg_left hb.2.2.1 hR
  have hnormH := mul_le_mul_of_nonneg_left hb.2.2.2 hR
  have hphi := mul_le_mul_of_nonneg_left PositiveBT3.DEndpoint.phi_lower
    (by norm_num [Cmax] : (0:ℝ)≤Cmax)
  have hd := mul_le_mul_of_nonneg_left PositiveBT3.DEndpoint.radical_bounds.1.le
    (by norm_num [Cmax] : (0:ℝ)≤1+Cmax)
  have hzero := PositiveBT3.DEndpoint.radical_bounds.2.2
  have hfull := fullD_lower (c:=Cmax) (x:=frameCap) (y:=-n)
    (by norm_num [frameCap]) (by rw [abs_neg,abs_of_nonneg hn.1]; exact hn.2)
  rw [fullD_mixed (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) hn] at hfull
  have hcst : (constant:ℝ)=Cmax*(phiLower:ℝ)+1+
      (Cmax+1)*((cLower:ℝ)-1/2)+slope*frameCap-(Tzero:ℝ) := by
    simp [constant,Cmax,slope,h,frameCap]
  rw [hcst]
  dsimp only [vstar,V]
  simp only [phiLower,cLower,Tzero,K,PositiveBT3.K,Cmax] at hphi hd hzero hfull hnormH hnormP ⊢
  linarith

theorem upper_endpoint {n : ℝ} (hn : n∈Icc 0 frameCap) :
    0<D Cmax frameCap (-n)+slope*frameCap-vstar n := by
  have hb := norm_bounds hn
  have hA : (0:ℝ)<(constant:ℝ) := by
    have hh := (Rat.cast_lt (K:=ℝ)).mpr constant_positive
    norm_num at hh
    linarith
  have hZ : 0<4*(constant:ℝ)^2*qCap*aeval n H-
      (qCap*(aeval n P-aeval n H)-(constant:ℝ)^2)^2 := by
    have hh : 0<aeval n Z := by linarith [polynomial_positive hn]
    simpa [Z,Q,qCap] using hh
  exact (PositiveBT3.DEndpoint.radical_gap_positive hA hb.1
    (by linarith [hb.2.1]) hZ).trans_le (full_lower hn)

theorem endpoint (e : End) {n : ℝ} (hn : n∈Icc 0 frameCap) :
    0<D (coefficient e:ℝ) frameCap (-n)+slope*frameCap-vstar n := by
  cases e
  · simpa [coefficient,PositiveBT3.DEndpoint.coefficient,vstar,PositiveBT3.vstar,K,slope] using
      PositiveBT3.DEndpoint.endpoint .one hn
  · simpa [coefficient,Cmax] using upper_endpoint hn

end SquaresInCircles.Eight.GlobalGA.SortedDSevenFifths.DEndpoint
end
end
end

section
/-!
## The signed diagonal charge and the interpolation of the wider D endpoint

The constants are `alpha = .65`, `k* = .6692` and `C* = 1.4`; the negative initial slope is below
`1.101`. The interpolation of the support (`D_weight_concave`) is used only in the forward mixed
quadrant, where both forces are strictly positive.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.SortedDSevenFifths
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PositiveBT3
open PairNormCalculus OrdinaryNegativeSlope

/-- The sorted support, including its tangent-zero branch, is convex along the interpolation of
the coefficient `c` between `1` and `Cmax`. -/
theorem D_weight_concave {c x n : ℝ} (hc : c∈Icc 1 Cmax)
    (hx : x∈Icc 0 frameCap) (hn : n∈Icc 0 frameCap) :
    ((Cmax-c)/(Cmax-1))*D 1 x (-n)+((c-1)/(Cmax-1))*D Cmax x (-n)≤D c x (-n) := by
  have hp := forward_force_positive hc hx hn
  obtain ⟨a,b,ha,hb,hs,hcircle,he⟩ := sortedSupport_attained hp.1 hp.2
  have hp1 := forward_force_positive (show (1:ℝ)∈Icc 1 Cmax by norm_num [Cmax]) hx hn
  have hpC := forward_force_positive (show Cmax∈Icc 1 Cmax by norm_num [Cmax]) hx hn
  have h1 := raw_sorted_support ha hb hs hcircle.le hp1.1.le hp1.2.le
  have hC := raw_sorted_support ha hb hs hcircle.le hpC.1.le hpC.2.le
  have hden : 0<Cmax-1 := by norm_num [Cmax]
  have hα : 0≤(Cmax-c)/(Cmax-1) := div_nonneg (sub_nonneg.mpr hc.2) hden.le
  have hβ : 0≤(c-1)/(Cmax-1) := div_nonneg (sub_nonneg.mpr hc.1) hden.le
  have hh1 := mul_le_mul_of_nonneg_left h1 hα
  have hhC := mul_le_mul_of_nonneg_left hC hβ
  have hbary : (Cmax-c)/(Cmax-1)+(c-1)/(Cmax-1)=1 := by field_simp [hden.ne']; ring
  have hcoef : (Cmax-c)/(Cmax-1)+((c-1)/(Cmax-1))*Cmax=c := by
    field_simp [hden.ne']; ring
  dsimp only [PositiveBT3.D]
  rw [he]
  have e1 := congrArg (fun z : ℝ => z*(edgeWidth (-n)-1+GlobalGA.Secondary.diagonal)) hbary
  have e2 := congrArg (fun z : ℝ => z*(edgeWidth x-1+GlobalGA.Secondary.diagonal)) hcoef
  have e3 := congrArg (fun z : ℝ => z*(Real.cos (-n)*a+Real.sin (-n)*b)) hbary
  have e4 := congrArg (fun z : ℝ => z*(Real.sin x*a+Real.cos x*b)) hcoef
  simp only [forceA,forceB] at hh1 hhC ⊢
  linarith

theorem mixed_far_endpoint {c n : ℝ} (hc : c∈Icc 1 Cmax)
    (hn : n∈Icc 0 frameCap) :
    0<D c frameCap (-n)+slope*frameCap-vstar n := by
  have h1 := DEndpoint.endpoint .one hn
  have hC := DEndpoint.endpoint .upper hn
  have e1 : ((DEndpoint.coefficient .one:ℚ):ℝ)=1 := by norm_num [DEndpoint.coefficient]
  have eC : ((DEndpoint.coefficient .upper:ℚ):ℝ)=Cmax := by
    norm_num [DEndpoint.coefficient,Cmax]
  rw [e1] at h1
  rw [eC] at hC
  have hw := D_weight_concave (x:=frameCap) hc (by norm_num [frameCap]) hn
  have hden : 0<Cmax-1 := by norm_num [Cmax]
  have hα : 0≤(Cmax-c)/(Cmax-1) := div_nonneg (sub_nonneg.mpr hc.2) hden.le
  have hβ : 0≤(c-1)/(Cmax-1) := div_nonneg (sub_nonneg.mpr hc.1) hden.le
  have hs : (Cmax-c)/(Cmax-1)+(c-1)/(Cmax-1)=1 := by field_simp [hden.ne']; ring
  have hpos : 0<((Cmax-c)/(Cmax-1))*(D 1 frameCap (-n)+slope*frameCap-vstar n)+
      ((c-1)/(Cmax-1))*(D Cmax frameCap (-n)+slope*frameCap-vstar n) := by
    by_cases hα0 : (Cmax-c)/(Cmax-1)=0
    · have hβ1 : (c-1)/(Cmax-1)=1 := by linarith
      simpa [hα0,hβ1] using hC
    · exact add_pos_of_pos_of_nonneg
        (mul_pos (lt_of_le_of_ne hα (Ne.symm hα0)) h1) (mul_nonneg hβ hC.le)
  have hid : ((Cmax-c)/(Cmax-1))*(D 1 frameCap (-n)+slope*frameCap-vstar n)+
      ((c-1)/(Cmax-1))*(D Cmax frameCap (-n)+slope*frameCap-vstar n)=
      ((Cmax-c)/(Cmax-1))*D 1 frameCap (-n)+((c-1)/(Cmax-1))*D Cmax frameCap (-n)+
      ((Cmax-c)/(Cmax-1)+(c-1)/(Cmax-1))*(slope*frameCap-vstar n) := by ring
  rw [hs,one_mul] at hid
  generalize (Cmax-c)/(Cmax-1)=α at hw hpos hid
  generalize (c-1)/(Cmax-1)=β at hw hpos hid
  generalize slope*frameCap=S at hpos hid ⊢
  linarith

theorem vstar_slope_zero : Vd R K 1 0<1101/1000 := by
  have hN := pairNorm_pos (p:=K) (q:=1) (t:=0) (by norm_num [K])
    (by norm_num) (by norm_num [frameCap])
  have hN2 := pairNorm_sq (p:=K) (q:=1) (t:=0) (by norm_num [K])
    (by norm_num) (by norm_num [frameCap])
  have hR2 : (R*K)^2=qCap*K^2 := by rw [mul_pow,radius_sq]
  have hs : (R*K)^2<((1101/1000)*pairNorm K 1 0)^2 := by
    norm_num [pairEnergy,pairProduct,K] at hN2
    norm_num [qCap,K] at hR2 ⊢
    nlinarith
  have hc : R*K<(1101/1000)*pairNorm K 1 0 := by
    nlinarith [Real.sqrt_nonneg qCap]
  have he : Vd R K 1 0=R*K/pairNorm K 1 0 := by
    simp [Vd,mixedNDerivative,normD1,pairProduct]
    ring
  rw [he]
  exact (div_lt_iff₀ hN).2 hc

theorem vstar_linear_upper {n : ℝ} (hn : n∈Icc 0 frameCap) :
    vstar n≤(1101/1000)*n := by
  have hh := V_tangent_zero (p:=K) (q:=1) (by norm_num [K])
    (by norm_num [K]) (by norm_num [K]) hn
  have hm := mul_le_mul_of_nonneg_right vstar_slope_zero.le hn.1
  exact hh.trans hm

theorem diagonal_increment_lower {w x : ℝ} (hw : w∈Icc 1 Cmax)
    (hx : |x|≤frameCap) :
    -slope*positivePart x+(1327/1000)*negativePart x≤diagonalIncrement w x := by
  by_cases hx0 : 0≤x
  · have ht : x∈Icc 0 frameCap := ⟨hx0,by simpa [abs_of_nonneg hx0] using hx⟩
    have hphi : Real.sin x+Real.cos x-1≤x := by
      linarith [Real.sin_le hx0,Real.cos_le_one x]
    have hwd : w*(GlobalGA.Secondary.diagonal-1/2)≤ slope := by
      have hm := mul_le_mul_of_nonneg_right hw.2
        (by linarith [diagonal_bounds.1] : 0≤GlobalGA.Secondary.diagonal-1/2)
      have hd := mul_lt_mul_of_pos_left
        (show GlobalGA.Secondary.diagonal-1/2<(2/5:ℝ) by linarith [diagonal_bounds.2])
        (show 0<Cmax by norm_num [Cmax])
      norm_num [slope,Cmax] at *
      linarith
    have hmul := mul_le_mul_of_nonneg_left hphi
      (mul_nonneg (show (0:ℝ)≤w by linarith [hw.1])
        (show 0≤GlobalGA.Secondary.diagonal-1/2 by linarith [diagonal_bounds.1]))
    have hsl := mul_le_mul_of_nonneg_right hwd hx0
    rw [diagonalIncrement,edgeWidth_positive_formula ht]
    simp only [positivePart,negativePart,max_eq_left hx0,
      max_eq_right (neg_nonpos.mpr hx0),mul_zero,add_zero]
    nlinarith
  · have hn : -x∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs x).trans hx⟩
    have hh := diagonal_negative_growth hn
    have hg : 0≤(GlobalGA.Secondary.diagonal+1/2)*Real.sin (-x)+(GlobalGA.Secondary.diagonal-1/2)*(1-Real.cos (-x)) := by
      nlinarith [hn.1]
    have hm := mul_le_mul_of_nonneg_right hw.1 hg
    have he : diagonalIncrement w x=
        w*((GlobalGA.Secondary.diagonal+1/2)*Real.sin (-x)+(GlobalGA.Secondary.diagonal-1/2)*(1-Real.cos (-x))) := by
      have hwidth := edgeWidth_negative_formula hn
      simp only [neg_neg] at hwidth
      rw [diagonalIncrement,hwidth,Real.sin_neg,Real.cos_neg]
      ring
    rw [he]
    simp only [positivePart,negativePart,max_eq_right (le_of_not_ge hx0),
      max_eq_left (show 0≤ -x by linarith),mul_zero,zero_add]
    linarith

/-- The diagonal expression is nonnegative on each whole orthant, so integrating it needs no
assumption that a path stays in one branch. -/
theorem diagonal_residual {c x y : ℝ} (hc : c∈Icc 1 Cmax)
    (hxy : SignedDomain x y) :
    0≤c*(edgeWidth x-1)+edgeWidth y-1+(1+c)*GlobalGA.Secondary.diagonal-
      diagonalSupport (forceA c x y) (forceB c x y)+
      slope*positiveTotal x y-vstar (negativeTotal x y) := by
  have hangle := signed_domain_angles hxy
  have hx := diagonal_increment_lower hc hangle.1
  have hy := diagonal_increment_lower
    (show (1:ℝ)∈Icc 1 Cmax by norm_num [Cmax]) hangle.2
  have hN : negativeTotal x y∈Icc 0 frameCap :=
    ⟨add_nonneg (negativePart_nonneg _) (negativePart_nonneg _),hxy.2⟩
  have hv := vstar_linear_upper hN
  have he : c*(edgeWidth x-1)+edgeWidth y-1+(1+c)*GlobalGA.Secondary.diagonal-
      diagonalSupport (forceA c x y) (forceB c x y)=
      diagonalIncrement c x+diagonalIncrement 1 y := by
    dsimp [diagonalSupport,forceA,forceB,diagonalIncrement]
    ring
  rw [he]
  have hh : 0≤diagonalIncrement c x+diagonalIncrement 1 y+
      slope*positiveTotal x y-vstar (negativeTotal x y) := by
    dsimp only [positiveTotal,negativeTotal] at hv hN ⊢
    dsimp only [SortedDSevenFifths.slope,PositiveBT3.slope] at hx hy ⊢
    linarith [hN.1]
  exact hh

end SquaresInCircles.Eight.GlobalGA.SortedDSevenFifths
end
end
end

section
/-!
## Both mixed-sign quadrants of the actual sorted-D support

The full-circle branch is strictly concave; the tangent-zero expression
decreases to its far endpoint.  Exact branch equality joins these bounds
to the independently proved diagonal and endpoint estimates.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.SortedDSevenFifths
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open PositiveBT3
open PairNormCalculus OrdinaryCurvatureBounds

theorem mixed_reverse_lower {c t n : ℝ} (hc : c∈Icc 1 Cmax)
    (ht : t∈Icc 0 frameCap) (hn : n∈Icc 0 frameCap) :
    -slope*t+vstar n≤D c (-n) t := by
  have hphi : 1≤Real.cos n+Real.sin n := CorrelatedSameBlock.one_le_phi hn
  have hs := (transport_trig ht).2.2.1
  have hm := mul_le_mul_of_nonneg_left hphi (by linarith [hc.1] : 0≤c)
  have he : forceA c (-n) t≤forceB c (-n) t := by
    dsimp [forceA,forceB]
    rw [Real.sin_neg,Real.cos_neg]
    nlinarith [Real.cos_le_one t,hc.1]
  have hh := diagonal_residual hc (mixed_domain ht hn).2
  dsimp only [PositiveBT3.D]
  rw [sortedSupport_diagonal he]
  simp only [positiveTotal,negativeTotal,positivePart,negativePart,
    max_eq_left ht.1,max_eq_left hn.1,max_eq_right (neg_nonpos.mpr ht.1),
    max_eq_right (neg_nonpos.mpr hn.1),neg_neg,zero_add,add_zero] at hh
  linarith

def mixedBase (c n t : ℝ) : ℝ :=
  c*(Real.cos t+Real.sin t-1)/2+(Real.cos n+Real.sin n-1)/2+
    (1+c)*GlobalGA.Secondary.diagonal+slope*t-vstar n

theorem mixed_base_identity {c t n : ℝ} (ht : t∈Icc 0 frameCap) (hn : n∈Icc 0 frameCap) :
    mixedBase c n t-sortedSupport (forceA c t (-n)) (forceB c t (-n))=
      D c t (-n)+slope*t-vstar n := by
  rw [PositiveBT3.D,edgeWidth_positive_formula ht,edgeWidth_negative_formula hn]
  dsimp only [mixedBase]
  ring

theorem mixed_full_identity (c n t : ℝ) :
    mixedBase c n t-fullSupport (forceA c t (-n)) (forceB c t (-n))=
      c*(Real.cos t+Real.sin t-1)+Real.cos n-1+(1+c)*(GlobalGA.Secondary.diagonal+1/2)-
      R*pairNorm 1 c (t-n)+slope*t-vstar n := by
  rw [fullSupport,force_norm]
  dsimp [mixedBase,forceA,forceB]
  rw [Real.sin_neg,Real.cos_neg]
  ring

theorem uniform_norm_curvature {c s : ℝ} (hc : c∈Icc 1 Cmax)
    (hs : |s|≤frameCap) : curvature R 1 c s<(189/200)*c := by
  have hc0 : 0<c := by linarith [hc.1]
  have hc2 : c≤2*(1:ℝ) := by norm_num [Cmax] at hc ⊢; linarith [hc.2]
  have hmon := curvature_monotone (R:=R) (p:=1) (q:=c)
    (Real.sqrt_nonneg _) (by norm_num) hc0
    (abs_le.mp hs) (show frameCap∈Icc (-frameCap) frameCap by norm_num [frameCap])
    ((le_abs_self s).trans hs)
  have htan := curvature_positive_upper (R:=R) (p:=1) (q:=c)
    (Real.sqrt_nonneg _) (by norm_num) hc.1 hc2
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
  have hconst := (curvature_constant_bounds (R:=R) (p:=1) (q:=c)
    (Real.sqrt_nonneg _) radius_sq.le (by norm_num) hc.1 hc2).2.2.2
  simp only [frameCap] at hmon htan hconst
  linarith

def mixedDerivative (c n t : ℝ) : ℝ :=
  c*(Real.cos t-Real.sin t)-R*normD1 1 c (t-n)+slope

theorem mixed_full_hasDerivAt {c n t : ℝ} (hc : c∈Icc 1 Cmax)
    (ht : t∈Icc 0 frameCap) (hn : n∈Icc 0 frameCap) :
    HasDerivAt (fun x => mixedBase c n x-
      fullSupport (forceA c x (-n)) (forceB c x (-n))) (mixedDerivative c n t) t := by
  have hnorm : HasDerivAt (fun x => pairNorm 1 c (x-n)) (normD1 1 c (t-n)) t :=
    HasDerivAt.comp_sub_const t n (pairNorm_hasDerivAt (p:=1) (q:=c) (by norm_num)
      (by linarith [hc.1]) (mixed_argument_bound ht hn))
  have h := (((((((Real.hasDerivAt_cos t).fun_add (Real.hasDerivAt_sin t)).sub_const 1).const_mul
    c).add_const (Real.cos n-1+(1+c)*(GlobalGA.Secondary.diagonal+1/2))).fun_sub
      (hnorm.const_mul R)).fun_add ((hasDerivAt_id' t).const_mul slope)).sub_const (vstar n)
  have he : (fun x => mixedBase c n x-
      fullSupport (forceA c x (-n)) (forceB c x (-n)))=fun x =>
      c*(Real.cos x+Real.sin x-1)+(Real.cos n-1+(1+c)*(GlobalGA.Secondary.diagonal+1/2))-
        R*pairNorm 1 c (x-n)+slope*x-vstar n := by
    funext x
    rw [mixed_full_identity]
    ring
  rw [he]
  exact h.congr_deriv (by dsimp only [mixedDerivative]; ring)

theorem mixed_derivative_hasDerivAt {c n t : ℝ} (hc : c∈Icc 1 Cmax)
    (ht : t∈Icc 0 frameCap) (hn : n∈Icc 0 frameCap) :
    HasDerivAt (mixedDerivative c n)
      (curvature R 1 c (t-n)-c*PositiveAngularEnvelope.phi t) t := by
  have hnorm : HasDerivAt (fun x => normD1 1 c (x-n)) (normD2 1 c (t-n)) t :=
    HasDerivAt.comp_sub_const t n (normD1_hasDerivAt (p:=1) (q:=c) (by norm_num)
      (by linarith [hc.1]) (mixed_argument_bound ht hn))
  have h := ((((Real.hasDerivAt_cos t).fun_sub (Real.hasDerivAt_sin t)).const_mul c).fun_sub
    (hnorm.const_mul R)).add_const slope
  show HasDerivAt (fun x => c*(Real.cos x-Real.sin x)-R*normD1 1 c (x-n)+slope) _ t
  exact h.congr_deriv (by simp only [curvature,PositiveAngularEnvelope.phi]; ring)

theorem mixed_curvature {c n t : ℝ} (hc : c∈Icc 1 Cmax)
    (ht : t∈Icc 0 frameCap) (hn : n∈Icc 0 frameCap) :
    curvature R 1 c (t-n)-c*PositiveAngularEnvelope.phi t< -(11/200)*c := by
  have hh := uniform_norm_curvature hc (mixed_argument_bound ht hn)
  have hp := mul_le_mul_of_nonneg_left (CorrelatedSameBlock.one_le_phi ht)
    (by linarith [hc.1] : 0≤c)
  linarith

theorem mixed_axis_hasDerivAt (c n t : ℝ) :
    HasDerivAt (fun x => mixedBase c n x-forceA c x (-n)*axial)
      (slope-c*((axial-1/2)*Real.cos t+(1/2)*Real.sin t)) t := by
  have hb := ((((Real.hasDerivAt_cos t).fun_add (Real.hasDerivAt_sin t)).sub_const 1).const_mul
    c).div_const 2
  have hl := (hasDerivAt_id' t).const_mul slope
  have hf := ((Real.hasDerivAt_sin t).const_mul c).add_const (Real.cos (-n))
  have he : (fun x => mixedBase c n x-forceA c x (-n)*axial)=fun x =>
      (c*(Real.cos x+Real.sin x-1)/2+slope*x+((Real.cos n+Real.sin n-1)/2+
        (1+c)*GlobalGA.Secondary.diagonal-vstar n))-(c*Real.sin x+Real.cos (-n))*axial := by
    funext x
    simp only [mixedBase,forceA]
    ring
  rw [he]
  exact (((hb.fun_add hl).add_const _).fun_sub (hf.mul_const axial)).congr_deriv (by ring)

theorem mixed_axis_antitone {c n : ℝ} (hc : c∈Icc 1 Cmax) :
    AntitoneOn (fun x => mixedBase c n x-forceA c x (-n)*axial) (Icc 0 frameCap) := by
  apply antiOn_of_hasDeriv_nonpos
  · intro t ht
    exact (mixed_axis_hasDerivAt c n t).continuousAt.continuousWithinAt
  · intro t ht
    exact mixed_axis_hasDerivAt c n t
  · intro t ht
    have hb := axis_bracket_lower (Ioo_subset_Icc_self ht)
    have hm := mul_le_mul_of_nonneg_right hc.1 (by linarith :
      0≤(axial-1/2)*Real.cos t+(1/2)*Real.sin t)
    norm_num [slope] at ⊢
    linarith

theorem mixed_forward_lower {c t n : ℝ} (hc : c∈Icc 1 Cmax)
    (ht : t∈Icc 0 frameCap) (hn : n∈Icc 0 frameCap) :
    -slope*t+vstar n≤D c t (-n) := by
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hz : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hfar : 0 ≤ mixedBase c n frameCap-
      sortedSupport (forceA c frameCap (-n)) (forceB c frameCap (-n)) := by
    rw [mixed_base_identity hh hn]
    exact (mixed_far_endpoint hc hn).le
  have hleft : 0 ≤ mixedBase c n 0-
      sortedSupport (forceA c 0 (-n)) (forceB c 0 (-n)) := by
    rw [mixed_base_identity hz hn]
    linarith [one_angle_lower hc hn]
  have haxis (x : ℝ) (hx : x∈Icc 0 frameCap) :
      0 ≤ mixedBase c n x-forceA c x (-n)*axial := by
    have hanti : mixedBase c n frameCap-forceA c frameCap (-n)*axial≤
        mixedBase c n x-forceA c x (-n)*axial := mixed_axis_antitone (n:=n) hc hx hh hx.2
    have hpos := forward_force_positive (t:=frameCap) hc (by norm_num [frameCap]) hn
    have hs := axis_support_lower hpos.1 hpos.2
    linarith
  have hbound := support_path_lower
    (base:=mixedBase c n) (f:=fun x => forceA c x (-n)) (g:=fun x => forceB c x (-n))
    (df:=mixedDerivative c n) (ddf:=fun x => curvature R 1 c (x-n)-c*PositiveAngularEnvelope.phi x)
    (κ:=11/200) (by unfold mixedBase; fun_prop)
    (by dsimp [forceA]; fun_prop) (by dsimp [forceB]; fun_prop) ht (by norm_num)
    (fun x hx => forward_force_positive hc hx hn)
    (fun x hx => by
      have hd := diagonal_residual hc (mixed_domain hx hn).1
      rw [edgeWidth_positive_formula hx,edgeWidth_negative_formula hn] at hd
      simp only [positiveTotal,negativeTotal,positivePart,negativePart,
        max_eq_left hx.1,max_eq_left hn.1,max_eq_right (neg_nonpos.mpr hx.1),
        max_eq_right (neg_nonpos.mpr hn.1),neg_neg,zero_add,add_zero] at hd
      dsimp [mixedBase]
      linarith)
    (fun x hx _ => haxis x hx) hleft hfar
    (fun x hx => mixed_full_hasDerivAt hc (Ioo_subset_Icc_self hx) hn)
    (fun x hx => mixed_derivative_hasDerivAt hc (Ioo_subset_Icc_self hx) hn)
    (fun x hx => by
      have hh := mixed_curvature hc (Ioo_subset_Icc_self hx) hn
      linarith [hc.1])
  rw [mixed_base_identity ht hn] at hbound
  linarith

end SquaresInCircles.Eight.GlobalGA.SortedDSevenFifths
end
end
end

section
/-!
## The signed two-angle sorted-D minorant

At a fixed total of equal signs the force norm is constant. The interior support is concave in the
allocation, and the tangent-zero branch is either decreasing or absent. The endpoint theorems of
the two mixed quadrants therefore cover the two quadrants of equal signs (`positive_path_lower`,
`negative_path_lower`), weak ties included, and `lower` holds on the whole signed domain.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.SortedDSevenFifths
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PositiveBT3

def equalBase (c n t : ℝ) (positive : Bool) : ℝ :=
  c*(Real.cos t+Real.sin t-1)/2+(Real.cos (n-t)+Real.sin (n-t)-1)/2+
    (1+c)*GlobalGA.Secondary.diagonal+(if positive then slope*n else -vstar n)

theorem positive_base_identity {c n t : ℝ}
    (hn : n∈Icc 0 frameCap) (ht : t∈Icc 0 n) :
    equalBase c n t true-sortedSupport (forceA c t (n-t)) (forceB c t (n-t))=
      D c t (n-t)+slope*n := by
  have h₁ : t∈Icc 0 frameCap := ⟨ht.1,ht.2.trans hn.2⟩
  have h₂ : n-t∈Icc 0 frameCap := ⟨by linarith [ht.2],by linarith [ht.1,hn.2]⟩
  rw [PositiveBT3.D,edgeWidth_positive_formula h₁,edgeWidth_positive_formula h₂]
  simp only [equalBase,↓reduceIte]
  ring

theorem negative_base_identity {c n t : ℝ}
    (hn : n∈Icc 0 frameCap) (ht : t∈Icc 0 n) :
    equalBase c n t false-sortedSupport (forceA c (-t) (-(n-t))) (forceB c (-t) (-(n-t)))=
      D c (-t) (-(n-t))-vstar n := by
  have h₁ : t∈Icc 0 frameCap := ⟨ht.1,ht.2.trans hn.2⟩
  have h₂ : n-t∈Icc 0 frameCap := ⟨by linarith [ht.2],by linarith [ht.1,hn.2]⟩
  rw [PositiveBT3.D,edgeWidth_negative_formula h₁,edgeWidth_negative_formula h₂]
  simp only [equalBase,Bool.false_eq_true,↓reduceIte]
  ring

theorem positive_full_identity (c n t : ℝ) :
    equalBase c n t true-fullSupport (forceA c t (n-t)) (forceB c t (n-t))=
      c*(Real.cos t+Real.sin t-1)+Real.cos (n-t)+Real.sin (n-t)-1+
      (1+c)*(GlobalGA.Secondary.diagonal+1/2)-R*pairNorm 1 c n+slope*n := by
  rw [fullSupport,force_norm,show t+(n-t)=n by ring]
  dsimp [equalBase,forceA,forceB]
  ring

theorem negative_full_identity (c n t : ℝ) :
    equalBase c n t false-fullSupport (forceA c (-t) (-(n-t))) (forceB c (-t) (-(n-t)))=
      c*(Real.cos t-1)+Real.cos (n-t)-1+
      (1+c)*(GlobalGA.Secondary.diagonal+1/2)-R*pairNorm 1 c (-n)-vstar n := by
  rw [fullSupport,force_norm,show -t+(-(n-t))= -n by ring]
  dsimp [equalBase,forceA,forceB]
  rw [Real.cos_neg,Real.cos_neg,Real.sin_neg,Real.sin_neg]
  ring

def positiveDerivative (c n t : ℝ) : ℝ :=
  c*(Real.cos t-Real.sin t)-(Real.cos (n-t)-Real.sin (n-t))
def negativeDerivative (c n t : ℝ) : ℝ := -c*Real.sin t+Real.sin (n-t)

theorem positive_full_hasDerivAt (c n t : ℝ) :
    HasDerivAt (fun x => equalBase c n x true-
      fullSupport (forceA c x (n-x)) (forceB c x (n-x))) (positiveDerivative c n t) t := by
  have hy : HasDerivAt (fun x : ℝ => n-x) (-1) t := (hasDerivAt_id' t).const_sub n
  have h := (((((Real.hasDerivAt_cos t).fun_add (Real.hasDerivAt_sin t)).sub_const 1).const_mul
    c).fun_add (hy.cos.fun_add hy.sin)).sub_const 1 |>.add_const
      ((1+c)*(GlobalGA.Secondary.diagonal+1/2)-R*pairNorm 1 c n+slope*n)
  have he : (fun x => equalBase c n x true-
      fullSupport (forceA c x (n-x)) (forceB c x (n-x)))=fun x =>
      c*(Real.cos x+Real.sin x-1)+(Real.cos (n-x)+Real.sin (n-x))-1+
        ((1+c)*(GlobalGA.Secondary.diagonal+1/2)-R*pairNorm 1 c n+slope*n) := by
    funext x
    rw [positive_full_identity]
    ring
  rw [he]
  exact h.congr_deriv (by dsimp only [positiveDerivative]; ring)

theorem positive_derivative_hasDerivAt (c n t : ℝ) :
    HasDerivAt (positiveDerivative c n) (-c*PositiveAngularEnvelope.phi t-PositiveAngularEnvelope.phi (n-t)) t := by
  have hy : HasDerivAt (fun x : ℝ => n-x) (-1) t := (hasDerivAt_id' t).const_sub n
  have h := (((Real.hasDerivAt_cos t).fun_sub (Real.hasDerivAt_sin t)).const_mul c).fun_sub
    (hy.cos.fun_sub hy.sin)
  show HasDerivAt (fun x => c*(Real.cos x-Real.sin x)-(Real.cos (n-x)-Real.sin (n-x))) _ t
  exact h.congr_deriv (by simp only [PositiveAngularEnvelope.phi]; ring)

theorem negative_full_hasDerivAt (c n t : ℝ) :
    HasDerivAt (fun x => equalBase c n x false-
      fullSupport (forceA c (-x) (-(n-x))) (forceB c (-x) (-(n-x))))
      (negativeDerivative c n t) t := by
  have hy : HasDerivAt (fun x : ℝ => n-x) (-1) t := (hasDerivAt_id' t).const_sub n
  have h := (((((Real.hasDerivAt_cos t).sub_const 1).const_mul c).fun_add hy.cos).sub_const
    1).add_const ((1+c)*(GlobalGA.Secondary.diagonal+1/2)-R*pairNorm 1 c (-n)-vstar n)
  have he : (fun x => equalBase c n x false-
      fullSupport (forceA c (-x) (-(n-x))) (forceB c (-x) (-(n-x))))=fun x =>
      c*(Real.cos x-1)+Real.cos (n-x)-1+
        ((1+c)*(GlobalGA.Secondary.diagonal+1/2)-R*pairNorm 1 c (-n)-vstar n) := by
    funext x
    rw [negative_full_identity]
    ring
  rw [he]
  exact h.congr_deriv (by dsimp only [negativeDerivative]; ring)

theorem negative_derivative_hasDerivAt (c n t : ℝ) :
    HasDerivAt (negativeDerivative c n) (-c*Real.cos t-Real.cos (n-t)) t := by
  have hy : HasDerivAt (fun x : ℝ => n-x) (-1) t := (hasDerivAt_id' t).const_sub n
  show HasDerivAt (fun x => -c*Real.sin x+Real.sin (n-x)) _ t
  exact (((Real.hasDerivAt_sin t).const_mul (-c)).fun_add hy.sin).congr_deriv (by ring)

theorem positive_axis_hasDerivAt (c n t : ℝ) :
    HasDerivAt (fun x => equalBase c n x true-forceA c x (n-x)*axial)
      (-c*((axial-1/2)*Real.cos t+(1/2)*Real.sin t)-
        ((axial-1/2)*Real.sin (n-t)+(1/2)*Real.cos (n-t))) t := by
  have hy : HasDerivAt (fun x : ℝ => n-x) (-1) t := (hasDerivAt_id' t).const_sub n
  have hb := ((((((Real.hasDerivAt_cos t).fun_add (Real.hasDerivAt_sin t)).sub_const 1).const_mul
    c).div_const 2).fun_add (((hy.cos.fun_add hy.sin).sub_const 1).div_const 2)).add_const
      ((1+c)*GlobalGA.Secondary.diagonal+slope*n)
  have hf := ((Real.hasDerivAt_sin t).const_mul c).fun_add hy.cos
  have he : (fun x => equalBase c n x true-forceA c x (n-x)*axial)=fun x =>
      (c*(Real.cos x+Real.sin x-1)/2+(Real.cos (n-x)+Real.sin (n-x)-1)/2+
        ((1+c)*GlobalGA.Secondary.diagonal+slope*n))-(c*Real.sin x+Real.cos (n-x))*axial := by
    funext x
    simp only [equalBase,forceA,↓reduceIte]
    ring
  rw [he]
  exact (hb.fun_sub (hf.mul_const axial)).congr_deriv (by ring)

theorem positive_axis_antitone {c n : ℝ} (hc : c∈Icc 1 Cmax)
    (hn : n∈Icc 0 frameCap) :
    AntitoneOn (fun x => equalBase c n x true-forceA c x (n-x)*axial) (Icc 0 n) := by
  apply antiOn_of_hasDeriv_nonpos
  · intro t ht
    exact (positive_axis_hasDerivAt c n t).continuousAt.continuousWithinAt
  · intro t ht
    exact positive_axis_hasDerivAt c n t
  · intro t ht
    have ht' : t∈Icc 0 frameCap := ⟨ht.1.le,ht.2.le.trans hn.2⟩
    have hy : n-t∈Icc 0 frameCap := ⟨by linarith [ht.2],by linarith [ht.1,hn.2]⟩
    have hb := axis_bracket_lower ht'
    have hs := (transport_trig hy).2.2.1
    have hcos : 0≤Real.cos (n-t) := by linarith [(transport_trig hy).1]
    have hp := mul_nonneg (show 0≤axial-1/2 by linarith [axial_bounds.1]) hs
    have hcp := mul_nonneg (show 0≤c by linarith [hc.1]) (show
      0≤(axial-1/2)*Real.cos t+(1/2)*Real.sin t by linarith)
    linarith

theorem equal_domains {n t : ℝ} (hn : n∈Icc 0 frameCap) (ht : t∈Icc 0 n) :
    SignedDomain t (n-t) ∧ SignedDomain (-t) (-(n-t)) := by
  have hy : 0≤n-t := by linarith [ht.2]
  have hf : (0:ℝ)≤frameCap := by norm_num [frameCap]
  simp only [SignedDomain,positiveTotal,negativeTotal,positivePart,negativePart,
    max_eq_left ht.1,max_eq_left hy,max_eq_right (neg_nonpos.mpr ht.1),
    max_eq_right (neg_nonpos.mpr hy),neg_neg]
  refine ⟨⟨by linarith [hn.2],by linarith⟩,⟨by linarith,by linarith [hn.2]⟩⟩

theorem positive_path_lower {c n t : ℝ} (hc : c∈Icc 1 Cmax)
    (hn : n∈Icc 0 frameCap) (ht : t∈Icc 0 n) : -slope*n≤D c t (n-t) := by
  have hz : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hleft : 0≤equalBase c n 0 true-sortedSupport (forceA c 0 n) (forceB c 0 n) := by
    have hh := positive_base_identity (c:=c) hn (show (0:ℝ)∈Icc 0 n from ⟨le_rfl,hn.1⟩)
    have hs := mixed_reverse_lower hc hn hz
    simp only [sub_zero,neg_zero,vstar,V_zero] at hh hs
    linarith
  have hright : 0≤equalBase c n n true-sortedSupport (forceA c n 0) (forceB c n 0) := by
    have hh := positive_base_identity (c:=c) hn (show n∈Icc 0 n from ⟨hn.1,le_rfl⟩)
    have hs := mixed_forward_lower hc hn hz
    simp only [sub_self,neg_zero,vstar,V_zero] at hh hs
    linarith
  have hbound := support_path_lower
    (base:=fun x => equalBase c n x true) (f:=fun x => forceA c x (n-x)) (g:=fun x => forceB c x (n-x))
    (df:=positiveDerivative c n) (ddf:=fun x => -c*PositiveAngularEnvelope.phi x-PositiveAngularEnvelope.phi (n-x)) (κ:=1)
    (by dsimp [equalBase]; fun_prop) (by dsimp [forceA]; fun_prop)
    (by dsimp [forceB]; fun_prop) ht (by norm_num)
    (fun x hx => positive_force_positive hc ⟨hx.1,hx.2.trans hn.2⟩
      ⟨by linarith [hx.2],by linarith [hx.1,hn.2]⟩)
    (fun x hx => by
      have h₁ : x∈Icc 0 frameCap := ⟨hx.1,hx.2.trans hn.2⟩
      have h₂ : n-x∈Icc 0 frameCap := ⟨by linarith [hx.2],by linarith [hx.1,hn.2]⟩
      have hd := diagonal_residual hc (equal_domains hn hx).1
      rw [edgeWidth_positive_formula h₁,edgeWidth_positive_formula h₂] at hd
      simp only [positiveTotal,negativeTotal,positivePart,negativePart,
        max_eq_left h₁.1,max_eq_left h₂.1,max_eq_right (neg_nonpos.mpr h₁.1),
        max_eq_right (neg_nonpos.mpr h₂.1),add_zero,vstar,V_zero,sub_zero] at hd
      dsimp [equalBase]
      linarith)
    (fun x hx _ => by
      have ha := positive_axis_antitone hc hn hx ⟨hn.1,le_rfl⟩ hx.2
      have hp := positive_force_positive (y:=0) hc hn (by norm_num [frameCap])
      have hs := axis_support_lower hp.1 hp.2
      simp only [sub_self] at ha
      linarith)
    (by simpa using hleft) (by simpa using hright)
    (fun x _ => positive_full_hasDerivAt c n x)
    (fun x _ => positive_derivative_hasDerivAt c n x)
    (fun x hx => by
      have h₁ := CorrelatedSameBlock.one_le_phi (show x∈Icc 0 frameCap from ⟨hx.1.le,hx.2.le.trans hn.2⟩)
      have h₂ := CorrelatedSameBlock.one_le_phi (show n-x∈Icc 0 frameCap by
        constructor <;> linarith [hx.1,hx.2,hn.2])
      have hm := mul_le_mul_of_nonneg_left h₁ (by linarith [hc.1] : 0≤c)
      linarith [hc.1])
  rw [positive_base_identity hn ht] at hbound
  linarith

def negativeAxisGate (c n t : ℝ) : ℝ :=
  (axial+1/2)*forceB c (-t) (-(n-t))-forceA c (-t) (-(n-t))/2

theorem negative_axis_gate_hasDerivAt (c n t : ℝ) :
    HasDerivAt (negativeAxisGate c n)
      ((axial+1/2)*forceA c (-t) (-(n-t))+forceB c (-t) (-(n-t))/2) t := by
  have hy : HasDerivAt (fun x : ℝ => n-x) (-1) t := (hasDerivAt_id' t).const_sub n
  have hf := ((Real.hasDerivAt_sin t).const_mul (-c)).fun_add hy.cos
  have hg := ((Real.hasDerivAt_cos t).const_mul c).fun_sub hy.sin
  have he : negativeAxisGate c n=fun x =>
      (axial+1/2)*(c*Real.cos x-Real.sin (n-x))-(-c*Real.sin x+Real.cos (n-x))/2 := by
    funext x
    simp only [negativeAxisGate,forceA,forceB,Real.cos_neg,Real.sin_neg]
    ring
  rw [he]
  exact ((hg.const_mul (axial+1/2)).fun_sub (hf.div_const 2)).congr_deriv
    (by simp only [forceA,forceB,Real.cos_neg,Real.sin_neg]; ring)

theorem negative_axis_gate_positive {c n t : ℝ} (hc : c∈Icc 1 Cmax)
    (hn : n∈Icc 0 frameCap) (ht : t∈Icc 0 n) : 0<negativeAxisGate c n t := by
  have hmono : MonotoneOn (negativeAxisGate c n) (Icc 0 n) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro x hx
      exact (negative_axis_gate_hasDerivAt c n x).continuousAt.continuousWithinAt
    · intro x hx
      exact negative_axis_gate_hasDerivAt c n x
    · intro x hx
      have hp := negative_force_positive hc hn (Ioo_subset_Icc_self hx)
      have hm := mul_nonneg (show 0≤axial+1/2 by linarith [axial_bounds.1]) hp.1.le
      linarith [hp.2]
  have hs := (transport_trig hn).2.2.2.1
  have hA : (19/10:ℝ)<axial+1/2 := by linarith [axial_bounds.1]
  have hpos : 0<c-Real.sin n := by linarith [hc.1]
  have hm := mul_lt_mul_of_pos_right hA hpos
  have hz : 0<negativeAxisGate c n 0 := by
    simp only [negativeAxisGate,forceA,forceB,neg_zero,sub_zero,Real.cos_zero,
      Real.sin_zero,Real.cos_neg,Real.sin_neg,mul_zero,zero_add,mul_one]
    nlinarith [Real.cos_le_one n,hc.1]
  exact hz.trans_le (hmono ⟨le_rfl,hn.1⟩ ht ht.1)

theorem negative_path_lower {c n t : ℝ} (hc : c∈Icc 1 Cmax)
    (hn : n∈Icc 0 frameCap) (ht : t∈Icc 0 n) : vstar n≤D c (-t) (-(n-t)) := by
  have hz : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hleft : 0≤equalBase c n 0 false-sortedSupport (forceA c 0 (-n)) (forceB c 0 (-n)) := by
    have hh := negative_base_identity (c:=c) hn (show (0:ℝ)∈Icc 0 n from ⟨le_rfl,hn.1⟩)
    have hs := one_angle_lower hc hn
    simp only [sub_zero,neg_zero] at hh
    linarith
  have hright : 0≤equalBase c n n false-sortedSupport (forceA c (-n) 0) (forceB c (-n) 0) := by
    have hh := negative_base_identity (c:=c) hn (show n∈Icc 0 n from ⟨hn.1,le_rfl⟩)
    have hs := mixed_reverse_lower hc hz hn
    simp only [sub_self,neg_zero,mul_zero,neg_zero,zero_add] at hh hs
    linarith
  have hbound := support_path_lower
    (base:=fun x => equalBase c n x false) (f:=fun x => forceA c (-x) (-(n-x)))
    (g:=fun x => forceB c (-x) (-(n-x))) (df:=negativeDerivative c n)
    (ddf:=fun x => -c*Real.cos x-Real.cos (n-x)) (κ:=1/2)
    (by dsimp [equalBase]; fun_prop) (by dsimp [forceA]; fun_prop)
    (by dsimp [forceB]; fun_prop) ht (by norm_num)
    (fun x hx => negative_force_positive hc hn hx)
    (fun x hx => by
      have h₁ : x∈Icc 0 frameCap := ⟨hx.1,hx.2.trans hn.2⟩
      have h₂ : n-x∈Icc 0 frameCap := ⟨by linarith [hx.2],by linarith [hx.1,hn.2]⟩
      have hd := diagonal_residual hc (equal_domains hn hx).2
      rw [edgeWidth_negative_formula h₁,edgeWidth_negative_formula h₂] at hd
      simp only [positiveTotal,negativeTotal,positivePart,negativePart,
        max_eq_left h₁.1,max_eq_left h₂.1,max_eq_right (neg_nonpos.mpr h₁.1),
        max_eq_right (neg_nonpos.mpr h₂.1),neg_neg,add_zero,mul_zero,
        show x+(n-x)=n by ring] at hd
      dsimp [equalBase]
      linarith)
    (fun x hx ha => by
      have hp := negative_axis_gate_positive hc hn hx
      dsimp [negativeAxisGate] at hp
      linarith)
    (by simpa using hleft) (by simpa using hright)
    (fun x _ => negative_full_hasDerivAt c n x)
    (fun x _ => negative_derivative_hasDerivAt c n x)
    (fun x hx => by
      have h₁ := (transport_trig (show x∈Icc 0 frameCap from ⟨hx.1.le,hx.2.le.trans hn.2⟩)).1
      have h₂ := (transport_trig (show n-x∈Icc 0 frameCap by
        constructor <;> linarith [hx.1,hx.2,hn.2])).1
      have hm := mul_le_mul_of_nonneg_right hc.1 (by linarith : 0≤Real.cos x)
      linarith)
  rw [negative_base_identity hn ht] at hbound
  linarith

/-- The minorant `-slope * positiveTotal x y + vstar (negativeTotal x y) ≤ D c x y` on the whole
signed domain, with the sorted zero-angle support and every equality transition. -/
theorem lower {c x y : ℝ} (hc : c∈Icc 1 Cmax)
    (hxy : SignedDomain x y) :
    -slope*positiveTotal x y+vstar (negativeTotal x y)≤D c x y := by
  have ha := signed_domain_angles hxy
  by_cases hx : 0≤x
  · by_cases hy : 0≤y
    · have hn : x+y∈Icc 0 frameCap := by
        refine ⟨add_nonneg hx hy,?_⟩
        simpa [positiveTotal,positivePart,max_eq_left hx,max_eq_left hy] using hxy.1
      have hh := positive_path_lower hc hn (show x∈Icc 0 (x+y) by constructor <;> linarith)
      simp only [show x+y-x=y by ring] at hh
      simpa [positiveTotal,negativeTotal,positivePart,negativePart,
        max_eq_left hx,max_eq_left hy,max_eq_right (neg_nonpos.mpr hx),
        max_eq_right (neg_nonpos.mpr hy),vstar] using hh
    · have hy' : 0≤ -y := by linarith
      have hh := mixed_forward_lower hc ⟨hx,(le_abs_self x).trans ha.1⟩
        ⟨hy',(neg_le_abs y).trans ha.2⟩
      simpa [positiveTotal,negativeTotal,positivePart,negativePart,
        max_eq_left hx,max_eq_left hy',max_eq_right (neg_nonpos.mpr hx),
        max_eq_right (le_of_not_ge hy)] using hh
  · have hx' : 0≤ -x := by linarith
    by_cases hy : 0≤y
    · have hh := mixed_reverse_lower hc ⟨hy,(le_abs_self y).trans ha.2⟩
        ⟨hx',(neg_le_abs x).trans ha.1⟩
      simpa [positiveTotal,negativeTotal,positivePart,negativePart,
        max_eq_left hy,max_eq_left hx',max_eq_right (neg_nonpos.mpr hy),
        max_eq_right (le_of_not_ge hx)] using hh
    · have hy' : 0≤ -y := by linarith
      have hn : -x+(-y)∈Icc 0 frameCap := by
        refine ⟨add_nonneg hx' hy',?_⟩
        simpa [negativeTotal,negativePart,max_eq_left hx',max_eq_left hy'] using hxy.2
      have hh := negative_path_lower hc hn
        (show -x∈Icc 0 (-x+(-y)) by constructor <;> linarith)
      simp only [neg_neg,show -x+(-y)-(-x)= -y by ring] at hh
      simpa [positiveTotal,negativeTotal,positivePart,negativePart,
        max_eq_left hx',max_eq_left hy',max_eq_right (le_of_not_ge hx),
        max_eq_right (le_of_not_ge hy)] using hh

end SquaresInCircles.Eight.GlobalGA.SortedDSevenFifths
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.SortedDSevenFifths
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PositiveBT3

theorem actual_support {Q c x y : ℝ} {P : SignedPoint}
    (hs : P.Sorted) (hy : P.y≤0) (hP : P.Contained Q) (hQ : Q≤qCap)
    (hc : c∈Icc 1 Cmax) (hxy : SignedDomain x y) :
    forceA c x y*P.a+forceB c x y*(-P.y)≤ sortedSupport (forceA c x y) (forceB c x y) := by
  have ha := signed_domain_angles hxy
  have huse (hp : 0<forceA c x y ∧ 0<forceB c x y) :=
    actual_sorted_support hs hy hP hQ hp.1.le hp.2.le
  by_cases hx0 : 0≤x
  · have hx : x∈Icc 0 frameCap := ⟨hx0,(le_abs_self x).trans ha.1⟩
    by_cases hy0 : 0≤y
    · exact huse (positive_force_positive hc hx ⟨hy0,(le_abs_self y).trans ha.2⟩)
    · have hn : -y∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs y).trans ha.2⟩
      apply huse
      simpa only [neg_neg] using forward_force_positive hc hx hn
  · have hn : -x∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs x).trans ha.1⟩
    by_cases hy0 : 0≤y
    · have ht : y∈Icc 0 frameCap := ⟨hy0,(le_abs_self y).trans ha.2⟩
      have hnt := transport_trig hn
      have htt := transport_trig ht
      have hphi := CorrelatedSameBlock.one_le_phi hn
      have hmul := mul_le_mul_of_nonneg_left hphi (by linarith [hc.1] : 0≤c)
      have hfg : forceA c x y≤forceB c x y := by
        dsimp [forceA,forceB,PositiveAngularEnvelope.phi] at *
        rw [Real.cos_neg,Real.sin_neg] at hphi hnt hmul
        nlinarith [Real.cos_le_one y,hc.1,htt.2.2.1]
      have hdiff : 0<Real.cos (-x)-Real.sin (-x) := by
        linarith [hnt.1,hnt.2.2.2.1]
      have hscaled := mul_pos (by linarith [hc.1] : 0<c) hdiff
      have hsum : 0≤forceA c x y+forceB c x y := by
        dsimp [forceA,forceB]
        rw [Real.cos_neg,Real.sin_neg] at hscaled
        linarith [htt.1,htt.2.2.1]
      have hcircle : (P.a+1/2)^2+(-P.y+1/2)^2≤qCap := by
        simpa [SignedPoint.Contained,SignedPoint.circle,abs_of_nonpos hy] using hP.trans hQ
      have hb : -P.y≤P.a := by simpa [abs_of_nonpos hy] using hs.2
      have hh := raw_clipped_support hcircle hb (by linarith [hs.1]) hsum
      simpa [clippedSupport,sortedSupport,hfg] using hh
    · have htotal : -x+(-y)∈Icc 0 frameCap := by
        refine ⟨by linarith,?_⟩
        simpa [negativeTotal,negativePart,max_eq_left (show 0≤ -x by linarith),
          max_eq_left (show 0≤ -y by linarith)] using hxy.2
      have hp := negative_force_positive hc htotal
        (show -x∈Icc 0 (-x+(-y)) by constructor <;> linarith)
      apply huse
      simpa only [neg_neg,show -x+(-y)-(-x)= -y by ring] using hp

/-- The wider signed D envelope at the point `P` itself. -/
theorem actual_minorant {Q c x y : ℝ} {P : SignedPoint}
    (hs : P.Sorted) (hy : P.y≤0) (hP : P.Contained Q) (hQ : Q≤qCap)
    (hc : c∈Icc 1 Cmax) (hxy : SignedDomain x y) :
    -slope*positiveTotal x y+vstar (negativeTotal x y)≤
      c*(edgeWidth x-1)+edgeWidth y-1+(1+c)*GlobalGA.Secondary.diagonal-
        (forceA c x y*P.a+forceB c x y*(-P.y)) := by
  have hsupp := actual_support hs hy hP hQ hc hxy
  have hminor := lower hc hxy
  dsimp only [PositiveBT3.D] at hminor
  linarith

theorem lower_for {k c x y : ℝ} (hk : k∈Icc (1/2:ℝ) K)
    (hc : c∈Icc 1 Cmax) (hxy : SignedDomain x y) :
    -slope*positiveTotal x y+V R k 1 (negativeTotal x y)≤D c x y := by
  have hn : negativeTotal x y∈Icc 0 frameCap :=
    ⟨add_nonneg (negativePart_nonneg _) (negativePart_nonneg _),hxy.2⟩
  have hm := OrdinaryNegativeEnvelope.V_monotone_smaller (R:=R) (q:=1) (Real.sqrt_nonneg _)
    (by norm_num) hn
    (show k∈Icc (1/2:ℝ) 1 from ⟨hk.1,by dsimp [K] at hk; linarith [hk.2]⟩)
    (show K∈Icc (1/2:ℝ) 1 by norm_num [K]) hk.2
  have hh := lower hc hxy
  dsimp only [vstar] at hh hm
  linarith

theorem actual_minorant_for {Q k c x y : ℝ} {P : SignedPoint}
    (hs : P.Sorted) (hy : P.y≤0) (hP : P.Contained Q) (hQ : Q≤qCap)
    (hk : k∈Icc (1/2:ℝ) K) (hc : c∈Icc 1 Cmax) (hxy : SignedDomain x y) :
    -slope*positiveTotal x y+V R k 1 (negativeTotal x y)≤
      c*(edgeWidth x-1)+edgeWidth y-1+(1+c)*GlobalGA.Secondary.diagonal-
        (forceA c x y*P.a+forceB c x y*(-P.y)) := by
  have hsupp := actual_support hs hy hP hQ hc hxy
  have hminor := lower_for hk hc hxy
  dsimp only [PositiveBT3.D] at hminor
  linarith

end SquaresInCircles.Eight.GlobalGA.SortedDSevenFifths
end
end
end
