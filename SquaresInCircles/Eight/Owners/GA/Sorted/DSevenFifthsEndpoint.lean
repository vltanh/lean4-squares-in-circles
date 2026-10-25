module

public import SquaresInCircles.Eight.Owners.GA.Positive.BT3DEndpoints
public import SquaresInCircles.Eight.Owners.GA.Sorted.DSevenFifthsData

/-!
# Eight squares: the additional intrinsic D endpoint at c=7/5

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
