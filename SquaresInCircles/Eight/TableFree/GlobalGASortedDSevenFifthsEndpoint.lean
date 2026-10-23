module

public import SquaresInCircles.Eight.TableFree.GlobalGASortedDSevenFifthsData

/-!
# The additional intrinsic D endpoint at c=7/5

Uncompiled Section 2 of the seven-fifths companion. Its single degree
eighteen certificate is the prescribed coefficient norm on [0,.7].
The c=1 endpoint is the unchanged earlier theorem. Both signs of the
isolated radical difference are covered by the squared certificate.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.SortedDSevenFifths.DEndpoint
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
set_option maxHeartbeats 0 in
theorem constant_positive : (1253/625:ℚ)<constant := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem expansion_certificate : centered 0 h Z=expansion 18 (centered 0 h Z) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem reserve_certificate : (317/200:ℚ)<lowerOn 18 0 h Z := by decide

theorem polynomial_positive {n : ℝ} (hn : n∈Icc 0 frameCap) : (317/200:ℝ)<aeval n Z :=
  positive_on_interval (by norm_num [h]) expansion_certificate reserve_certificate hn

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
  refine ⟨by rw [hP]; positivity,hH.2.1,?_,hH.2.2.2⟩
  apply Real.sqrt_le_sqrt
  rw [hP]
  have hm := mul_le_mul_of_nonneg_left ht (by norm_num [Cmax] : (0:ℝ)≤2*Cmax)
  dsimp [pairNorm]
  nlinarith

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
  have hfull := fullD_lower (c:=Cmax)
    (by norm_num [frameCap]) (by rw [abs_neg,abs_of_nonneg hn.1]; exact hn.2)
  rw [fullD_mixed (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) hn] at hfull
  have hcst : (constant:ℝ)=Cmax*(phiLower:ℝ)+1+
      (Cmax+1)*((cLower:ℝ)-1/2)+slope*frameCap-(Tzero:ℝ) := by
    simp [constant,Cmax,slope,h,frameCap]
  rw [hcst]
  dsimp [vstar,V]
  nlinarith

theorem upper_endpoint {n : ℝ} (hn : n∈Icc 0 frameCap) :
    0<D Cmax frameCap (-n)+slope*frameCap-vstar n := by
  have hb := norm_bounds hn
  have hA : (0:ℝ)<(constant:ℝ) := by
    have hh : (1253/625:ℝ)<(constant:ℝ) := by exact_mod_cast constant_positive
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

end SquaresInCircles.Eight.TableFree.GlobalGA.SortedDSevenFifths.DEndpoint
