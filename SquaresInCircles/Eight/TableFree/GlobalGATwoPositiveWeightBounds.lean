module

public import SquaresInCircles.Eight.TableFree.GlobalGATwoPositiveHighPolynomial

/-!
# The explicit high split family stays in its analytic domain

Endpoint quotients retain the monotonic directions of the cubic
weights.  The A/T auxiliary masses have a common positive lower
bound.  The B coefficient cap is proved on the whole interval by
one completed square, including its interior minimum.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalGA.TwoPositive.Certificate

open Polynomial WholeIntervalPolynomial
open PositiveTD.Certificate (L h)

def kRight : ℚ[X] := (highK-C (highK.eval h)).divByMonic (X-C h)
def lRight : ℚ[X] := -((highL-C (highL.eval h)).divByMonic (X-C h))
def cLeft : ℚ[X] := -((highC-C (highC.eval L)).divByMonic (X-C L))
def cRight : ℚ[X] := -((highC-C (highC.eval h)).divByMonic (X-C h))
def rangePoly : Fin 7→ℚ[X] :=
  ![highK,kRight,lRight,cLeft,cRight,highC-C (9/10)*highL,C (11/10)*highL-highC]
def rangeReserve : Fin 7→ℚ := ![669/1000,1/10,1/100,1/100,1/100,2/25,2/25]
def mass (e : Endpoint) : Fin 7→ℚ[X] :=
  ![highRH,highRG,highRD,highRB e,highRHminus,highRGminus,highRBminus e]
def gapCentered : ℚ[X] := DirectedPowerBounds.shift (13/30) highQGap
def gapCurvature : ℚ := gapCentered.coeff 2-PowerTailBounds.norm gapCentered 3 6 (4/15)
def gapReserve : ℚ := gapCentered.coeff 0-(gapCentered.coeff 1)^2/(4*gapCurvature)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem range_identities (i : Fin 7) :
    centered L h (rangePoly i)=expansion 3 (centered L h (rangePoly i)) := by
  fin_cases i <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem range_reserves (i : Fin 7) :
    rangeReserve i<lowerOn 3 L h (rangePoly i) := by fin_cases i <;> decide

theorem range_lower (i : Fin 7) {z : ℝ} (hz : z∈Icc (1/6:ℝ) (7/10:ℝ)) :
    (rangeReserve i:ℝ)<aeval z (rangePoly i) :=
  positive_on_interval (by norm_num [L,h]) (range_identities i) (range_reserves i) hz

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem weight_endpoint_identities :
    highK=C (highK.eval h)+(X-C h)*kRight ∧
    highL=C (highL.eval h)+(C h-X)*lRight ∧
    highC=C (highC.eval L)-(X-C L)*cLeft ∧
    highC=C (highC.eval h)+(C h-X)*cRight := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem weight_endpoint_reserves :
    highK.eval h<(843/1000:ℚ) ∧ (89/100:ℚ)<highL.eval h ∧
      (89/100:ℚ)<highC.eval h ∧ highC.eval L=10163/10000 := by decide

theorem highL_upper {z : ℝ} (hz : z∈Icc (1/6:ℝ) (7/10:ℝ)) :
    aeval z highL<(5001/5000:ℝ) := by
  let u : ℝ := z-1/6
  have hu : u∈Icc 0 (8/15:ℝ) := ⟨by dsimp [u]; linarith [hz.1],
    by dsimp [u]; linarith [hz.2]⟩
  have hcube : u^3≤(8/15)*u^2 := by
    nlinarith [mul_le_mul_of_nonneg_right hu.2 (sq_nonneg u)]
  have he : aeval z highL=1+(7/400)*u-(2733/2500)*u^2+(639/500)*u^3 := by
    simp [highL,t,u,L]
  rw [he]
  nlinarith [sq_nonneg (u-(7/400)/(2*(1029/2500)))]

/-- Every inequality holds throughout the one high interval. -/
theorem high_ranges {z : ℝ} (hz : z∈Icc (1/6:ℝ) (7/10:ℝ)) :
    (669/1000:ℝ)<aeval z highK ∧ aeval z highK<843/1000 ∧
      (89/100:ℝ)<aeval z highL ∧ aeval z highL<5001/5000 ∧
      (89/100:ℝ)<aeval z highC ∧ aeval z highC≤10163/10000 ∧
      (9/10)*aeval z highL<aeval z highC ∧
      aeval z highC<(11/10)*aeval z highL := by
  have h0 := range_lower 0 hz
  have h1 := range_lower 1 hz
  have h2 := range_lower 2 hz
  have h3 := range_lower 3 hz
  have h4 := range_lower 4 hz
  have h5 := range_lower 5 hz
  have h6 := range_lower 6 hz
  norm_num [rangePoly,rangeReserve] at h0 h1 h2 h3 h4 h5 h6
  have eK := congrArg (fun f : ℚ[X] => aeval z f) weight_endpoint_identities.1
  have eL := congrArg (fun f : ℚ[X] => aeval z f) weight_endpoint_identities.2.1
  have eC0 := congrArg (fun f : ℚ[X] => aeval z f) weight_endpoint_identities.2.2.1
  have eCh := congrArg (fun f : ℚ[X] => aeval z f) weight_endpoint_identities.2.2.2
  simp only [map_add,map_sub,map_mul,aeval_C,aeval_X] at eK eL eC0 eCh
  have hK : (highK.eval h:ℝ)<843/1000 := by exact_mod_cast weight_endpoint_reserves.1
  have hL : (89/100:ℝ)<(highL.eval h:ℝ) := by exact_mod_cast weight_endpoint_reserves.2.1
  have hC : (89/100:ℝ)<(highC.eval h:ℝ) := by exact_mod_cast weight_endpoint_reserves.2.2.1
  have hC0 : (highC.eval L:ℝ)=10163/10000 := by exact_mod_cast weight_endpoint_reserves.2.2.2
  have pK := mul_nonpos_of_nonpos_of_nonneg
    (show z-(h:ℝ)≤0 by norm_num [h]; linarith [hz.2]) (show 0≤aeval z kRight by linarith)
  have pL := mul_nonneg (show 0≤(h:ℝ)-z by norm_num [h]; linarith [hz.2])
    (show 0≤aeval z lRight by linarith)
  have pC0 := mul_nonneg (show 0≤z-(L:ℝ) by norm_num [L]; linarith [hz.1])
    (show 0≤aeval z cLeft by linarith)
  have pCh := mul_nonneg (show 0≤(h:ℝ)-z by norm_num [h]; linarith [hz.2])
    (show 0≤aeval z cRight by linarith)
  exact ⟨h0,by linarith,by linarith,highL_upper hz,by linarith,by linarith,
    by linarith,by linarith⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem mass_identities (e : Endpoint) (i : Fin 7) :
    centered L h (mass e i)=expansion 8 (centered L h (mass e i)) := by
  cases e <;> fin_cases i <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem mass_reserves (e : Endpoint) (i : Fin 7) :
    (7/10:ℚ)<lowerOn 8 L h (mass e i) := by cases e <;> fin_cases i <;> decide

theorem masses_positive (e : Endpoint) (i : Fin 7) {z : ℝ}
    (hz : z∈Icc (1/6:ℝ) (7/10:ℝ)) : 0<aeval z (mass e i) := by
  have hh := positive_on_interval (by norm_num [L,h] : L<h)
    (mass_identities e i) (mass_reserves e i) hz
  linarith

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gap_identity :
    gapCentered=C (gapCentered.coeff 0)+C (gapCentered.coeff 1)*X+
      C (gapCentered.coeff 2)*X^2+PowerTailBounds.tail gapCentered 3 6 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gap_reserves : (107/400:ℚ)<gapCurvature ∧ (1/250:ℚ)<gapReserve := by decide

theorem highQGap_positive {z : ℝ} (hz : z∈Icc (1/6:ℝ) (7/10:ℝ)) :
    0<aeval z highQGap := by
  have hx : |z-13/30|≤(4/15:ℝ) := abs_le.mpr
    ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hb := PowerTailBounds.quadratic_lower gap_identity (by norm_num) hx
  have hc : (0:ℝ)<(gapCurvature:ℝ) := by
    exact_mod_cast (lt_trans (by norm_num : (0:ℚ)<107/400) gap_reserves.1)
  have hm := ChebyshevLeadingBounds.quadratic_min
    (a:=(gapCentered.coeff 0:ℝ)) (b:=(gapCentered.coeff 1:ℝ)) (x:=z-13/30) hc
  have he : aeval (z-13/30) gapCentered=aeval z highQGap := by simp [gapCentered]
  rw [he] at hb
  have hr : (1/250:ℝ)<(gapReserve:ℝ) := by exact_mod_cast gap_reserves.2
  dsimp [gapReserve,gapCurvature] at hr hm
  push_cast at hr hm
  linarith

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem highQ_C_identity :
    centered L h (highQ-highC)=expansion 3 (centered L h (highQ-highC)) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem highQ_C_reserve : (1/3000:ℚ)<lowerOn 3 L h (highQ-highC) := by decide

theorem highQ_C_positive {z : ℝ} (hz : z∈Icc (1/6:ℝ) (7/10:ℝ)) :
    aeval z highC<aeval z highQ := by
  have hh := positive_on_interval (by norm_num [L,h] : L<h)
    highQ_C_identity highQ_C_reserve hz
  simp only [map_sub] at hh
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.TwoPositive.Certificate
