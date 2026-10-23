module

public import SquaresInCircles.Eight.TableFree.SoleLowGapPolynomials

/-!
# Two coefficient comparisons for the middle and high sole-E families

Uncompiled source. The first comparison keeps the correlation between
the two high-family coefficients. The second proves that the actual
middle E-endpoint coefficient is below c, using directed Taylor bounds.
Each is one polynomial inequality on its complete coefficient interval.
The exact reductions have not been run.
-/

@[expose] public section
namespace SquaresInCircles.Eight.TableFree.SoleBalancedPolynomials
open Polynomial WholeIntervalPolynomial SoleECoefficients HighOrderTaylor

def highNormGap : ℚ[X] := C ((53/50)^2)-
  (SoleScalarPolynomials.k .high)^2*(1+(SoleScalarPolynomials.g .high)^2)

def middleCoefficientGap : ℚ[X] :=
  SoleScalarPolynomials.c .middle-SoleScalarPolynomials.cosine .middle-
    SoleScalarPolynomials.eta .middle*
      SoleLowGapPolynomials.sinUpper.comp (SoleScalarPolynomials.parameter .middle)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem highNormGap_identity : centered 0 (7/20) highNormGap=
    expansion 4 (centered 0 (7/20) highNormGap) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem highNormGap_reserve : (1/200 : ℚ)<lowerOn 4 0 (7/20) highNormGap := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem middleCoefficientGap_identity : centered 0 (3/20) middleCoefficientGap=
    expansion 16 (centered 0 (3/20) middleCoefficientGap) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem middleCoefficientGap_reserve :
    (1/10000 : ℚ)<lowerOn 16 0 (3/20) middleCoefficientGap := by decide

theorem high_norm_square {t : ℝ} (ht : t∈domain .high) :
    (k .high t)^2*(1+(g .high t)^2)<(53/50 : ℝ)^2 := by
  have hz := SoleScalarPolynomials.local_parameter ht
  have hb := positive_on_interval (by norm_num) highNormGap_identity highNormGap_reserve
    (show t-7/20∈Set.Icc ((0:ℚ):ℝ) ((7/20:ℚ):ℝ) by
      simpa [SoleScalarPolynomials.origin,SoleScalarPolynomials.length] using hz)
  have hc := SoleScalarData.polynomial_parameters .high t
  norm_num [SoleScalarPolynomials.origin] at hc
  simp only [highNormGap,map_sub,map_mul,map_pow,map_add,map_one,aeval_C,hc.1,hc.2.2.2.1] at hb
  norm_num at hb
  linarith

theorem middle_p_lt_c {t : ℝ} (ht : t∈domain .middle) :
    p .middle t t<c .middle t := by
  have hz := SoleScalarPolynomials.local_parameter ht
  have hb := positive_on_interval (by norm_num) middleCoefficientGap_identity
    middleCoefficientGap_reserve
    (show t-1/5∈Set.Icc ((0:ℚ):ℝ) ((3/20:ℚ):ℝ) by
      simpa [SoleScalarPolynomials.origin,SoleScalarPolynomials.length] using hz)
  have hc := SoleScalarData.polynomial_parameters .middle t
  have htrig := SoleScalarData.polynomial_trig .middle t
  have hpar : aeval (t-1/5) (SoleScalarPolynomials.parameter .middle)=t := by
    simp [SoleScalarPolynomials.parameter,SoleScalarPolynomials.origin]
  norm_num [SoleScalarPolynomials.origin] at hc htrig
  simp only [middleCoefficientGap,map_sub,map_mul,aeval_comp,hpar,
    SoleLowGapPolynomials.sinUpper_eval,hc.2.2.1,hc.2.2.2.2,htrig.2.1] at hb
  have hs := sin_le_S13 (angle ht).1
  have hcos := cos_le_C16 (angle ht).1
  have heta := (positive ht).2.2.2.2
  have hm := mul_le_mul_of_nonneg_left hs heta
  simp only [p,show Band.middle≠Band.high by decide,if_false]
  norm_num at hb
  linarith

end SquaresInCircles.Eight.TableFree.SoleBalancedPolynomials
