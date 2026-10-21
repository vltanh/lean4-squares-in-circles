module

public import SquaresInCircles.Eight.TableFree.GlobalGATwoPositivePolynomialData
public import SquaresInCircles.Eight.TableFree.CenteredMonomialBounds

/-!
# Six whole-interval positive split endpoint numerators

The H and G numerators retain their value at 1/6.  Their quotient
polynomials are bounded by a Chebyshev coefficient sum or an exact
completed square.  Each B numerator retains its endpoint chord; the
chord quotient decreases to a positive value.  The displayed rational
identities and reserves concern the complete interval [1/6,7/10].
Uncompiled source draft; the kernel reductions have not been run.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalGA.TwoPositive.Certificate

open Polynomial WholeIntervalPolynomial
open PositiveTD.Certificate (L h)

def highHDegree : Endpoint→ℕ
  | .atT => 40
  | .atA => 26
def highTGCoefficients : ℕ→ℚ := coefficient 43 (centered L h (highQG .atT))
def highAGCoefficients : ℕ→ℚ := coefficient 29 (centered L h (highQG .atA))
def highBNegSlope (e : Endpoint) : ℚ[X] :=
  DirectedPowerBounds.shift (13/30) (-(highQB e).derivative)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem high_HG_identities (e : Endpoint) :
    highNH e=C ((highNH e).eval L)+(X-C L)*highQH e ∧
    highNG e=C ((highNG e).eval L)+(X-C L)*highQG e := by
  cases e <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem high_HG_left_reserves (e : Endpoint) :
    (1/625:ℚ)<(highNH e).eval L ∧ (17/10000:ℚ)<(highNG e).eval L := by
  cases e <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem high_H_expansion (e : Endpoint) :
    centered L h (highQH e)=expansion (highHDegree e) (centered L h (highQH e)) := by
  cases e <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem high_H_quotient_reserve (e : Endpoint) :
    (1/20:ℚ)<lowerOn (highHDegree e) L h (highQH e) := by
  cases e <;> decide

theorem highNH_positive (e : Endpoint) {z : ℝ} (hz : z∈Icc (1/6:ℝ) (7/10:ℝ)) :
    0<aeval z (highNH e) := by
  have hq := positive_on_interval (by norm_num [L,h] : L<h)
    (high_H_expansion e) (high_H_quotient_reserve e) hz
  have hleft : (1/625:ℝ)<((highNH e).eval L:ℝ) := by
    exact_mod_cast (high_HG_left_reserves e).1
  have he := congrArg (fun f : ℚ[X] => aeval z f) (high_HG_identities e).1
  simp only [map_add,map_mul,map_sub,aeval_C,aeval_X] at he
  have hprod : 0≤(z-(L:ℝ))*aeval z (highQH e) :=
    mul_nonneg (by norm_num [L]; linarith [hz.1]) (by norm_num at hq; linarith)
  linarith

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem high_TG_identity :
    centered L h (highQG .atT)=C (highTGCoefficients 0-highTGCoefficients 2)+
      C (highTGCoefficients 1)*X+C (2*highTGCoefficients 2)*X^2+
        ChebyshevLeadingBounds.tail highTGCoefficients 3 41 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem high_TG_reserve : 0<highTGCoefficients 2 ∧
    (69/10000:ℚ)<ChebyshevLeadingBounds.quadraticReserve highTGCoefficients 41 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem high_AG_identity :
    centered L h (highQG .atA)=C (highAGCoefficients 0-highAGCoefficients 2)+
      C (highAGCoefficients 1-3*highAGCoefficients 3)*X+
      C (2*highAGCoefficients 2)*X^2+C (4*highAGCoefficients 3)*X^3+
        ChebyshevLeadingBounds.tail highAGCoefficients 4 26 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem high_AG_reserve : 0<2*highAGCoefficients 2-4*|highAGCoefficients 3| ∧
    (29/2500:ℚ)<ChebyshevLeadingBounds.cubicReserve highAGCoefficients 26 := by decide

theorem highQG_positive (e : Endpoint) {z : ℝ} (hz : z∈Icc (1/6:ℝ) (7/10:ℝ)) :
    0<aeval z (highQG e) := by
  cases e
  · have hh := ChebyshevLeadingBounds.quadratic_on_interval
      (by norm_num [L,h] : L<h) high_TG_identity high_TG_reserve.1 hz
    have hr : (69/10000:ℝ)<
        (ChebyshevLeadingBounds.quadraticReserve highTGCoefficients 41:ℝ) := by
      exact_mod_cast high_TG_reserve.2
    linarith
  · have hh := ChebyshevLeadingBounds.cubic_on_interval
      (by norm_num [L,h] : L<h) high_AG_identity high_AG_reserve.1 hz
    have hr : (29/2500:ℝ)<
        (ChebyshevLeadingBounds.cubicReserve highAGCoefficients 26:ℝ) := by
      exact_mod_cast high_AG_reserve.2
    linarith

theorem highNG_positive (e : Endpoint) {z : ℝ} (hz : z∈Icc (1/6:ℝ) (7/10:ℝ)) :
    0<aeval z (highNG e) := by
  have hq := highQG_positive e hz
  have hleft : (17/10000:ℝ)<((highNG e).eval L:ℝ) := by
    exact_mod_cast (high_HG_left_reserves e).2
  have he := congrArg (fun f : ℚ[X] => aeval z f) (high_HG_identities e).2
  simp only [map_add,map_mul,map_sub,aeval_C,aeval_X] at he
  have hprod : 0≤(z-(L:ℝ))*aeval z (highQG e) :=
    mul_nonneg (by norm_num [L]; linarith [hz.1]) hq.le
  linarith

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem high_B_chord_identity (e : Endpoint) :
    highNB e=highChord e+(X-C L)*(C h-X)*highQB e := by cases e <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem high_B_slope_identity (e : Endpoint) :
    highBNegSlope e=C ((highBNegSlope e).coeff 0)+
      PowerTailBounds.tail (highBNegSlope e) 1 40 := by cases e <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem high_B_slope_reserve (e : Endpoint) :
    (2/5:ℚ)<(highBNegSlope e).coeff 0-
      PowerTailBounds.norm (highBNegSlope e) 1 40 (4/15) := by cases e <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem high_B_endpoint_reserves (e : Endpoint) :
    (3/100:ℚ)<(highNB e).eval L ∧ (3/100:ℚ)<(highNB e).eval h ∧
      (3/40:ℚ)<(highQB e).eval h := by cases e <;> decide

theorem highQB_derivative_negative (e : Endpoint) {z : ℝ}
    (hz : z∈Icc (1/6:ℝ) (7/10:ℝ)) : aeval z (highQB e).derivative<0 := by
  have hx : |z-13/30|≤(4/15:ℝ) := abs_le.mpr
    ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hh := DirectedPowerBounds.constant_lower (high_B_slope_identity e) hx
  have hr : (2/5:ℝ)<((highBNegSlope e).coeff 0:ℝ)-
      (PowerTailBounds.norm (highBNegSlope e) 1 40 (4/15):ℝ) := by
    exact_mod_cast high_B_slope_reserve e
  have he : aeval (z-13/30) (highBNegSlope e)= -aeval z (highQB e).derivative := by
    simp [highBNegSlope]
  rw [he] at hh
  linarith

theorem highQB_positive (e : Endpoint) {z : ℝ} (hz : z∈Icc (1/6:ℝ) (7/10:ℝ)) :
    0<aeval z (highQB e) := by
  have hm : AntitoneOn (fun z : ℝ => aeval z (highQB e)) (Icc (1/6) (7/10)) := by
    apply antiOn_of_hasDeriv_nonpos
    · intro z _
      exact (CenteredMonomialBounds.aeval_hasDerivAt (highQB e) z).continuousAt.continuousWithinAt
    · exact fun z _ => CenteredMonomialBounds.aeval_hasDerivAt (highQB e) z
    · exact fun z hz => (highQB_derivative_negative e (Ioo_subset_Icc_self hz)).le
  have hh := hm hz (by norm_num) hz.2
  have hr : (3/40:ℝ)<aeval (7/10:ℝ) (highQB e) := by
    exact_mod_cast (high_B_endpoint_reserves e).2.2
  linarith

theorem highNB_positive (e : Endpoint) {z : ℝ} (hz : z∈Icc (1/6:ℝ) (7/10:ℝ)) :
    0<aeval z (highNB e) := by
  have hq := highQB_positive e hz
  have hleft : (3/100:ℝ)≤((highNB e).eval L:ℝ) := by
    exact_mod_cast (high_B_endpoint_reserves e).1.le
  have hright : (3/100:ℝ)≤((highNB e).eval h:ℝ) := by
    exact_mod_cast (high_B_endpoint_reserves e).2.1.le
  have hl := mul_le_mul_of_nonneg_left hleft
    (show 0≤((h:ℝ)-z)/((h:ℝ)-(L:ℝ)) by
      apply div_nonneg <;> norm_num [h,L] <;> linarith [hz.2])
  have hr := mul_le_mul_of_nonneg_left hright
    (show 0≤(z-(L:ℝ))/((h:ℝ)-(L:ℝ)) by
      apply div_nonneg <;> norm_num [h,L] <;> linarith [hz.1])
  have hchord : (3/100:ℝ)≤aeval z (highChord e) := by
    simp only [highChord,map_add,map_mul,map_sub,aeval_C,aeval_X]
    norm_num [L,h] at hl hr ⊢
    linarith
  have hp : 0≤(z-(L:ℝ))*((h:ℝ)-z)*aeval z (highQB e) :=
    mul_nonneg (mul_nonneg (by norm_num [L]; linarith [hz.1])
      (by norm_num [h]; linarith [hz.2])) hq.le
  have he := congrArg (fun f : ℚ[X] => aeval z f) (high_B_chord_identity e)
  simp only [map_add,map_mul,map_sub,aeval_C,aeval_X] at he
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.TwoPositive.Certificate
