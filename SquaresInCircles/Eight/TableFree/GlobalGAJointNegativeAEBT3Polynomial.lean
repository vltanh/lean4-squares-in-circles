module

public import SquaresInCircles.Eight.TableFree.GlobalGAJointNegativeAEBT3PolynomialData

/-!
# Six whole-interval BT3 numerator certificates

Uncompiled transcription of Section 4 of the BT3 scalar companion.
The low row decreases by one Chebyshev derivative bound. The middle
row uses its displayed centered quadratic reserve. The high row has
a positive polynomial quotient at the actual D support transition.
-/

@[expose] public section
noncomputable section
open Set Polynomial
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAEBT3.Certificate
open PowerTailBounds

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_certificate (e : Endpoint) :
    WholeIntervalPolynomial.centered 0 (3/20) (numerator .low e).derivative=
      WholeIntervalPolynomial.expansion (degree .low e-1)
        (WholeIntervalPolynomial.centered 0 (3/20) (numerator .low e).derivative) ∧
    WholeIntervalPolynomial.upperOn (degree .low e-1) 0 (3/20) (numerator .low e).derivative<lowSlope e ∧
    lowValue e<(numerator .low e).eval (3/20) := by
  cases e <;> decide

theorem low_antitone (e : Endpoint) :
    AntitoneOn (fun z : ℝ => aeval z (numerator .low e)) (Icc (0:ℝ) (3/20)) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun z _ => (CenteredMonomialBounds.aeval_hasDerivAt (numerator .low e) z).continuousAt.continuousWithinAt)
    (fun z _ => CenteredMonomialBounds.aeval_hasDerivAt (numerator .low e) z)
  intro z hz
  have hb := (WholeIntervalPolynomial.interval_bounds
    (by norm_num : (0:ℚ)<3/20) (low_certificate e).1 (Ioo_subset_Icc_self hz)).2
  have hr : (WholeIntervalPolynomial.upperOn (degree .low e-1) 0 (3/20)
      (numerator .low e).derivative:ℝ)<(lowSlope e:ℝ) := by
    exact_mod_cast (low_certificate e).2.1
  have hs : (lowSlope e:ℝ)<0 := by cases e <;> norm_num [lowSlope]
  linarith

theorem low_positive (e : Endpoint) {z : ℝ} (hz : z∈Icc (0:ℝ) (3/20)) :
    (lowValue e:ℝ)<aeval z (numerator .low e) := by
  have hm := low_antitone e hz (show (3/20:ℝ)∈Icc (0:ℝ) (3/20) by norm_num) hz.2
  have hr : (lowValue e:ℝ)<aeval (3/20:ℝ) (numerator .low e) := by
    have hh : (lowValue e:ℝ)<((numerator .low e).eval (3/20):ℝ) := by
      exact_mod_cast (low_certificate e).2.2
    simpa only [←NonnegativeTotals.Certificate.eval_rat] using hh
  exact hr.trans_le hm

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem middle_certificate (e : Endpoint) :
    middleShift e=C ((middleShift e).coeff 0)+C ((middleShift e).coeff 1)*X+
      C ((middleShift e).coeff 2)*X^2+tail (middleShift e) 3 (degree .middle e-2) ∧
    middleValue e<(middleShift e).coeff 0 ∧
    |(middleShift e).coeff 1|<middleLinear e ∧
    middleQuadratic e<(middleShift e).coeff 2-
      PowerTailBounds.norm (middleShift e) 3 (degree .middle e-2) (17/200) := by
  cases e <;> decide

theorem middle_positive (e : Endpoint) {z : ℝ} (hz : z∈Icc (3/20:ℝ) (1/4)) :
    (middleReserve e:ℝ)<aeval z (numerator .middle e) := by
  let u : ℝ := z-47/200
  have hu : |u|≤(17/200:ℝ) := by
    apply abs_le.mpr
    dsimp [u]
    exact ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hp := PowerTailBounds.quadratic_lower (middle_certificate e).1 (by norm_num) hu
  have h0 : (middleValue e:ℝ)<((middleShift e).coeff 0:ℝ) := by
    exact_mod_cast (middle_certificate e).2.1
  have h1 : |((middleShift e).coeff 1:ℝ)|<(middleLinear e:ℝ) := by
    exact_mod_cast (middle_certificate e).2.2.1
  have h2 : (middleQuadratic e:ℝ)<((middleShift e).coeff 2:ℝ)-
      (PowerTailBounds.norm (middleShift e) 3 (degree .middle e-2) (17/200):ℝ) := by
    exact_mod_cast (middle_certificate e).2.2.2
  have hlin : -(middleLinear e:ℝ)*|u|≤((middleShift e).coeff 1:ℝ)*u := by
    have hh := mul_le_mul_of_nonneg_right h1.le (abs_nonneg u)
    rw [←abs_mul] at hh
    exact (abs_le.mp hh).1
  have hquad := mul_le_mul_of_nonneg_right h2.le (sq_nonneg u)
  have hm := ChebyshevLeadingBounds.quadratic_min (a:=(middleValue e:ℝ))
    (b:=-(middleLinear e:ℝ)) (x:=|u|)
    (show 0<(middleQuadratic e:ℝ) by cases e <;> norm_num [middleQuadratic])
  have hr : (middleReserve e:ℝ)<(middleValue e:ℝ)-
      (middleLinear e:ℝ)^2/(4*(middleQuadratic e:ℝ)) := by
    cases e <;> norm_num [middleReserve,middleValue,middleLinear,middleQuadratic]
  have hid : aeval u (middleShift e)=aeval z (numerator .middle e) := by
    simp [middleShift,u]
  rw [hid] at hp
  rw [sq_abs] at hm
  nlinarith

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem high_certificate (e : Endpoint) :
    highShift e=C ((highShift e).coeff 0)+X*highQuotient e ∧
    WholeIntervalPolynomial.centered 0 (9/20) (highQuotient e)=
      WholeIntervalPolynomial.expansion (degree .high e-1)
        (WholeIntervalPolynomial.centered 0 (9/20) (highQuotient e)) ∧
    highSlope e<WholeIntervalPolynomial.lowerOn (degree .high e-1) 0 (9/20) (highQuotient e) ∧
    highValue e<(numerator .high e).eval (1/4) := by
  cases e <;> decide

theorem high_positive (e : Endpoint) {z : ℝ} (hz : z∈Icc (1/4:ℝ) (7/10)) :
    (highValue e:ℝ)<aeval z (numerator .high e) := by
  have hu : z-1/4∈Icc (0:ℝ) (9/20) := ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hq := WholeIntervalPolynomial.positive_on_interval
    (by norm_num : (0:ℚ)<9/20) (high_certificate e).2.1 (high_certificate e).2.2.1 hu
  have hq0 : 0≤aeval (z-1/4) (highQuotient e) := by
    have hs : (0:ℝ)<(highSlope e:ℝ) := by cases e <;> norm_num [highSlope]
    linarith
  have hp := mul_nonneg hu.1 hq0
  have hi := congrArg (fun p : ℚ[X] => aeval (z-1/4) p) (high_certificate e).1
  have h0 := congrArg (fun p : ℚ[X] => aeval (0:ℝ) p) (high_certificate e).1
  simp only [map_add,map_mul,aeval_C,aeval_X] at hi h0
  have hbase : (highValue e:ℝ)<aeval (1/4:ℝ) (numerator .high e) := by
    have hh : (highValue e:ℝ)<((numerator .high e).eval (1/4):ℝ) := by
      exact_mod_cast (high_certificate e).2.2.2
    simpa only [←NonnegativeTotals.Certificate.eval_rat] using hh
  simp only [highShift,DirectedPowerBounds.shift_eval] at hi h0
  norm_num at h0
  rw [show (1/4:ℝ)+(z-1/4)=z by ring] at hi
  linarith

theorem numerator_positive (r : Row) (e : Endpoint) {z : ℝ}
    (hz : z∈Icc (left r:ℝ) (right r:ℝ)) : (7/10000:ℝ)<aeval z (numerator r e) := by
  cases r
  · have hh := low_positive e hz
    cases e <;> norm_num [lowValue] at hh ⊢ <;> linarith
  · have hh := middle_positive e hz
    cases e <;> norm_num [middleReserve] at hh ⊢ <;> linarith
  · have hh := high_positive e hz
    cases e <;> norm_num [highValue] at hh ⊢ <;> linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAEBT3.Certificate
