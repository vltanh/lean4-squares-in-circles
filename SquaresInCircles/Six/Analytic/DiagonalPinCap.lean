module
public import SquaresInCircles.Six.Analytic.PinWindowBounds

@[expose] public section

/-!
# The diagonal pin cannot lie in the negative west-cap fringe

The cap inequality and the pin's normal-coordinate inequality are combined
with fixed multiplier 1/2. Cauchy--Schwarz bounds the resulting normal
(cos z-1/2,sin z). One explicit Taylor polynomial has positive value at 2/7
and a positive divided difference throughout [2/7,2/5]. This is a single
whole-domain identity, not a mesh, search, or generated endpoint table.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization Normalization.Certificates

private def capPinLower (z : ℝ) : ℝ :=
  -113/1000+(681/1000)*(1-z^2/2)+(1318/1000)*(z-z^3/6)

private def capPinPolynomial (z : ℝ) : ℝ :=
  (capPinLower z)^2-Q0*(1/4+z^2/2)

private def capPinQuotient (z : ℝ) : ℝ :=
  (434281/9000000)*z^5+(10292921/63000000)*z^4-
  (734566943/1764000000)*z^3-(7816758227/6174000000)*z^2-
  (9443354093/21609000000)*z+103795758019/75631500000

lemma cap_pin_polynomial_positive {z : ℝ} (hz : 2/7 ≤ z ∧ z ≤ 2/5) :
    0 < capPinPolynomial z := by
  have hz0 : 0 ≤ z := by linarith [hz.1]
  have h2 := pow_le_pow_left₀ hz0 hz.2 2
  have h3 := pow_le_pow_left₀ hz0 hz.2 3
  have h4 := pow_nonneg hz0 4
  have h5 := pow_nonneg hz0 5
  have hD : 0 < capPinQuotient z := by
    dsimp [capPinQuotient]
    nlinarith only [hz.2,h2,h3,h4,h5]
  have hid : capPinPolynomial z=410796053/211768200000+(z-2/7)*capPinQuotient z := by
    dsimp [capPinPolynomial,capPinLower,capPinQuotient,Q0]
    ring
  have hp := mul_nonneg (sub_nonneg.mpr hz.1) hD.le
  rw [hid]
  linarith

lemma cap_pin_lower_nonneg {z : ℝ} (hz : 2/7 ≤ z ∧ z ≤ 2/5) : 0 ≤ capPinLower z := by
  have hz0 : 0 ≤ z := by linarith [hz.1]
  have h2 := pow_le_pow_left₀ hz0 hz.2 2
  have h3 := mul_le_mul_of_nonneg_right h2 hz0
  dsimp [capPinLower]
  nlinarith only [hz0,h2,h3]

/-- A west-cardinal D helper has t>-2/7, a stronger bound than the broad D window. -/
theorem diagonal_west_cap_lower {a b t H : ℝ} (h : ContainedChart a |b|)
    (ht : |t| < 2/5) (hH : coreRadius ≤ H)
    (hcap : H+angularWidth t ≤ centerX t a b)
    (hpin : openSquare (orientedSquare (Real.pi+t) a b) (fixedPin 3)) : -2/7 < t := by
  by_contra! htlo
  let z := -t
  have hz : 2/7 ≤ z ∧ z ≤ 2/5 := by
    dsimp [z]
    have hb := abs_lt.mp ht
    constructor <;> linarith [hb.1]
  have hz0 : 0 ≤ z := by linarith [hz.1]
  have hc0 : 0 ≤ Real.cos z := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Real.pi_pos],by linarith [hz.2,Real.pi_gt_d2]⟩
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hz0 (by linarith [hz.2,Real.pi_gt_d2])
  let A := a+1/2
  let B := b+1/2
  let f := A*(Real.cos z-1/2)+B*Real.sin z
  have hnormal := (abs_lt.mp hpin.1).1
  rw [fixedPin_eq_polar,pinDirection,pin_localX] at hnormal
  have hangle : 5*Real.pi/4-(Real.pi+t)=Real.pi/4+z := by dsimp [z]; ring
  rw [hangle,Real.cos_add,Real.cos_pi_div_four,Real.sin_pi_div_four] at hnormal
  have hrel : t=-z := by dsimp [z]; ring
  rw [hrel] at hcap
  dsimp [angularWidth,centerX] at hcap
  rw [Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg hc0,abs_of_nonneg hs0] at hcap
  have hL : H-1/2+(1-(9/20)*(Real.sqrt 2/2))*Real.cos z+
      (1+(9/20)*(Real.sqrt 2/2))*Real.sin z ≤ f := by
    dsimp [f,A,B]
    nlinarith only [hcap,hnormal]
  have hrlo : (707:ℝ)/1000 ≤ Real.sqrt 2/2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num),Real.sqrt_nonneg (2:ℝ)]
  have hrhi : Real.sqrt 2/2 ≤ (708:ℝ)/1000 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num),Real.sqrt_nonneg (2:ℝ)]
  have hcCoeff := mul_le_mul_of_nonneg_right
    (show (681:ℝ)/1000 ≤ 1-(9/20)*(Real.sqrt 2/2) by linarith) hc0
  have hsCoeff := mul_le_mul_of_nonneg_right
    (show (1318:ℝ)/1000 ≤ 1+(9/20)*(Real.sqrt 2/2) by linarith) hs0
  have hcTaylor := Real.one_sub_sq_div_two_le_cos (x := z)
  have hsTaylor := Real.sin_ge_sub_cube hz0
  have hlower : capPinLower z ≤ f := by
    dsimp [capPinLower]
    nlinarith [coreRadius_gt_387_1000]
  have hbox : A^2+B^2 ≤ Q0 := by
    have hdiff := (h.containment)
    have hb := le_abs_self b
    have hsq := sq_abs b
    dsimp [A,B]
    nlinarith
  have hu := Real.sin_sq_add_cos_sq z
  have hnorm : (Real.cos z-1/2)^2+Real.sin z^2=5/4-Real.cos z := by nlinarith
  have hn0 : 0 ≤ 5/4-Real.cos z := by linarith [Real.cos_le_one z]
  have hmul := mul_le_mul_of_nonneg_right hbox hn0
  have hcs : f^2+(A*Real.sin z-B*(Real.cos z-1/2))^2=
      (A^2+B^2)*(5/4-Real.cos z) := by
    dsimp [f]
    linear_combination (A^2+B^2)*hu
  have hfupper : f^2 ≤ Q0*(1/4+z^2/2) := by
    have hQ : 0 ≤ Q0 := Q0_pos.le
    have htaylor := mul_le_mul_of_nonneg_left
      (show 5/4-Real.cos z ≤ 1/4+z^2/2 by linarith) hQ
    nlinarith [sq_nonneg (A*Real.sin z-B*(Real.cos z-1/2))]
  have hslower := mul_nonneg (sub_nonneg.mpr hlower)
    (show 0 ≤ f+capPinLower z by linarith [cap_pin_lower_nonneg hz])
  have hpositive := cap_pin_polynomial_positive hz
  dsimp [capPinPolynomial] at hpositive
  nlinarith

end SquaresInCircles.Six.Analytic
