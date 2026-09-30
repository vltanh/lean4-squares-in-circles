import SquaresInCircles.Six.Analytic.EndpointReduction
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Analytic minorant for the diagonal vertex branch

Put X = |(w+s)/2| and Y = |(w-s)/2|. The helper rectangle implies
X+Y <= 11/25. The vertex branch has 29/100 <= |delta| <= 2/7+X.

The expression below is concave in |delta|, so only its two endpoints are
needed. At the upper endpoint, its dependence on Y is minimized at
min(X,11/25-X). This is why there are exactly two cases, separated at X=11/50:
they are the two sides of a diamond, not a numerical subdivision.

Second- and third-order Taylor inequalities give two explicit quartics. The
quartic chord identity proves their positivity from their endpoints. No box
evaluator, exhaustive search, or list of certified cells occurs in this file.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic

/-- Lower bound after dividing the diagonal remainder by its positive scale. -/
def vertexMinorant (x y t : ℝ) : ℝ :=
  (37 / 100) * max x y + (39 / 50) * y +
    (3 / 2 + y / 2) * Real.cos t + (1 / 2 + y / 2) * Real.sin t -
    (1689 / 1000) * (1 + y) + 111 / 100 - 1

private def penalty (t : ℝ) : ℝ :=
  909 / 1000 - (Real.cos t + Real.sin t) / 2

private def base (t : ℝ) : ℝ :=
  (3 / 2) * Real.cos t + (1 / 2) * Real.sin t - 1579 / 1000

private lemma minorant_decomposition (x y t : ℝ) :
    vertexMinorant x y t = base t + (37 / 100) * max x y - penalty t * y := by
  dsimp [vertexMinorant, base, penalty]
  ring

private lemma penalty_bounds {t : ℝ} (ht : 2 / 7 ≤ t ∧ t ≤ 3 / 4) :
    0 ≤ penalty t ∧ penalty t ≤ 37 / 100 := by
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have hsq := mul_nonneg (sub_nonneg.mpr ht.2)
    (show 0 ≤ 3 / 4 + t by linarith)
  have hcoef : 0 ≤ 1 / 2 - t / 2 - t ^ 2 / 6 := by nlinarith [ht.2]
  have hprod := mul_nonneg ht0 hcoef
  have hs := Real.sin_ge_sub_cube ht0
  have hc := Real.one_sub_sq_div_two_le_cos (x := t)
  have hwidthLower : 1 + t / 2 ≤ Real.cos t + Real.sin t := by
    nlinarith only [hprod, hs, hc]
  have hwidthUpper : Real.cos t + Real.sin t ≤ 3 / 2 := by
    nlinarith [Real.sin_sq_add_cos_sq t, sq_nonneg (Real.cos t - Real.sin t)]
  dsimp [penalty]
  constructor <;> linarith [hwidthLower, hwidthUpper, ht.1]

private lemma base_at_left_positive : 0 < base (29 / 100) := by
  have hs := Real.sin_ge_sub_cube (x := (29 : ℝ) / 100) (by norm_num)
  have hc := Real.one_sub_sq_div_two_le_cos (x := (29 : ℝ) / 100)
  dsimp [base]
  nlinarith only [hs, hc]

/-- First boundary: the minimizing value of Y is X. -/
private def smallBoundary (x : ℝ) : ℝ :=
  (3 / 2 + x / 2) * (1 - (2 / 7 + x) ^ 2 / 2) +
    (1 / 2 + x / 2) * ((2 / 7 + x) - (2 / 7 + x) ^ 3 / 6) -
    1579 / 1000 - (539 / 1000) * x

/-- Second boundary: the minimizing value of Y is 11/25-X. -/
private def largeBoundary (x : ℝ) : ℝ :=
  (43 / 25 - x / 2) * (1 - (2 / 7 + x) ^ 2 / 2) +
    (18 / 25 - x / 2) * ((2 / 7 + x) - (2 / 7 + x) ^ 3 / 6) -
    24737 / 12500 + (1279 / 1000) * x

private lemma smallBoundary_positive {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 11 / 50) :
    0 < smallBoundary x := by
  have hid : smallBoundary x =
      quartic (-19 / 280) (2227 / 7000) (-5 / 28) (-13 / 42) (-1 / 12) (2 / 7 + x) := by
    dsimp [smallBoundary, quartic]
    ring
  rw [hid]
  apply quartic_positive_of_chord (l := (2 : ℝ) / 7) (u := (177 : ℝ) / 350)
  · norm_num
  · constructor <;> linarith [hx.1, hx.2]
  · norm_num [quartic]
  · norm_num [quartic]
  · have hT : 0 ≤ 2 / 7 + x := by linarith [hx.1]
    nlinarith [sq_nonneg (2 / 7 + x)]

private lemma largeBoundary_positive {x : ℝ} (hx : 11 / 50 ≤ x ∧ x ≤ 11 / 25) :
    0 < largeBoundary x := by
  have hid : largeBoundary x =
      quartic (-21067 / 43750) (11493 / 7000) (-501 / 350)
        (223 / 2100) (1 / 12) (2 / 7 + x) := by
    dsimp [largeBoundary, quartic]
    ring
  rw [hid]
  apply quartic_positive_of_chord (l := (177 : ℝ) / 350) (u := (127 : ℝ) / 175)
  · norm_num
  · constructor <;> linarith [hx.1, hx.2]
  · norm_num [quartic]
  · norm_num [quartic]
  · have hT0 : 0 ≤ 2 / 7 + x := by linarith [hx.1]
    have hT1 : 2 / 7 + x ≤ 3 / 4 := by linarith [hx.2]
    have hsq := mul_nonneg (sub_nonneg.mpr hT1)
      (show 0 ≤ 3 / 4 + (2 / 7 + x) by linarith)
    nlinarith

private lemma minorant_at_left {x y : ℝ} (hy : 0 ≤ y) :
    0 < vertexMinorant x y (29 / 100) := by
  have hp := penalty_bounds (t := (29 : ℝ) / 100) (by constructor <;> norm_num)
  have hM := mul_nonneg (show (0 : ℝ) ≤ 37 / 100 by norm_num)
    (sub_nonneg.mpr (le_max_right x y))
  have hY := mul_nonneg (sub_nonneg.mpr hp.2) hy
  rw [minorant_decomposition]
  nlinarith only [base_at_left_positive, hM, hY]

private lemma minorant_at_right {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hdiamond : x + y ≤ 11 / 25) :
    0 < vertexMinorant x y (2 / 7 + x) := by
  let t := 2 / 7 + x
  have hxb : x ≤ 11 / 25 := by linarith
  have ht : 2 / 7 ≤ t ∧ t ≤ 3 / 4 := by
    dsimp [t]
    constructor <;> linarith
  have hp := penalty_bounds ht
  have hc := Real.one_sub_sq_div_two_le_cos (x := t)
  have hs := Real.sin_ge_sub_cube (show 0 ≤ t by linarith [ht.1])
  rw [minorant_decomposition]
  change 0 < base t + (37 / 100) * max x y - penalty t * y
  by_cases hsmall : x ≤ 11 / 50
  · have hM1 := mul_nonneg (sub_nonneg.mpr hp.2) (sub_nonneg.mpr (le_max_left x y))
    have hM2 := mul_nonneg hp.1 (sub_nonneg.mpr (le_max_right x y))
    have hC := mul_le_mul_of_nonneg_left hc
      (show 0 ≤ 3 / 2 + x / 2 by linarith)
    have hS := mul_le_mul_of_nonneg_left hs
      (show 0 ≤ 1 / 2 + x / 2 by linarith)
    have hpositive := smallBoundary_positive ⟨hx, hsmall⟩
    have hid : smallBoundary x =
        (3 / 2 + x / 2) * (1 - t ^ 2 / 2) +
        (1 / 2 + x / 2) * (t - t ^ 3 / 6) - 1579 / 1000 - (539 / 1000) * x := rfl
    rw [hid] at hpositive
    dsimp [base, penalty] at *
    nlinarith only [hM1, hM2, hC, hS, hpositive]
  · have hM := mul_nonneg (show (0 : ℝ) ≤ 37 / 100 by norm_num)
      (sub_nonneg.mpr (le_max_left x y))
    have hY := mul_nonneg hp.1 (show 0 ≤ 11 / 25 - x - y by linarith)
    have hC := mul_le_mul_of_nonneg_left hc
      (show 0 ≤ 43 / 25 - x / 2 by linarith)
    have hS := mul_le_mul_of_nonneg_left hs
      (show 0 ≤ 18 / 25 - x / 2 by linarith)
    have hpositive := largeBoundary_positive ⟨(lt_of_not_ge hsmall).le, hxb⟩
    have hid : largeBoundary x =
        (43 / 25 - x / 2) * (1 - t ^ 2 / 2) +
        (18 / 25 - x / 2) * (t - t ^ 3 / 6) - 24737 / 12500 + (1279 / 1000) * x := rfl
    rw [hid] at hpositive
    dsimp [base, penalty] at *
    nlinarith only [hM, hY, hC, hS, hpositive]

/-- The entire three-variable minorant is positive by concavity and the two
geometrically forced boundary polynomials. The interval includes its endpoints. -/
theorem vertexMinorant_positive {x y t : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hdiamond : x + y ≤ 11 / 25)
    (ht : 29 / 100 ≤ t ∧ t ≤ 2 / 7 + x) :
    0 < vertexMinorant x y t := by
  have hleft := minorant_at_left (x := x) hy
  have hright := minorant_at_right hx hy hdiamond
  have hbound := trig_lower_of_endpoints
    (A := 3 / 2 + y / 2) (B := 1 / 2 + y / 2)
    (C := (1689 / 1000) * (1 + y) - 111 / 100 + 1 -
      (37 / 100) * max x y - (39 / 50) * y)
    (l := (29 : ℝ) / 100) (u := 2 / 7 + x)
    (by linarith) (by linarith) (by norm_num)
    (by linarith [Real.pi_gt_d2]) ht
    (by dsimp [vertexMinorant] at hleft; linarith)
    (by dsimp [vertexMinorant] at hright; linarith)
  dsimp [vertexMinorant]
  linarith

end SquaresInCircles.Six.Analytic
