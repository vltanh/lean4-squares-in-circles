import SquaresInCircles.Six.Analytic.PairTaylorApprox
import SquaresInCircles.Six.Stress.Support

/-!
# Perturbed lengths and sums of roots

Errors of at most `e` in the coordinates of a plane vector raise its length by
at most `2e`. A sum `√X + √Y` lies below `E` when `X + Y < E²` and
`4XY < (E² - X - Y)²`, by squaring twice.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.PairTaylor
open Stress

lemma sum_difference {a b A B e f : ℝ}
    (ha : |a-A|≤e) (hb : |b-B|≤f) : |(a+b)-(A+B)|≤e+f := by
  have h := abs_add_le (a-A) (b-B)
  have he : (a+b)-(A+B)=(a-A)+(b-B) := by ring
  rw [he]
  linarith

lemma sub_difference {a b A B e f : ℝ}
    (ha : |a-A|≤e) (hb : |b-B|≤f) : |(a-b)-(A-B)|≤e+f := by
  have h := abs_add_le (a-A) (-(b-B))
  rw [abs_neg] at h
  have he : (a-b)-(A-B)=(a-A)+-(b-B) := by ring
  rw [he]
  linarith

/-- Errors of at most `e` in the coordinates raise the length of a vector by at
most `2e`. -/
theorem length_le_of_coordinate_errors {x y X Y e : ℝ}
    (he : 0≤e) (hx : |x-X|≤e) (hy : |y-Y|≤e) :
    Real.sqrt (x^2+y^2)≤Real.sqrt (X^2+Y^2)+2*e := by
  let L := Real.sqrt (X^2+Y^2)
  have hL0 : 0≤L := Real.sqrt_nonneg _
  have hLsq : L^2=X^2+Y^2 := Real.sq_sqrt (by positivity)
  have hX : |X|≤L := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg Y]
  have hY : |Y|≤L := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg X]
  have hdx := pow_le_pow_left₀ (abs_nonneg (x-X)) hx 2
  have hdy := pow_le_pow_left₀ (abs_nonneg (y-Y)) hy 2
  rw [sq_abs] at hdx hdy
  have hdotX : X*(x-X)≤L*e := by
    calc
      _≤|X*(x-X)| := le_abs_self _
      _=|X| *|x-X| := abs_mul _ _
      _≤L*e := mul_le_mul hX hx (abs_nonneg _) hL0
  have hdotY : Y*(y-Y)≤L*e := by
    calc
      _≤|Y*(y-Y)| := le_abs_self _
      _=|Y| *|y-Y| := abs_mul _ _
      _≤L*e := mul_le_mul hY hy (abs_nonneg _) hL0
  have hnorm : x^2+y^2≤(L+2*e)^2 := by nlinarith [sq_nonneg e]
  have hroot := Real.sq_sqrt (show 0≤x^2+y^2 by positivity)
  have hroot0 := Real.sqrt_nonneg (x^2+y^2)
  by_contra! hbad
  have hp := mul_pos (sub_pos.mpr hbad)
    (show 0<Real.sqrt (x^2+y^2)+(L+2*e) by linarith)
  nlinarith

/-- `√X + √Y < E` when `X + Y < E²` and `4XY < (E² - X - Y)²`. -/
theorem two_root_sum_lt {E X Y : ℝ}
    (hE : 0<E) (hX : 0≤X) (hY : 0≤Y)
    (hsum : X+Y<E^2) (hdisc : 4*X*Y<(E^2-X-Y)^2) :
    Real.sqrt X+Real.sqrt Y<E := by
  have hx := Real.sq_sqrt hX
  have hy := Real.sq_sqrt hY
  have hx0 := Real.sqrt_nonneg X
  have hy0 := Real.sqrt_nonneg Y
  by_contra! hbad
  have hp := mul_nonneg (sub_nonneg.mpr hbad)
    (show 0≤Real.sqrt X+Real.sqrt Y+E by linarith)
  have hd : E^2-X-Y≤2*Real.sqrt X*Real.sqrt Y := by nlinarith
  have hn : 0≤E^2-X-Y := by linarith
  have hs := pow_le_pow_left₀ hn hd 2
  have hprod : (2*Real.sqrt X*Real.sqrt Y)^2=4*X*Y := by
    calc
      _=4*(Real.sqrt X)^2*(Real.sqrt Y)^2 := by ring
      _=_ := by rw [hx,hy]
  rw [hprod] at hs
  linarith

lemma scaled_root_eq {A X : ℝ} (hA : 0≤A) (hX : 0≤X) :
    A*Real.sqrt X=Real.sqrt (A^2*X) := by
  have hx := Real.sq_sqrt hX
  have hprod : (A*Real.sqrt X)^2=A^2*X := by
    rw [mul_pow,hx]
  rw [← hprod,Real.sqrt_sq (mul_nonneg hA (Real.sqrt_nonneg X))]

/-- The same test for `A √X + B √Y` with `A, B ≥ 0`. -/
theorem scaled_two_roots_lt {E A B X Y : ℝ}
    (hE : 0<E) (hA : 0≤A) (hB : 0≤B) (hX : 0≤X) (hY : 0≤Y)
    (hsum : A^2*X+B^2*Y<E^2)
    (hdisc : 4*(A^2*X)*(B^2*Y)<(E^2-A^2*X-B^2*Y)^2) :
    A*Real.sqrt X+B*Real.sqrt Y<E := by
  rw [scaled_root_eq hA hX,scaled_root_eq hB hY]
  exact two_root_sum_lt hE (mul_nonneg (sq_nonneg A) hX)
    (mul_nonneg (sq_nonneg B) hY) hsum hdisc

end SquaresInCircles.Six.Analytic.PairTaylor
