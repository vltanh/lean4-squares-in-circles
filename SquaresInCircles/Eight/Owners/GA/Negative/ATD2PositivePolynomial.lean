module

public import Mathlib.Algebra.Order.Ring.Star
public import SquaresInCircles.Eight.Owners.CircleGeometry
public import SquaresInCircles.Eight.Owners.DirectedPowerBounds
public import SquaresInCircles.Eight.Arithmetic.PolynomialCertificates

/-!
# Eight squares: the two positive-angle quartics

Each quartic is a positive combination of the products `(r - a)^i (b - r)^(4 - i)` on its
interval `[a, b]` (its Bernstein coefficients are positive), which `linarith` finds
(`PU_positive`, `PA_positive`).
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.PositivePolynomial

theorem PU_positive {r : ℝ} (hr : r∈Set.Icc (1/2:ℝ) 1) :
    0<(3/5+(557/1000)*r)^2*(1+r^2+(741/1000)*r)-(1839/1000)^2*r^2 := by
  have h1 : 0≤r-1/2 := sub_nonneg.2 hr.1
  have h2 : 0≤1-r := sub_nonneg.2 hr.2
  linarith [pow_nonneg h1 4,mul_nonneg (pow_nonneg h1 3) h2,
    mul_nonneg (pow_nonneg h1 2) (pow_nonneg h2 2),mul_nonneg h1 (pow_nonneg h2 3),pow_nonneg h2 4]

theorem PA_positive {r : ℝ} (hr : r∈Set.Icc (4/5:ℝ) (27/25:ℝ)) :
    0<(13/12+371/1000+(557/1000)*r)^2*(1+(861/1000)*r^2)-
      qCap*(371/1000+r)^2 := by
  have h1 : 0≤r-4/5 := sub_nonneg.2 hr.1
  have h2 : 0≤27/25-r := sub_nonneg.2 hr.2
  simp only [qCap]
  linarith [pow_nonneg h1 4,mul_nonneg (pow_nonneg h1 3) h2,
    mul_nonneg (pow_nonneg h1 2) (pow_nonneg h2 2),mul_nonneg h1 (pow_nonneg h2 3),pow_nonneg h2 4]

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.PositivePolynomial
