module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic

/-!
# Positivity from a quadratic lower bound

For a polynomial of degree at most six, expand at a point `a` and divide the
remainder by `(x-a)²`. The resulting quartic is bounded below on `[0,1]` by
writing it as a constant plus nonnegative multiples of
`x`, `x(1-x)`, `x²(1-x)` and `x²(1-x²)` (`quartic_lower`).

If the lower bound is `m > 0`, completing the square proves positivity from
`f'(a)² < 4 m f(a)` (`sextic_positive`). No subdivision of the interval is needed.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Arithmetic.PolynomialBounds

def quartic (q : Fin 5 → ℝ) (x : ℝ) : ℝ :=
  q 0 + q 1*x + q 2*x^2 + q 3*x^3 + q 4*x^4

theorem quartic_lower {q : Fin 5 → ℝ} {m x : ℝ}
    (hx : 0 ≤ x ∧ x ≤ 1)
    (h : m ≤ q 0 ∧ 0 ≤ q 1+q 2+q 3+q 4 ∧ q 2+q 3+q 4 ≤ 0 ∧ q 3 ≤ 0 ∧ q 4 ≤ 0) :
    m ≤ quartic q x := by
  have h1 : 0 ≤ 1-x := by linarith [hx.2]
  have h2 : 0 ≤ 1-x^2 := by
    nlinarith [mul_nonneg hx.1 h1]
  have hR := mul_nonneg h.2.1 hx.1
  have hS := mul_nonneg (mul_nonneg (neg_nonneg.mpr h.2.2.1) hx.1) h1
  have hA := mul_nonneg (mul_nonneg (neg_nonneg.mpr h.2.2.2.1) (sq_nonneg x)) h1
  have hB := mul_nonneg (mul_nonneg (neg_nonneg.mpr h.2.2.2.2) (sq_nonneg x)) h2
  have he : quartic q x = q 0 + (q 1+q 2+q 3+q 4)*x -
      (q 2+q 3+q 4)*x*(1-x) - q 3*x^2*(1-x) - q 4*x^2*(1-x^2) := by
    dsimp [quartic]
    ring
  nlinarith only [he, h.1, hR, hS, hA, hB]

def sextic (p : Fin 7 → ℝ) (x : ℝ) : ℝ :=
  p 0 + p 1*x + p 2*x^2 + p 3*x^3 + p 4*x^4 + p 5*x^5 + p 6*x^6

def slope (p : Fin 7 → ℝ) (a : ℝ) : ℝ :=
  p 1+2*p 2*a+3*p 3*a^2+4*p 4*a^3+5*p 5*a^4+6*p 6*a^5

def remainder (p : Fin 7 → ℝ) (a : ℝ) : Fin 5 → ℝ :=
  ![p 2+2*a*p 3+3*a^2*p 4+4*a^3*p 5+5*a^4*p 6,
    p 3+2*a*p 4+3*a^2*p 5+4*a^3*p 6,
    p 4+2*a*p 5+3*a^2*p 6, p 5+2*a*p 6, p 6]

theorem expansion (p : Fin 7 → ℝ) (a x : ℝ) :
    sextic p x = sextic p a + slope p a*(x-a) + (x-a)^2*quartic (remainder p a) x := by
  simp only [sextic, slope, quartic, remainder, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  ring

theorem sextic_positive {p : Fin 7 → ℝ} {a m x : ℝ}
    (hm : 0 < m) (hx : 0 ≤ x ∧ x ≤ 1)
    (h : m ≤ remainder p a 0 ∧ 0 ≤ remainder p a 1+remainder p a 2+remainder p a 3+remainder p a 4 ∧
      remainder p a 2+remainder p a 3+remainder p a 4 ≤ 0 ∧ remainder p a 3 ≤ 0 ∧ remainder p a 4 ≤ 0)
    (hs : (slope p a)^2 < 4*m*sextic p a) : 0 < sextic p x := by
  have hq := quartic_lower hx h
  have hl := mul_nonneg (sq_nonneg (x-a)) (sub_nonneg.mpr hq)
  have he := expansion p a x
  have hsq := sq_nonneg (2*m*(x-a)+slope p a)
  have hprod := mul_nonneg (by linarith : 0 ≤ 4*m) (by
    nlinarith only [hl, he] : 0 ≤ sextic p x-(sextic p a+slope p a*(x-a)+m*(x-a)^2))
  nlinarith only [hs, hsq, hprod, hm]

end SquaresInCircles.Eight.Arithmetic.PolynomialBounds
