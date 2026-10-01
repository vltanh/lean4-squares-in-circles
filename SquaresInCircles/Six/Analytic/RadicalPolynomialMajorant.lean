import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# A polynomial majorant of a square root

For `a ≥ 0`, `a⁵ √(a² + b²) ≤ a⁶ + a⁴b²/2 - a²b⁴/8 + b⁶/16`: the right side is
`a⁶` times the cubic Taylor polynomial of `√(1 + x)` at `x = b²/a²`. It is
nonnegative, being `a⁶ + (b²/16)((b² - a²)² + 7a⁴)`, and its square exceeds
`a¹⁰ (a² + b²)` by `(b⁸/256)((b² - 2a²)² + 16a⁴)`.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.RadicalPolynomialMajorant

/-- `a⁶` times the cubic Taylor polynomial of `√(1 + x)` at `x = b²/a²`. -/
def numerator (a b : ℝ) : ℝ :=
  a^6+(b^2*a^4)/2-(b^4*a^2)/8+b^6/16

lemma positive_form (a b : ℝ) :
    numerator a b=a^6+(b^2/16)*((b^2-a^2)^2+7*a^4) := by
  dsimp [numerator]
  ring

lemma square_error (a b : ℝ) :
    (numerator a b)^2-a^10*(a^2+b^2)=
      (b^8/256)*((b^2-2*a^2)^2+16*a^4) := by
  dsimp [numerator]
  ring

/-- `a⁵ √(a² + b²) ≤ numerator a b` for `a ≥ 0`. -/
theorem scaled_sqrt_upper (a b : ℝ) (ha : 0 ≤ a) :
    a^5*Real.sqrt (a^2+b^2) ≤ numerator a b := by
  have hN : 0 ≤ numerator a b := by rw [positive_form]; positivity
  have hs := Real.sq_sqrt (show 0 ≤ a^2+b^2 by positivity)
  have hid : (a^5*Real.sqrt (a^2+b^2))^2=a^10*(a^2+b^2) := by
    linear_combination a^10*hs
  have he := square_error a b
  have hp : 0 ≤ (b^8/256)*((b^2-2*a^2)^2+16*a^4) := by positivity
  have hu : 0 ≤ a^5*Real.sqrt (a^2+b^2) := by positivity
  nlinarith only [hN,hid,he,hp,hu]

end SquaresInCircles.Six.Analytic.RadicalPolynomialMajorant
