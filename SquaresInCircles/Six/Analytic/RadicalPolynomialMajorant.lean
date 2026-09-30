module
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic

@[expose] public section

/-!
# A denominator-free analytic square-root majorant

For a>0, multiply the cubic Taylor upper bound for sqrt(1+b^2/a^2) by a^6.
No series theorem or interval check is needed: positivity of the numerator and
its squared error are the two explicit identities below. This allows a
continuously varying stress weight to be handled by one ordinary polynomial.
Compilation and kernel acceptance remain unverified.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.RadicalPolynomialMajorant

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

/-- A global exact inequality, not the result of evaluating a certificate. -/
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
