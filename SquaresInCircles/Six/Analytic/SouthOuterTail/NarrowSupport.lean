import SquaresInCircles.Six.Analytic.OwnWingProfileSharpening

/-!
# A radial support estimate for the final OWN/OWN corner

The far-vertex estimate is unnecessarily large when the diagonal force is
nearly radial. On 3/5 <= U <= 7/10 and |V| <= 2U/5, the far-corner quadratic
instead gives U*a+V*b <= rho0*U+1/160.

The proof is one completed square, with no choice of a numerical support cell.
The cone will be derived from the actual force at the single geometric corner
v=s=11/25; the whole diagonal-angle interval remains intact.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.SouthOuterTail
open Normalization

lemma narrow_support_square (x y : ℝ) :
    (93/500)*x^2-(9/40)*x*y+(7/100)*y^2 =
      (93/500)*(x-(75/124)*y)^2+(97/49600)*y^2 := by
  ring

/-- A uniform smooth bound, derived from the disk rather than a support-branch premise. -/
theorem narrow_support {a b U V : ℝ} (hc : ContainedChart a |b|)
    (hU : 3/5 ≤ U ∧ U ≤ 7/10) (hV : |V| ≤ (2/5)*U) :
    U*a+V*b ≤ rho0*U+1/160 := by
  have hU0 : 0 ≤ U := by linarith [hU.1]
  have hrad := radial_transverse_quadratic hc
  have hm := mul_nonneg hU0
    (show 0 ≤ rho0-a-(31/100)*(|b|+b^2) by linarith)
  have hlinear := mul_nonneg
    (show 0 ≤ (31/100)*U-(31/40)*|V| by linarith [hV]) (abs_nonneg b)
  have hquadratic := mul_nonneg
    (show 0 ≤ (31/100)*U-93/500 by linarith [hU.1]) (sq_nonneg b)
  have hproduct : V*b ≤ |V| *|b| := by
    simpa only [abs_mul] using le_abs_self (V*b)
  have hsq : 0 ≤ (93/500)*|b|^2-(9/40)*|b| *|V|+(7/100)*|V|^2 := by
    rw [narrow_support_square]
    positivity
  rw [sq_abs,sq_abs] at hsq
  have hsoft : U*a+V*b ≤ rho0*U+(7/100)*V^2 := by
    nlinarith only [hm,hlinear,hquadratic,hproduct,hsq]
  have habs : |V| ≤ 7/25 := by linarith [hV,hU.2]
  have hsquare := mul_nonneg (sub_nonneg.mpr habs)
    (show 0 ≤ 7/25+|V| by positivity)
  have hbound : V^2 ≤ (7/25:ℝ)^2 := by
    nlinarith only [hsquare,sq_abs V]
  nlinarith only [hsoft,hbound]

end SquaresInCircles.Six.Analytic.SouthOuterTail
