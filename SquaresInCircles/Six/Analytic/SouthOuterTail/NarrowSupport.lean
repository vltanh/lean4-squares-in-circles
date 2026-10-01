import SquaresInCircles.Six.Analytic.OwnWingProfileSharpening

/-!
# The support of a nearly radial force

A square in the disk of squared radius `Q0`, with local centre `(a, b)`, has
`U a + V b ≤ ρ0 U + 1/160` for every force `(U, V)` with `3/5 ≤ U ≤ 7/10` and
`|V| ≤ 2U/5`, which is sharper than the far-vertex bound for such forces. It
follows from the bound `a + (31/100)(|b| + b²) ≤ ρ0` of the far corner and a
completed square in `|b|` and `|V|`.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.SouthOuterTail
open Normalization

lemma narrow_support_square (x y : ℝ) :
    (93/500)*x^2-(9/40)*x*y+(7/100)*y^2 =
      (93/500)*(x-(75/124)*y)^2+(97/49600)*y^2 := by
  ring

/-- The support of a nearly radial force exceeds `ρ0 U` by at most `1/160`. -/
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
