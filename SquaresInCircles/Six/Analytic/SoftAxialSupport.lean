import SquaresInCircles.Six.Analytic.OwnWingProfileSharpening

/-!
# A smooth support bound near the axis

The far-corner disk gives `a + (31/100)(|b| + b²) ≤ rho0`. For a force `(U, V)`
with `U ≥ 7/5` and `|V| ≤ U/2`, the support of the square is then at most
`rho0 U + V²/12`: the transverse force costs a quadratic term, which vanishes on
the axis. The proof is one completed square.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma soft_axial_square (x y : ℝ) :
    (217/500)*x^2-(19/50)*x*y+y^2/12 =
      (217/500)*(x-(95/217)*y)^2+y^2/6510 := by
  ring

/-- For `U ≥ 7/5` and `|V| ≤ U/2`, `U a + V b ≤ rho0 U + V²/12`. -/
theorem soft_axial_support {a b U V : ℝ} (hc : ContainedChart a |b|)
    (hU : 7/5 ≤ U) (hV : |V| ≤ U/2) :
    U*a+V*b ≤ rho0*U+V^2/12 := by
  have hU0 : 0 ≤ U := by linarith
  have hrad := radial_transverse_quadratic hc
  have hm := mul_nonneg hU0
    (show 0 ≤ rho0-a-(31/100)*(|b|+b^2) by linarith)
  have hlinear := mul_nonneg
    (show 0 ≤ (31/100)*U-(31/50)*|V| by linarith [hV]) (abs_nonneg b)
  have hquadratic := mul_nonneg
    (show 0 ≤ (31/100)*U-217/500 by linarith [hU]) (sq_nonneg b)
  have hprod : V*b ≤ |V| *|b| := by
    simpa only [abs_mul] using le_abs_self (V*b)
  have hsq : 0 ≤ (217/500)*|b|^2-(19/50)*|b| *|V|+|V|^2/12 := by
    rw [soft_axial_square]
    positivity
  rw [sq_abs,sq_abs] at hsq
  nlinarith only [hm,hlinear,hquadratic,hprod,hsq]

end SquaresInCircles.Six.Analytic
