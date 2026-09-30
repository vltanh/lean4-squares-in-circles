module
public import SquaresInCircles.Six.Analytic.SoftAxialSupport

@[expose] public section

/-!
# A wider smooth-support cone

For U>=33/20 and |V|<=3U/5, the radial-transverse quadratic gives
  U*a+V*b <= rho0*U+(3/25)*V^2.
The proof is one completed square with positive rational remainder. This
slightly wider cone accommodates the negative cardinal-S angles without a
support-branch subdivision. Compilation remains unverified.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma wide_axial_square (x y : ℝ) :
    (1023/2000)*x^2-(29/60)*x*y+(3/25)*y^2 =
      (1023/2000)*(x-(1450/3069)*y)^2+(5359/920700)*y^2 := by
  ring

theorem soft_axial_support_wide {a b U V : ℝ} (hc : ContainedChart a |b|)
    (hU : 33/20 ≤ U) (hV : |V| ≤ (3/5)*U) :
    U*a+V*b ≤ rho0*U+(3/25)*V^2 := by
  have hU0 : 0 ≤ U := by linarith
  have hrad := radial_transverse_quadratic hc
  have hm := mul_nonneg hU0
    (show 0 ≤ rho0-a-(31/100)*(|b|+b^2) by linarith)
  have hlinear := mul_nonneg
    (show 0 ≤ (31/100)*U-(31/60)*|V| by linarith [hV]) (abs_nonneg b)
  have hquadratic := mul_nonneg
    (show 0 ≤ (31/100)*U-1023/2000 by linarith [hU]) (sq_nonneg b)
  have hprod : V*b ≤ |V|*|b| := by
    simpa only [abs_mul] using le_abs_self (V*b)
  have hsq : 0 ≤ (1023/2000)*|b|^2-(29/60)*|b|*|V|+(3/25)*|V|^2 := by
    rw [wide_axial_square]
    positivity
  rw [sq_abs,sq_abs] at hsq
  nlinarith only [hm,hlinear,hquadratic,hprod,hsq]

end SquaresInCircles.Six.Analytic
