module
public import SquaresInCircles.Six.Analytic.OwnWingProfileSharpening

@[expose] public section

/-!
# A smooth substitute for an axial/vertex support split

The far-corner disk implies a+(31/100)(|b|+b^2)<=rho0. If U>=7/5 and
|V|<=U/2, its support in direction (U,V) therefore satisfies
  U*a+V*b <= rho0*U+V^2/12.
The extra cost is quadratic in the transverse force, so it vanishes on the
axis. One completed square proves the estimate on the whole force cone;
there is no support-branch or angle-box table.

Compilation and kernel acceptance remain unverified.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma soft_axial_square (x y : ℝ) :
    (217/500)*x^2-(19/50)*x*y+y^2/12 =
      (217/500)*(x-(95/217)*y)^2+y^2/6510 := by
  ring

/-- A universal smooth support bound on a fixed, explicitly justified force cone. -/
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
  have hprod : V*b ≤ |V|*|b| := by
    simpa only [abs_mul] using le_abs_self (V*b)
  have hsq : 0 ≤ (217/500)*|b|^2-(19/50)*|b|*|V|+|V|^2/12 := by
    rw [soft_axial_square]
    positivity
  rw [sq_abs,sq_abs] at hsq
  nlinarith only [hm,hlinear,hquadratic,hprod,hsq]

/-- The transverse penalty can be enlarged without changing the force hypotheses. -/
lemma soft_axial_support_weaken {a b U V K : ℝ} (hc : ContainedChart a |b|)
    (hU : 7/5 ≤ U) (hV : |V| ≤ U/2) (hK : 1/12 ≤ K) :
    U*a+V*b ≤ rho0*U+K*V^2 := by
  have h := soft_axial_support hc hU hV
  have hp := mul_nonneg (show 0 ≤ K-1/12 by linarith) (sq_nonneg V)
  nlinarith only [h,hp]

end SquaresInCircles.Six.Analytic
