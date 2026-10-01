import SquaresInCircles.Six.Analytic.OwnWingProfileSharpening

/-!
# Support of a force near the axis

For a square in the disk the far-corner inequality gives
`a + (31/100)|b| ≤ rho0`. So a force `(U, V)` with `U ≥ 0` and
`|V| ≤ (31/100) U` does work at most `rho0 U` on the centre:
`U a + V b ≤ rho0 U`.
-/
noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

/-- A force in the cone `|V| ≤ (31/100) U` has support at most `rho0 U`. -/
theorem axial_cone_support {a b U V : ℝ} (hc : ContainedChart a |b|)
    (hU : 0 ≤ U) (hV : |V| ≤ (31/100)*U) :
    U*a+V*b ≤ rho0*U := by
  have hrad := radial_transverse_quadratic hc
  have hp := mul_nonneg hU
    (show 0 ≤ rho0-a-(31/100)*|b| by nlinarith [sq_nonneg b])
  have hv := mul_le_mul_of_nonneg_right hV (abs_nonneg b)
  have hm : V*b ≤ |V| *|b| := by
    simpa only [abs_mul] using le_abs_self (V*b)
  nlinarith only [hp,hv,hm]

end SquaresInCircles.Six.Analytic
