import SquaresInCircles.Six.Analytic.OwnWingProfileSharpening

/-!
# Axial support without a selected cap branch

The far-corner quadratic implies a+(31/100)|b|<=rho0. Therefore every force
with U>=0 and |V|<=31U/100 has support at most rho0 U. The force-cone
hypothesis is explicit and must be proved by each geometric application.
Compilation and kernel acceptance remain unverified.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

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
