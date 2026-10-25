module

public import SquaresInCircles.Eight.Owners.CenteredMonomialBounds
public import SquaresInCircles.Eight.Frames.High.HighVaryingReferences

/-!
# Eight squares: complete high/high varying support by one quadratic reserve

The full second-derivative lower bound and the
actual value and slope at `4/5` imply the strict bound on `[3/5,19/20]`.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighHighVaryingScalars
open FrameHighHighVaryingCalculus FrameHighHighVaryingReferences

theorem curvature {x : ℝ} (hx : x∈domain) : (1/2:ℝ)<Fdd x :=
  concave_gt_of_endpoints second_concave hx endpoint_curvatures.1 endpoint_curvatures.2

theorem lower {x : ℝ} (hx : x∈Icc (3/5:ℝ) (19/20)) : (9099/10000:ℝ)<F x := by
  have ht := CenteredMonomialBounds.second_derivative_tangent_lower
    (κ := (1/2:ℝ)) (fun z _ => F_deriv z) (fun z _ => Fd_deriv z)
    (fun z hz => (curvature hz).le)
    (show (4/5:ℝ)∈domain by constructor <;> norm_num [domain]) hx
  have hd := abs_lt.mp tangent_slope
  have hs := mul_pos (sub_pos.mpr hd.2)
    (show 0<Fd (4/5)+1/250 by linarith [hd.1])
  nlinarith [tangent_value,sq_nonneg (x-4/5+2*Fd (4/5))]

end SquaresInCircles.Eight.FrameHighHighVaryingScalars
