module

public import SquaresInCircles.Eight.TableFree.FrameMidHighVaryingReferences

/-!
# Both varying-multiplier bounds on their full closed intervals

Concavity of the second derivative propagates the two endpoint reserves.
The positive source decreases to its final endpoint.  The negative source
uses one actual tangent and the quadratic reserve from strong convexity.
Both bounds exceed the original strengthened middle/high target.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameMidHighVaryingScalars
open FramePairCalculus FrameMidHighVaryingCalculus FrameMidHighVaryingReferences

theorem positive_curvature {x : ℝ} (hx : x∈domain true) :
    (4/25:ℝ)<Fdd true x := by
  exact concave_gt_of_endpoints (second_concave true) hx
    positive_endpoint_curvature.1 positive_endpoint_curvature.2

theorem negative_curvature {x : ℝ} (hx : x∈domain false) :
    (3/5:ℝ)<Fdd false x := by
  exact concave_gt_of_endpoints (second_concave false) hx
    negative_endpoint_curvature.1 negative_endpoint_curvature.2

theorem positive_slope_monotone : MonotoneOn (Fd true) (domain true) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x _ => (Fd_deriv true x).continuousAt.continuousWithinAt
  · exact fun x _ => Fd_deriv true x
  · exact fun x hx => by linarith [positive_curvature (Ioo_subset_Icc_self hx)]

theorem positive_slope_negative {x : ℝ} (hx : x∈domain true) : Fd true x<0 := by
  have hh := positive_slope_monotone hx (right_mem true) hx.2
  have he : right true=(21/50:ℝ) := rfl
  rw [he] at hh
  linarith [positive_final_slope]

theorem positive_antitone : AntitoneOn (F true) (domain true) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun x _ => (F_deriv true x).continuousAt.continuousWithinAt
  · exact fun x _ => F_deriv true x
  · exact fun x hx => (positive_slope_negative (Ioo_subset_Icc_self hx)).le

theorem positive_lower {x : ℝ} (hx : x∈Icc (1/10:ℝ) (21/50)) :
    (4463/5000:ℝ)<F true x := by
  have hh := positive_antitone hx (right_mem true) hx.2
  change F true (21/50)≤F true x at hh
  linarith [positive_final_value]

theorem negative_tangent_lower {x : ℝ} (hx : x∈domain false) :
    F false (14/25)+Fd false (14/25)*(x-14/25)+(3/10)*(x-14/25)^2≤F false x := by
  have h := CenteredMonomialBounds.second_derivative_tangent_lower
    (κ := (3/5:ℝ)) (fun z _ => F_deriv false z)
    (fun z _ => Fd_deriv false z) (fun z hz => (negative_curvature hz).le)
    (show (14/25:ℝ)∈domain false by constructor <;> norm_num [domain,left,right]) hx
  norm_num at h
  exact h

theorem negative_lower {x : ℝ} (hx : x∈Icc (2/5:ℝ) (3/5)) :
    (4463/5000:ℝ)<F false x := by
  have ht := negative_tangent_lower hx
  have hd := abs_lt.mp negative_tangent_slope
  have hs := mul_pos (sub_pos.mpr hd.2)
    (show 0<Fd false (14/25)+7/5000 by linarith [hd.1])
  have hcomplete := sq_nonneg (x-14/25+(5/3)*Fd false (14/25))
  nlinarith [negative_tangent_value]

theorem lower {i : Bool} {x : ℝ} (hx : x∈domain i) :
    (4463/5000:ℝ)<F i x := by
  cases i
  · exact negative_lower hx
  · exact positive_lower hx

end SquaresInCircles.Eight.TableFree.FrameMidHighVaryingScalars
