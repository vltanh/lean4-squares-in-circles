import SquaresInCircles.Seven.Labels
import SquaresInCircles.Seven.Construction
import SquaresInCircles.Common.DiskSupport

/-!
# The support of an admissible square

Bounds for `√3`, and the support function of the closed square of an admissible
state, bounded below by the distance of its centre from the disk centre.
-/
noncomputable section
namespace SquaresInCircles.Seven

lemma sqrt_three_bounds : (173 : ℝ)/100 < Real.sqrt 3 ∧ Real.sqrt 3 < 1733/1000 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  constructor <;> nlinarith [Real.sqrt_nonneg (3 : ℝ)]

/-- The centre of an admissible square is within `√3 - 1/2` of the disk centre,
so its support in every direction is at least `1 - √3 > -37/50`. -/
lemma support_lower {a b : ℝ} (h : Admissible a |b|) (z : ℝ) :
    -37/50 < support a b z := by
  have hc : a^2+b^2 ≤ (Real.sqrt 3-1/2)^2 := h.center_sq_le.trans_eq (by norm_num [targetSq])
  linarith [support_ge (by linarith [sqrt_three_bounds.1]) hc z,sqrt_three_bounds.2]

end SquaresInCircles.Seven
