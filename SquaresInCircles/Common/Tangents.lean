import SquaresInCircles.Common.Basic

/-!
# Contact tangents and the octagon

The tangent-plus-remainder identity for the farthest-vertex function `phi`
turns the curved constraint `phi a b ≤ K` into a linear one at every point of
`phi = K`, strict away from the point of tangency. The octagon `P8` keeps the
radial sweep of five squares disjoint from the other squares.
-/
noncomputable section
namespace SquaresInCircles

/-- Exact tangent-plus-remainder identity, valid at every contact point. -/
theorem tangent_identity (a b u v : ℝ) :
    phi a b - phi u v =
      2*(u+1/2)*(a-u) + 2*(v+1/2)*(b-v) + (a-u)^2 + (b-v)^2 := by
  unfold phi; ring

theorem tangent_le {a b u v R2 : ℝ} (h : phi a b ≤ R2) (hc : phi u v = R2) :
    2*(u+1/2)*(a-u) + 2*(v+1/2)*(b-v) ≤ 0 := by
  have hid := tangent_identity a b u v
  linarith [sq_nonneg (a-u), sq_nonneg (b-v)]

/-- The tangent inequality is strict away from the point of tangency. -/
theorem tangent_lt {a b u v R2 : ℝ} (h : phi a b ≤ R2) (hc : phi u v = R2) (ha : a ≠ u) :
    2*(u+1/2)*(a-u) + 2*(v+1/2)*(b-v) < 0 := by
  have hid := tangent_identity a b u v
  linarith [sq_pos_of_ne_zero (sub_ne_zero.mpr ha), sq_nonneg (b-v)]

def P8 (a b : ℝ) : Prop := 3*a+b ≤ 3 ∧ a+3*b ≤ 3

end SquaresInCircles
