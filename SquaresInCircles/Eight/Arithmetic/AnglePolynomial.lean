module

public import SquaresInCircles.Eight.Arithmetic.TargetSupport
public import SquaresInCircles.Eight.Arithmetic.Bernstein
public import SquaresInCircles.Eight.Arithmetic.ScalarExpr
public import SquaresInCircles.Eight.Arithmetic.ClosedCover

/-!
# Eight squares: the angle of a row

On an edge with the quarter `k` the angle between the frames is `φ = k π / 2 + δ`, with a small
frame difference `δ`. A row of an affine table treats one sign of `δ`, its half, and writes
`δ = ± u` with `u ≥ 0`, so that `φ = k π / 2 ± u` (`phi`, with the sign `signQ`).
`CoreRow.lean`, `RowCheck.lean` and `AffineCoverage.lean` write the angles of the rows in this
form.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.Arithmetic
namespace AnglePolynomial

/-- The sign of a half: `1` on the positive half, `-1` on the negative half. -/
def signQ (positiveHalf : Bool) : ℚ := if positiveHalf then 1 else -1

/-- The angle `k π / 2 ± u` of the quarter `k` and a half. -/
def phi (quarter : ℕ) (positiveHalf : Bool) (u : ℝ) : ℝ :=
  (quarter : ℝ)*Real.pi/2+(signQ positiveHalf : ℝ)*u

end AnglePolynomial
end SquaresInCircles.Eight.Arithmetic
