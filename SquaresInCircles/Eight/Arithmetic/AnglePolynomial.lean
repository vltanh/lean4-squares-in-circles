module

public import SquaresInCircles.Eight.Arithmetic.TargetSupport
public import SquaresInCircles.Eight.Arithmetic.Bernstein
public import SquaresInCircles.Eight.Arithmetic.ScalarExpr
public import SquaresInCircles.Eight.Arithmetic.ClosedCover

/-!
# The real meaning of the ten one-angle parameters

The two remainder parameters are chosen separately at each angle.  The other
parameters denote fixed algebraic arc endpoints and π.  Their rational boxes
are obtained from the proved scalar-expression evaluator.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.Arithmetic
namespace AnglePolynomial

def signQ (positiveHalf : Bool) : ℚ := if positiveHalf then 1 else -1

def phi (quarter : ℕ) (positiveHalf : Bool) (u : ℝ) : ℝ :=
  (quarter : ℝ)*Real.pi/2+(signQ positiveHalf : ℝ)*u

end AnglePolynomial
end SquaresInCircles.Eight.Arithmetic
