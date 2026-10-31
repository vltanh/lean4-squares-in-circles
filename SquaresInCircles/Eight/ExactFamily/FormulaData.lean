module

public import SquaresInCircles.Eight.ExactFamily.Expression
public meta import SquaresInCircles.Eight.ExactFamily.Expression
public meta import Mathlib.Tactic.ToExpr
public meta import Mathlib.Tactic.Eval

/-!
# Caching symbolic formula data

`eval%` computes a formula and elaborates its value to ordinary constructors. It supplies
data only: the derivative identities and every interval bound are proved by the kernel.
-/

public meta section
deriving instance Lean.ToExpr for SquaresInCircles.Eight.ExactFamily.Formula
