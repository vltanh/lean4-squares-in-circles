module

public import SquaresInCircles.Eight.Arithmetic.Interval

/-!
# Eight squares: interval evaluation of scalar expressions

A `ScalarExpr n` is an expression in `n` real variables built from rational constants, sums,
negatives, products, reciprocals, square roots and powers; a square root, and an `enclose` node
around any subexpression, carries a rational interval, the bracket of its value. `eval` is the
real value of an expression at a point, and `range` its interval value on a box of the variables
(`Interval.lean`), in which a square root or an `enclose` node takes its bracket. `Valid` collects
the side conditions, decided on the rationals: the argument of every reciprocal has an interval
value of positive numbers, every square-root bracket is nonnegative and squares to bounds of the
interval value of its argument, and every `enclose` bracket contains the interval value of its
argument. For a valid expression the value at every point of the box lies in the interval value
(`sound`).

The quantities of the model on the box of parameters (`Stationary/Generated/EqualityBox.lean`)
are bounded with these expressions.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.Arithmetic

/-- An expression in `n` real variables; `sqrt` and `enclose` carry the bracket of their value. -/
inductive ScalarExpr (n : ℕ)
  | const (q : ℚ)
  | var (i : Fin n)
  | add (a b : ScalarExpr n)
  | neg (a : ScalarExpr n)
  | mul (a b : ScalarExpr n)
  | inv (a : ScalarExpr n)
  | sqrt (a : ScalarExpr n) (bracket : QInterval)
  | pow (a : ScalarExpr n) (exponent : ℕ)
  | enclose (a : ScalarExpr n) (bracket : QInterval)

namespace ScalarExpr

def sub {n : ℕ} (a b : ScalarExpr n) : ScalarExpr n := add a (neg b)
def div {n : ℕ} (a b : ScalarExpr n) : ScalarExpr n := mul a (inv b)

/-- The real value of an expression at the point `env`. -/
def eval {n : ℕ} (env : Fin n → ℝ) : ScalarExpr n → ℝ
  | .const q => q
  | .var i => env i
  | .add a b => eval env a + eval env b
  | .neg a => -eval env a
  | .mul a b => eval env a * eval env b
  | .inv a => (eval env a)⁻¹
  | .sqrt a _ => Real.sqrt (eval env a)
  | .pow a k => (eval env a)^k
  | .enclose a _ => eval env a

/-- The interval value of an expression on a box of the variables; a square root or an
`enclose` node takes its bracket. -/
def range {n : ℕ} (boxes : Fin n → QInterval) : ScalarExpr n → QInterval
  | .const q => .point q
  | .var i => boxes i
  | .add a b => (range boxes a).add (range boxes b)
  | .neg a => (range boxes a).neg
  | .mul a b => (range boxes a).mul (range boxes b)
  | .inv a => (range boxes a).inv
  | .sqrt _ bracket => bracket
  | .pow a k => (range boxes a).pow k
  | .enclose _ bracket => bracket

/-- The side conditions of the interval evaluation on a box: positive arguments of the
reciprocals, square-root brackets that square to bounds of their arguments, and `enclose`
brackets that contain the interval values of their arguments. -/
def Valid {n : ℕ} (boxes : Fin n → QInterval) : ScalarExpr n → Prop
  | .const _ => True
  | .var _ => True
  | .add a b => Valid boxes a ∧ Valid boxes b
  | .neg a => Valid boxes a
  | .mul a b => Valid boxes a ∧ Valid boxes b
  | .inv a => Valid boxes a ∧ 0 < (range boxes a).lo
  | .sqrt a J => Valid boxes a ∧ 0 ≤ (range boxes a).lo ∧ 0 ≤ J.lo ∧
      J.lo^2 ≤ (range boxes a).lo ∧ (range boxes a).hi ≤ J.hi^2 ∧ 0 ≤ J.hi
  | .pow a _ => Valid boxes a
  | .enclose a J => Valid boxes a ∧ J.lo ≤ (range boxes a).lo ∧ (range boxes a).hi ≤ J.hi

instance validDecidable {n : ℕ} (boxes : Fin n → QInterval) (e : ScalarExpr n) :
    Decidable (Valid boxes e) := by
  induction e <;> simp only [Valid] <;> infer_instance

/-- The value of a valid expression at every point of the box lies in its interval value. -/
theorem sound {n : ℕ} (boxes : Fin n → QInterval) (e : ScalarExpr n)
    (he : e.Valid boxes) (env : Fin n → ℝ)
    (henv : ∀ i, (boxes i).Mem (env i)) : (e.range boxes).Mem (e.eval env) := by
  induction e with
  | const q => exact QInterval.mem_point q
  | var i => exact henv i
  | add a b ha hb => exact QInterval.mem_add (ha he.1) (hb he.2)
  | neg a ha => exact QInterval.mem_neg (ha he)
  | mul a b ha hb => exact QInterval.mem_mul (ha he.1) (hb he.2)
  | inv a ha => exact QInterval.mem_inv_pos he.2 (ha he.1)
  | sqrt a J ha =>
      exact QInterval.mem_sqrt (ha he.1) he.2.1 he.2.2.1
        he.2.2.2.1 he.2.2.2.2.1 he.2.2.2.2.2
  | pow a k ha => exact QInterval.mem_pow (ha he) k
  | enclose a J ha => exact QInterval.mem_mono (ha he.1) he.2.1 he.2.2

end ScalarExpr
end SquaresInCircles.Eight.Arithmetic
