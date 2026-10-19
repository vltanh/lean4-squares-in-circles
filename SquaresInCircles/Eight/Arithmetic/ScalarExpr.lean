module

public import SquaresInCircles.Eight.Arithmetic.Interval

/-!
# Rational interval expression certificates

The expression itself is embedded in Lean.  Square-root nodes carry rational
brackets, whose squared endpoint comparisons are included in `Valid`.
Positive-denominator division is similarly an explicit checked condition.
The interpreter's theorem proves enclosure of the real expression for every
real input in the declared box; no sampled-value or imported Boolean premise
occurs in that theorem.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.Arithmetic

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
