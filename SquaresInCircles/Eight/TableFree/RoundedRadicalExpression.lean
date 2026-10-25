module

public import SquaresInCircles.Eight.TableFree.RoundedBinomialEnclosure

/-!
# Literal expressions for the rounded critical derivative calculation

Uncompiled source. The real formula and the rounded rational model have
the same tree of additions, multiplications and three binomial operations.
The Boolean check records only each constructed model's exact rational
normalization bounds. Its soundness is proved by expression induction.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree.RoundedRadicalExpression
open RoundedTensorEnclosure RoundedBinomialEnclosure

inductive Expression (ι : Type*) where
  | literal (r : ℚ)
  | variable (i : ι)
  | add (a b : Expression ι)
  | neg (a : Expression ι)
  | mul (a b : Expression ι)
  | power (a : Expression ι) (n : ℕ)
  | binomial (e : Exponent) (a : Expression ι)
  deriving DecidableEq

namespace Expression
instance {ι : Type*} : Add (Expression ι) := ⟨.add⟩
instance {ι : Type*} : Neg (Expression ι) := ⟨.neg⟩
instance {ι : Type*} : Sub (Expression ι) := ⟨fun a b => .add a (.neg b)⟩
instance {ι : Type*} : Mul (Expression ι) := ⟨.mul⟩
instance {ι : Type*} : Pow (Expression ι) ℕ := ⟨.power⟩
instance {ι : Type*} (n : ℕ) : OfNat (Expression ι) n := ⟨.literal n⟩
instance {ι : Type*} : Div (Expression ι) := ⟨fun a b => .mul a (.binomial .inverse b)⟩

def value {ι : Type*} (v : ι→ℝ) : Expression ι→ℝ
  | .literal r => r
  | .variable i => v i
  | .add a b => value v a+value v b
  | .neg a => -value v a
  | .mul a b => value v a*value v b
  | .power a n => value v a^n
  | .binomial e a => RoundedBinomialEnclosure.value e (value v a)

def model {ι : Type*} (v : ι→Enclosure) : Expression ι→Enclosure
  | .literal r => constant r
  | .variable i => v i
  | .add a b => RoundedTensorEnclosure.add (model v a) (model v b)
  | .neg a => RoundedTensorEnclosure.neg (model v a)
  | .mul a b => RoundedTensorEnclosure.mul (model v a) (model v b)
  | .power a n => RoundedTensorEnclosure.power (model v a) n
  | .binomial e a => enclose (model v a) e

/-- `Valid` is a conjunction of three rational comparisons. -/
instance (a : Enclosure) (e : Exponent) : Decidable (RoundedBinomialEnclosure.Valid a e) :=
  inferInstanceAs (Decidable (0<RoundedBinomialEnclosure.seed a ∧
    0<RoundedBinomialEnclosure.base a e ∧ RoundedBinomialEnclosure.span a e<19/200))

def safe {ι : Type*} (v : ι→Enclosure) : Expression ι→Bool
  | .literal _ | .variable _ => true
  | .add a b | .mul a b => safe v a && safe v b
  | .neg a | .power a _ => safe v a
  | .binomial e a => safe v a && decide (Valid (model v a) e)

theorem contains {ι : Type*} (e : Expression ι)
    {v : ι→ℝ} {w : ι→Enclosure} {x y : ℝ}
    (hw : ∀i,Contains (w i) x y (v i)) (hx : |x|≤1) (hy : |y|≤1)
    (hs : safe w e=true) : Contains (model w e) x y (value v e) := by
  induction e with
  | literal r => exact contains_constant r hx hy
  | «variable» i => exact hw i
  | add a b ha hb =>
      simp only [safe,Bool.and_eq_true] at hs
      exact contains_add (ha hs.1) (hb hs.2) hx hy
  | neg a ha => exact contains_neg (ha hs) hx hy
  | mul a b ha hb =>
      simp only [safe,Bool.and_eq_true] at hs
      exact contains_mul (ha hs.1) (hb hs.2) hx hy
  | power a n ha => exact contains_power (ha hs) hx hy n
  | binomial e a ha =>
      simp only [safe,Bool.and_eq_true,decide_eq_true_eq] at hs
      exact contains_enclose (ha hs.1) hx hy e hs.2

end Expression
end SquaresInCircles.Eight.TableFree.RoundedRadicalExpression
