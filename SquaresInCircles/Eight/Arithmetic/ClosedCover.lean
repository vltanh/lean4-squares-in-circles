module

public import Mathlib.Tactic
public import SquaresInCircles.Eight.Arithmetic.Interval

/-!
# Eight squares: closed chains and boxes

A list of rational intervals is a closed chain over `[lo, hi]` (`ClosedChain`) when its first
interval starts at or before `lo` and either reaches `hi` or ends at a point `c ≥ lo` from which
the rest of the list is a closed chain over `[c, hi]`; consecutive intervals thus meet at a
common endpoint, and the empty list is a closed chain only over an empty interval (`hi < lo`).
Every point of `[lo, hi]` then lies in an interval of the chain (`ClosedChain.covers`). The chain
condition compares rationals only, and is decidable.

A `QBox n` is a product of `n` rational intervals. `QBox.left` and `QBox.right` cut it at a
rational in one coordinate, and a point of the box on one side of the cut lies in that half
(`QBox.mem_left`, `QBox.mem_right`).

The formulas of `Stationary/` are bounded on such boxes (`Stationary/FixedEval.lean`,
`Stationary/Generated/`).
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.Arithmetic

/-- The intervals cover `[lo, hi]` as a chain: each starts at or before the point reached by
the ones before it, until one reaches `hi`; the empty list covers only an empty interval. -/
def ClosedChain (lo hi : ℚ) : List QInterval → Prop
  | [] => hi < lo
  | I::rest => I.lo ≤ lo ∧ (hi ≤ I.hi ∨ (lo ≤ I.hi ∧ ClosedChain I.hi hi rest))

instance closedChainDecidable (lo hi : ℚ) (xs : List QInterval) :
    Decidable (ClosedChain lo hi xs) := by
  induction xs generalizing lo <;> simp only [ClosedChain] <;> infer_instance

/-- A box: a rational interval for each of `n` coordinates. -/
abbrev QBox (n : ℕ) := Fin n → QInterval

def QBox.Mem {n : ℕ} (b : QBox n) (x : Fin n → ℝ) : Prop :=
  ∀ i, (b i).Mem (x i)

/-- The part of the box where the coordinate `i` is at most `c`. -/
def QBox.left {n : ℕ} (b : QBox n) (i : Fin n) (c : ℚ) : QBox n :=
  Function.update b i ⟨(b i).lo,c⟩

/-- The part of the box where the coordinate `i` is at least `c`. -/
def QBox.right {n : ℕ} (b : QBox n) (i : Fin n) (c : ℚ) : QBox n :=
  Function.update b i ⟨c,(b i).hi⟩

theorem QBox.mem_left {n : ℕ} {b : QBox n} {i : Fin n} {c : ℚ}
    {x : Fin n → ℝ} (hx : b.Mem x) (hi : x i ≤ (c : ℝ)) :
    (b.left i c).Mem x := by
  intro j
  by_cases hji : j = i
  · subst j
    simpa [left,QInterval.Mem] using And.intro (hx i).1 hi
  · simpa [left,Function.update_of_ne hji] using hx j

theorem QBox.mem_right {n : ℕ} {b : QBox n} {i : Fin n} {c : ℚ}
    {x : Fin n → ℝ} (hx : b.Mem x) (hi : (c : ℝ) ≤ x i) :
    (b.right i c).Mem x := by
  intro j
  by_cases hji : j = i
  · subst j
    simpa [right,QInterval.Mem] using And.intro hi (hx i).2
  · simpa [right,Function.update_of_ne hji] using hx j

end SquaresInCircles.Eight.Arithmetic
