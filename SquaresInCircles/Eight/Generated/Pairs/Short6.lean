module

public import SquaresInCircles.Eight.Generated.Pairs.Short6.Rows000
public meta import SquaresInCircles.Eight.PairData

/-! # The pair table `Short6`

Each of its 153 rows passes `checkRow`, so it satisfies its claim; the labels of its 16 arcs
pass `labelsCheck`; the trees of its 54 problems pass `problemsCheck`. So every problem holds. -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Pairs.Short6
open Arithmetic Arithmetic.PairCover

set_option maxRecDepth 100000

/-- All rows, in the order the trees consume them. -/
def data : List AffineRow :=
  chunk000

theorem data_check : checkRows ctx data = true := by
  simp only [data, checkRows_append, chunk000_check, Bool.and_true]

theorem all_row_claims : ∀ x ∈ data, (x.toTableRow table ctx.den).Claim table :=
  fun x hx => checkRow_claim ctx_valid (checkRows_sound data_check x hx)

/-- The trees of the halves of the problems, in order. -/
def trees : List PairTree := pair_trees% "../../../../data/eight/pairs/short_6.trees"

theorem trees_check : problemsCheck table ctx specs problems trees data = true := by
  decide +kernel

theorem sound : ∀ P ∈ problems, P.Holds table.radius ctx.den :=
  table_sound ctx_valid labels_check all_row_claims trees_check

end SquaresInCircles.Eight.Generated.Pairs.Short6
