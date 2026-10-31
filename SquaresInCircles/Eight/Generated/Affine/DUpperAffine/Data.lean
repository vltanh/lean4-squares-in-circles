module

public import SquaresInCircles.Eight.Generated.Affine.DUpperAffine.Rows000
public import SquaresInCircles.Eight.Generated.Affine.DUpperAffine.Rows001

/-!
# Eight squares: the rows of the affine table `DUpperAffine`

All rows of the table, as the list of their parts; together they pass `checkRows`.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.DUpperAffine
open Arithmetic

set_option maxRecDepth 100000

/-- The rows in parts of 200, in natural numbers, sorted by source, target, axis and half. -/
noncomputable def chunks : List (List AffineRow) :=
  parts000 ++ parts001

/-- All rows. -/
noncomputable def data : List AffineRow := chunks.flatten

theorem data_check : checkRows ctx data = true := by
  simp only [data, chunks, checkRows_flatten, List.all_append, parts000_check, parts001_check,
    Bool.and_true]

end SquaresInCircles.Eight.Generated.Affine.DUpperAffine
