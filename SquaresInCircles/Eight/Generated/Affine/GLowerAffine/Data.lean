module

public import SquaresInCircles.Eight.Generated.Affine.GLowerAffine.Rows000

/-!
# Eight squares: the rows of the affine table `GLowerAffine`

All rows of the table, as the list of their parts; together they pass `checkRows`.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.GLowerAffine
open Arithmetic

set_option maxRecDepth 100000

/-- The rows in parts of 200, in natural numbers, sorted by source, target, axis and half. -/
noncomputable def chunks : List (List AffineRow) :=
  parts000

/-- All rows. -/
noncomputable def data : List AffineRow := chunks.flatten

theorem data_check : checkRows ctx data = true := by
  simp only [data, chunks, checkRows_flatten, parts000_check]

end SquaresInCircles.Eight.Generated.Affine.GLowerAffine
