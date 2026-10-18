module

public import SquaresInCircles.Eight.Generated.Affine.GUpperAffine.Rows000

/-! All rows of the table. -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.GUpperAffine
open Arithmetic

set_option maxRecDepth 100000

/-- The rows in parts of 200, in natural numbers, sorted by source, target, axis and half. -/
noncomputable def chunks : List (List AffineRow) :=
  parts000

/-- All rows. -/
noncomputable def data : List AffineRow := chunks.flatten

theorem data_check : checkRows ctx data = true := by
  simp only [data, chunks, checkRows_flatten, List.all_append, parts000_check, Bool.and_true]

end SquaresInCircles.Eight.Generated.Affine.GUpperAffine
