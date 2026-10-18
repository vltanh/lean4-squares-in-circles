module

public import SquaresInCircles.Eight.Generated.Affine.HLowerAffine.Context
public meta import SquaresInCircles.Eight.IntRows

/-! Rows 40000 to 40295 of the table, checked by `decide +kernel`, 200 rows a theorem. -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.HLowerAffine
open Arithmetic

set_option maxRecDepth 100000

noncomputable def rows004_0 : List AffineRow :=
  nat_rows% "../../../../../data/eight/affine/H_LOWER_AFFINE.rows" 40001 40201 ↦
    AffineRow.ofData

theorem rows004_0_check : checkRows ctx rows004_0 = true := by decide +kernel

noncomputable def rows004_1 : List AffineRow :=
  nat_rows% "../../../../../data/eight/affine/H_LOWER_AFFINE.rows" 40201 40297 ↦
    AffineRow.ofData

theorem rows004_1_check : checkRows ctx rows004_1 = true := by decide +kernel

/-- Rows 40000 to 40295, in parts of 200. -/
noncomputable def parts004 : List (List AffineRow) :=
  [rows004_0, rows004_1]

theorem parts004_check : parts004.all (checkRows ctx) = true := by
  simp only [parts004, List.all_cons, List.all_nil, rows004_0_check, rows004_1_check, Bool.and_true]

theorem parts004_length : (parts004.map List.length).sum = 296 := by decide +kernel

end SquaresInCircles.Eight.Generated.Affine.HLowerAffine
