module

public import SquaresInCircles.Eight.Generated.Affine.TLowerAffine.Context
public meta import SquaresInCircles.Eight.IntRows

/-! Rows 40000 to 41713 of the table, checked by `decide +kernel`, 200 rows a theorem. -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.TLowerAffine
open Arithmetic

set_option maxRecDepth 100000

noncomputable def rows004_0 : List AffineRow :=
  nat_rows% "../../../../../data/eight/affine/T_LOWER_AFFINE.rows" 40001 40201 ↦
    AffineRow.ofData

theorem rows004_0_check : checkRows ctx rows004_0 = true := by decide +kernel

noncomputable def rows004_1 : List AffineRow :=
  nat_rows% "../../../../../data/eight/affine/T_LOWER_AFFINE.rows" 40201 40401 ↦
    AffineRow.ofData

theorem rows004_1_check : checkRows ctx rows004_1 = true := by decide +kernel

noncomputable def rows004_2 : List AffineRow :=
  nat_rows% "../../../../../data/eight/affine/T_LOWER_AFFINE.rows" 40401 40601 ↦
    AffineRow.ofData

theorem rows004_2_check : checkRows ctx rows004_2 = true := by decide +kernel

noncomputable def rows004_3 : List AffineRow :=
  nat_rows% "../../../../../data/eight/affine/T_LOWER_AFFINE.rows" 40601 40801 ↦
    AffineRow.ofData

theorem rows004_3_check : checkRows ctx rows004_3 = true := by decide +kernel

noncomputable def rows004_4 : List AffineRow :=
  nat_rows% "../../../../../data/eight/affine/T_LOWER_AFFINE.rows" 40801 41001 ↦
    AffineRow.ofData

theorem rows004_4_check : checkRows ctx rows004_4 = true := by decide +kernel

noncomputable def rows004_5 : List AffineRow :=
  nat_rows% "../../../../../data/eight/affine/T_LOWER_AFFINE.rows" 41001 41201 ↦
    AffineRow.ofData

theorem rows004_5_check : checkRows ctx rows004_5 = true := by decide +kernel

noncomputable def rows004_6 : List AffineRow :=
  nat_rows% "../../../../../data/eight/affine/T_LOWER_AFFINE.rows" 41201 41401 ↦
    AffineRow.ofData

theorem rows004_6_check : checkRows ctx rows004_6 = true := by decide +kernel

noncomputable def rows004_7 : List AffineRow :=
  nat_rows% "../../../../../data/eight/affine/T_LOWER_AFFINE.rows" 41401 41601 ↦
    AffineRow.ofData

theorem rows004_7_check : checkRows ctx rows004_7 = true := by decide +kernel

noncomputable def rows004_8 : List AffineRow :=
  nat_rows% "../../../../../data/eight/affine/T_LOWER_AFFINE.rows" 41601 41715 ↦
    AffineRow.ofData

theorem rows004_8_check : checkRows ctx rows004_8 = true := by decide +kernel

/-- Rows 40000 to 41713, in parts of 200. -/
noncomputable def parts004 : List (List AffineRow) :=
  [rows004_0, rows004_1, rows004_2, rows004_3, rows004_4, rows004_5, rows004_6, rows004_7,
   rows004_8]

theorem parts004_check : parts004.all (checkRows ctx) = true := by
  simp only [parts004, List.all_cons, List.all_nil, rows004_0_check, rows004_1_check,
    rows004_2_check, rows004_3_check, rows004_4_check, rows004_5_check, rows004_6_check,
    rows004_7_check, rows004_8_check, Bool.and_true]

end SquaresInCircles.Eight.Generated.Affine.TLowerAffine
