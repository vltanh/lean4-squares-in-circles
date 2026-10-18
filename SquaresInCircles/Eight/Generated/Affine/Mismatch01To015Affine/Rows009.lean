module

public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Context
public meta import SquaresInCircles.Eight.IntRows

/-! Rows 90000 to 92067 of the table, checked by `decide +kernel`, 200 rows a theorem. -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine
open Arithmetic

set_option maxRecDepth 100000

noncomputable def rows009_0 : List AffineRow :=
  nat_rows% "../../../../../data/eight/affine/MISMATCH_01_TO_015_AFFINE.rows" 90001 90201 ↦
    AffineRow.ofData

theorem rows009_0_check : checkRows ctx rows009_0 = true := by decide +kernel

noncomputable def rows009_1 : List AffineRow :=
  nat_rows% "../../../../../data/eight/affine/MISMATCH_01_TO_015_AFFINE.rows" 90201 90401 ↦
    AffineRow.ofData

theorem rows009_1_check : checkRows ctx rows009_1 = true := by decide +kernel

noncomputable def rows009_2 : List AffineRow :=
  nat_rows% "../../../../../data/eight/affine/MISMATCH_01_TO_015_AFFINE.rows" 90401 90601 ↦
    AffineRow.ofData

theorem rows009_2_check : checkRows ctx rows009_2 = true := by decide +kernel

noncomputable def rows009_3 : List AffineRow :=
  nat_rows% "../../../../../data/eight/affine/MISMATCH_01_TO_015_AFFINE.rows" 90601 90801 ↦
    AffineRow.ofData

theorem rows009_3_check : checkRows ctx rows009_3 = true := by decide +kernel

noncomputable def rows009_4 : List AffineRow :=
  nat_rows% "../../../../../data/eight/affine/MISMATCH_01_TO_015_AFFINE.rows" 90801 91001 ↦
    AffineRow.ofData

theorem rows009_4_check : checkRows ctx rows009_4 = true := by decide +kernel

noncomputable def rows009_5 : List AffineRow :=
  nat_rows% "../../../../../data/eight/affine/MISMATCH_01_TO_015_AFFINE.rows" 91001 91201 ↦
    AffineRow.ofData

theorem rows009_5_check : checkRows ctx rows009_5 = true := by decide +kernel

noncomputable def rows009_6 : List AffineRow :=
  nat_rows% "../../../../../data/eight/affine/MISMATCH_01_TO_015_AFFINE.rows" 91201 91401 ↦
    AffineRow.ofData

theorem rows009_6_check : checkRows ctx rows009_6 = true := by decide +kernel

noncomputable def rows009_7 : List AffineRow :=
  nat_rows% "../../../../../data/eight/affine/MISMATCH_01_TO_015_AFFINE.rows" 91401 91601 ↦
    AffineRow.ofData

theorem rows009_7_check : checkRows ctx rows009_7 = true := by decide +kernel

noncomputable def rows009_8 : List AffineRow :=
  nat_rows% "../../../../../data/eight/affine/MISMATCH_01_TO_015_AFFINE.rows" 91601 91801 ↦
    AffineRow.ofData

theorem rows009_8_check : checkRows ctx rows009_8 = true := by decide +kernel

noncomputable def rows009_9 : List AffineRow :=
  nat_rows% "../../../../../data/eight/affine/MISMATCH_01_TO_015_AFFINE.rows" 91801 92001 ↦
    AffineRow.ofData

theorem rows009_9_check : checkRows ctx rows009_9 = true := by decide +kernel

noncomputable def rows009_10 : List AffineRow :=
  nat_rows% "../../../../../data/eight/affine/MISMATCH_01_TO_015_AFFINE.rows" 92001 92069 ↦
    AffineRow.ofData

theorem rows009_10_check : checkRows ctx rows009_10 = true := by decide +kernel

/-- Rows 90000 to 92067, in parts of 200. -/
noncomputable def parts009 : List (List AffineRow) :=
  [rows009_0, rows009_1, rows009_2, rows009_3, rows009_4, rows009_5, rows009_6, rows009_7,
   rows009_8, rows009_9, rows009_10]

theorem parts009_check : parts009.all (checkRows ctx) = true := by
  simp only [parts009, List.all_cons, List.all_nil, rows009_0_check, rows009_1_check,
    rows009_2_check, rows009_3_check, rows009_4_check, rows009_5_check, rows009_6_check,
    rows009_7_check, rows009_8_check, rows009_9_check, rows009_10_check, Bool.and_true]

theorem parts009_length : (parts009.map List.length).sum = 2068 := by decide +kernel

end SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine
