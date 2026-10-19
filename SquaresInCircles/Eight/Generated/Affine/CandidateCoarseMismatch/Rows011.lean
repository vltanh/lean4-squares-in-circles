module

public import SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.Context
public meta import SquaresInCircles.Eight.IntRows

/-! Rows 110000 to 110424 of the table, checked by `decide +kernel`, 200 rows a theorem. -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch
open Arithmetic

set_option maxRecDepth 100000

noncomputable def rows011_0 : List AffineRow :=
  nat_rows% "../../../../../data/eight/affine/CANDIDATE_COARSE_MISMATCH.rows" 110001 110201 ↦
    AffineRow.ofData

theorem rows011_0_check : checkRows ctx rows011_0 = true := by decide +kernel

noncomputable def rows011_1 : List AffineRow :=
  nat_rows% "../../../../../data/eight/affine/CANDIDATE_COARSE_MISMATCH.rows" 110201 110401 ↦
    AffineRow.ofData

theorem rows011_1_check : checkRows ctx rows011_1 = true := by decide +kernel

noncomputable def rows011_2 : List AffineRow :=
  nat_rows% "../../../../../data/eight/affine/CANDIDATE_COARSE_MISMATCH.rows" 110401 110426 ↦
    AffineRow.ofData

theorem rows011_2_check : checkRows ctx rows011_2 = true := by decide +kernel

/-- Rows 110000 to 110424, in parts of 200. -/
noncomputable def parts011 : List (List AffineRow) :=
  [rows011_0, rows011_1, rows011_2]

theorem parts011_check : parts011.all (checkRows ctx) = true := by
  simp only [parts011, List.all_cons, List.all_nil, rows011_0_check, rows011_1_check,
    rows011_2_check, Bool.and_true]

end SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch
