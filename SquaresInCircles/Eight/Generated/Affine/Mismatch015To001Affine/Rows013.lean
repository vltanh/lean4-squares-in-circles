module

public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Context
public meta import SquaresInCircles.Eight.IntRows

/-!
# Eight squares: rows 130000 to 130197 of the affine table `Mismatch015To001Affine`

Each part of 200 rows passes `checkRows`, evaluated by the kernel.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine
open Arithmetic

set_option maxRecDepth 100000

noncomputable def rows013_0 : List AffineRow :=
  nat_rows% "../../../../../data/eight/affine/MISMATCH_015_TO_001_AFFINE.rows" 130001 130199 ↦
    AffineRow.ofData

theorem rows013_0_check : checkRows ctx rows013_0 = true := by decide +kernel

/-- Rows 130000 to 130197, in parts of 200. -/
noncomputable def parts013 : List (List AffineRow) :=
  [rows013_0]

theorem parts013_check : parts013.all (checkRows ctx) = true := by
  simp only [parts013, List.all_cons, List.all_nil, rows013_0_check, Bool.and_true]

end SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine
