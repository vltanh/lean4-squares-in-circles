module

public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Context
public meta import SquaresInCircles.Eight.Certificates.Check

/-!
# Eight squares: rows 70000 to 79999 of the affine table `Mismatch015To001Affine`

Each part of 200 rows passes `checkRows`, evaluated by the kernel.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine
open Arithmetic

set_option maxRecDepth 100000

/- Rows 70000 to 79999, in parts of 200. -/
checked_rows parts007 using ctx from "../../../../../data/eight/affine/MISMATCH_015_TO_001_AFFINE.rows" 70001 80001 by 200

end SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine
