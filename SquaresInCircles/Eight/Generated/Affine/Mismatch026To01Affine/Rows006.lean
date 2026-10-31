module

public import SquaresInCircles.Eight.Generated.Affine.Mismatch026To01Affine.Context
public meta import SquaresInCircles.Eight.Certificates.Check

/-!
# Eight squares: rows 60000 to 69999 of the affine table `Mismatch026To01Affine`

Each part of 200 rows passes `checkRows`, evaluated by the kernel.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.Mismatch026To01Affine
open Arithmetic

set_option maxRecDepth 100000

/- Rows 60000 to 69999, in parts of 200. -/
checked_rows parts006 using ctx from "../../../../../data/eight/affine/MISMATCH_026_TO_01_AFFINE.rows" 60001 70001 by 200

end SquaresInCircles.Eight.Generated.Affine.Mismatch026To01Affine
