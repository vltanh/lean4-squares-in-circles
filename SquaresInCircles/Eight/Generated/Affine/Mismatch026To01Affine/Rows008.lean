module

public import SquaresInCircles.Eight.Generated.Affine.Mismatch026To01Affine.Context
public meta import SquaresInCircles.Eight.Certificates.Check

/-!
# Eight squares: rows 80000 to 89999 of the affine table `Mismatch026To01Affine`

Each part of 200 rows passes `checkRows`, evaluated by the kernel.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.Mismatch026To01Affine
open Arithmetic

set_option maxRecDepth 100000

/- Rows 80000 to 89999, in parts of 200. -/
checked_rows parts008 using ctx from "../../../../../data/eight/affine/MISMATCH_026_TO_01_AFFINE.rows" 80001 90001 by 200

end SquaresInCircles.Eight.Generated.Affine.Mismatch026To01Affine
