module

public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Context
public meta import SquaresInCircles.Eight.Certificates.Check

/-!
# Eight squares: rows 80000 to 87117 of the affine table `Mismatch01To015Affine`

Each part of 200 rows passes `checkRows`, evaluated by the kernel.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine
open Arithmetic

set_option maxRecDepth 100000

/- Rows 80000 to 87117, in parts of 200. -/
checked_rows parts008 using ctx from "../../../../../data/eight/affine/MISMATCH_01_TO_015_AFFINE.rows" 80001 87119 by 200

end SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine
