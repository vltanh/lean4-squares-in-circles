module

public import SquaresInCircles.Eight.Generated.Affine.DUpperAffine.Context
public meta import SquaresInCircles.Eight.Certificates.Check

/-!
# Eight squares: rows 10000 to 14212 of the affine table `DUpperAffine`

Each part of 200 rows passes `checkRows`, evaluated by the kernel.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.DUpperAffine
open Arithmetic

set_option maxRecDepth 100000

/- Rows 10000 to 14212, in parts of 200. -/
checked_rows parts001 using ctx from "../../../../../data/eight/affine/D_UPPER_AFFINE.rows" 10001 14214 by 200

end SquaresInCircles.Eight.Generated.Affine.DUpperAffine
