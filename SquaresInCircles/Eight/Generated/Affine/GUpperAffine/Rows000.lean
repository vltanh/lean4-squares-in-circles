module

public import SquaresInCircles.Eight.Generated.Affine.GUpperAffine.Context
public meta import SquaresInCircles.Eight.Certificates.Check

/-!
# Eight squares: rows 0 to 8956 of the affine table `GUpperAffine`

Each part of 200 rows passes `checkRows`, evaluated by the kernel.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.GUpperAffine
open Arithmetic

set_option maxRecDepth 100000

/- Rows 0 to 8956, in parts of 200. -/
checked_rows parts000 using ctx from "../../../../../data/eight/affine/G_UPPER_AFFINE.rows" 1 8958 by 200

end SquaresInCircles.Eight.Generated.Affine.GUpperAffine
