module

public import SquaresInCircles.Eight.Generated.Affine.TUpperAffine.Context
public meta import SquaresInCircles.Eight.Certificates.Check

/-!
# Eight squares: rows 0 to 6432 of the affine table `TUpperAffine`

Each part of 200 rows passes `checkRows`, evaluated by the kernel.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.TUpperAffine
open Arithmetic

set_option maxRecDepth 100000

/- Rows 0 to 6432, in parts of 200. -/
checked_rows parts000 using ctx from "../../../../../data/eight/affine/T_UPPER_AFFINE.rows" 1 6434 by 200

end SquaresInCircles.Eight.Generated.Affine.TUpperAffine
