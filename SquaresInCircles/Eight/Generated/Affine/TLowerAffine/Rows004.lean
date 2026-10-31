module

public import SquaresInCircles.Eight.Generated.Affine.TLowerAffine.Context
public meta import SquaresInCircles.Eight.Certificates.Check

/-!
# Eight squares: rows 40000 to 41713 of the affine table `TLowerAffine`

Each part of 200 rows passes `checkRows`, evaluated by the kernel.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.TLowerAffine
open Arithmetic

set_option maxRecDepth 100000

/- Rows 40000 to 41713, in parts of 200. -/
checked_rows parts004 using ctx from "../../../../../data/eight/affine/T_LOWER_AFFINE.rows" 40001 41715 by 200

end SquaresInCircles.Eight.Generated.Affine.TLowerAffine
