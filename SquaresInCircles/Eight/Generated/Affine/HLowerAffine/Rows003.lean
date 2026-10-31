module

public import SquaresInCircles.Eight.Generated.Affine.HLowerAffine.Context
public meta import SquaresInCircles.Eight.Certificates.Check

/-!
# Eight squares: rows 30000 to 35665 of the affine table `HLowerAffine`

Each part of 200 rows passes `checkRows`, evaluated by the kernel.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.HLowerAffine
open Arithmetic

set_option maxRecDepth 100000

/- Rows 30000 to 35665, in parts of 200. -/
checked_rows parts003 using ctx from "../../../../../data/eight/affine/H_LOWER_AFFINE.rows" 30001 35667 by 200

end SquaresInCircles.Eight.Generated.Affine.HLowerAffine
