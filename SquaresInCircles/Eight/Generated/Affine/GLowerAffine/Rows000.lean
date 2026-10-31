module

public import SquaresInCircles.Eight.Generated.Affine.GLowerAffine.Context
public meta import SquaresInCircles.Eight.Certificates.Check

/-!
# Eight squares: rows 0 to 8249 of the affine table `GLowerAffine`

Each part of 200 rows passes `checkRows`, evaluated by the kernel.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.GLowerAffine
open Arithmetic

set_option maxRecDepth 100000

/- Rows 0 to 8249, in parts of 200. -/
checked_rows parts000 using ctx from "../../../../../data/eight/affine/G_LOWER_AFFINE.rows" 1 8251 by 200

end SquaresInCircles.Eight.Generated.Affine.GLowerAffine
