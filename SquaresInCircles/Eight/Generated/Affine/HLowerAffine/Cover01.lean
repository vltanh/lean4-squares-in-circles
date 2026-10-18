module

public import SquaresInCircles.Eight.Generated.Affine.HLowerAffine.Data

/-! The angle coverage for the source arcs 256 to 278, checked by `decide +kernel`. -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.HLowerAffine
open Arithmetic

set_option maxRecDepth 100000

theorem cover_12 : coverBlock coverCtx table 256 14 171 158 chunks = true := by
  decide +kernel

theorem cover_13 : coverBlock coverCtx table 270 9 189 53 chunks = true := by
  decide +kernel

end SquaresInCircles.Eight.Generated.Affine.HLowerAffine
