module

public import SquaresInCircles.Eight.Generated.Affine.HLowerAffine.Data

/-! The angle coverage for the source arcs 278 to 278, checked by `decide +kernel`. -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.HLowerAffine
open Arithmetic

set_option maxRecDepth 100000

theorem cover_12 : coverBlock coverCtx table true 278 1 177 11 chunks = true := by
  decide +kernel

end SquaresInCircles.Eight.Generated.Affine.HLowerAffine
