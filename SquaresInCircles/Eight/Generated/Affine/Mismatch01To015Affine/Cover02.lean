module

public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Data

/-! The angle coverage for the source arcs 331 to 334, checked by `decide +kernel`. -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine
open Arithmetic

set_option maxRecDepth 100000

theorem cover_24 : coverBlock coverCtx table true 331 4 432 15 chunks = true := by
  decide +kernel

end SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine
