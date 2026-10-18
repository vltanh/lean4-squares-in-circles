module

public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Data

/-! The angle coverage for the source arcs 310 to 334, checked by `decide +kernel`. -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine
open Arithmetic

set_option maxRecDepth 100000

theorem cover_24 : coverBlock coverCtx table 310 10 422 83 chunks = true := by
  decide +kernel

theorem cover_25 : coverBlock coverCtx table 320 14 444 12 chunks = true := by
  decide +kernel

theorem cover_26 : coverBlock coverCtx table 334 1 459 116 chunks = true := by
  decide +kernel

end SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine
