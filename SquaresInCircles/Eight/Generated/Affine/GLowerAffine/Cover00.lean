module

public import SquaresInCircles.Eight.Generated.Affine.GLowerAffine.Data

/-! The angle coverage for the source arcs 0 to 113, checked by `decide +kernel`. -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.GLowerAffine
open Arithmetic

set_option maxRecDepth 100000

theorem cover_0 : coverBlock coverCtx table 0 51 0 0 chunks = true := by
  decide +kernel

theorem cover_1 : coverBlock coverCtx table 51 36 15 87 chunks = true := by
  decide +kernel

theorem cover_2 : coverBlock coverCtx table 87 27 30 12 chunks = true := by
  decide +kernel

end SquaresInCircles.Eight.Generated.Affine.GLowerAffine
