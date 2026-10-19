module

public import SquaresInCircles.Eight.Generated.Affine.DUpperAffine.Data

/-! The angle coverage for the source arcs 0 to 198, checked by `decide +kernel`. -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.DUpperAffine
open Arithmetic

set_option maxRecDepth 100000

theorem cover_0 : coverBlock coverCtx table true 0 52 0 0 chunks = true := by
  decide +kernel

theorem cover_1 : coverBlock coverCtx table true 52 38 16 111 chunks = true := by
  decide +kernel

theorem cover_2 : coverBlock coverCtx table true 90 49 28 7 chunks = true := by
  decide +kernel

theorem cover_3 : coverBlock coverCtx table true 139 47 45 152 chunks = true := by
  decide +kernel

theorem cover_4 : coverBlock coverCtx table true 186 13 59 43 chunks = true := by
  decide +kernel

end SquaresInCircles.Eight.Generated.Affine.DUpperAffine
