module

public import SquaresInCircles.Eight.Generated.Affine.GUpperAffine.Data

/-! The angle coverage for the source arcs 0 to 121, checked by `decide +kernel`. -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.GUpperAffine
open Arithmetic

set_option maxRecDepth 100000

theorem cover_0 : coverBlock coverCtx table 0 48 0 0 chunks = true := by
  decide +kernel

theorem cover_1 : coverBlock coverCtx table 48 33 11 160 chunks = true := by
  decide +kernel

theorem cover_2 : coverBlock coverCtx table 81 40 28 9 chunks = true := by
  decide +kernel

theorem cover_3 : coverBlock coverCtx table 121 1 44 79 chunks = true := by
  decide +kernel

end SquaresInCircles.Eight.Generated.Affine.GUpperAffine
