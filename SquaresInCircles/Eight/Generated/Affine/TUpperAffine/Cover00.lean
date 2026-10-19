module

public import SquaresInCircles.Eight.Generated.Affine.TUpperAffine.Data

/-! The angle coverage for the source arcs 0 to 101, checked by `decide +kernel`. -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.TUpperAffine
open Arithmetic

set_option maxRecDepth 100000

theorem cover_0 : coverBlock coverCtx table false 0 47 0 0 chunks = true := by
  decide +kernel

theorem cover_1 : coverBlock coverCtx table false 47 55 14 159 chunks = true := by
  decide +kernel

end SquaresInCircles.Eight.Generated.Affine.TUpperAffine
