module

public import SquaresInCircles.Eight.Generated.Affine.TLowerAffine.Data

/-! The angle coverage for the source arcs 267 to 302, checked by `decide +kernel`. -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.TLowerAffine
open Arithmetic

set_option maxRecDepth 100000

theorem cover_12 : coverBlock coverCtx table false 267 17 163 143 chunks = true := by
  decide +kernel

theorem cover_13 : coverBlock coverCtx table false 284 11 177 150 chunks = true := by
  decide +kernel

theorem cover_14 : coverBlock coverCtx table false 295 8 195 121 chunks = true := by
  decide +kernel

end SquaresInCircles.Eight.Generated.Affine.TLowerAffine
