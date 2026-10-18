module

public import SquaresInCircles.Eight.Generated.Affine.TLowerAffine.Data

/-! The angle coverage for the source arcs 258 to 302, checked by `decide +kernel`. -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.TLowerAffine
open Arithmetic

set_option maxRecDepth 100000

theorem cover_12 : coverBlock coverCtx table 258 21 160 100 chunks = true := by
  decide +kernel

theorem cover_13 : coverBlock coverCtx table 279 11 172 195 chunks = true := by
  decide +kernel

theorem cover_14 : coverBlock coverCtx table 290 10 189 133 chunks = true := by
  decide +kernel

theorem cover_15 : coverBlock coverCtx table 300 3 206 21 chunks = true := by
  decide +kernel

end SquaresInCircles.Eight.Generated.Affine.TLowerAffine
