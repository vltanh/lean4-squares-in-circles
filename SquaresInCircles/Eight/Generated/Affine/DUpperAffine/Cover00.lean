module

public import SquaresInCircles.Eight.Generated.Affine.DUpperAffine.Data

/-! The angle coverage for the source arcs 0 to 198, checked by `decide +kernel`. -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.DUpperAffine
open Arithmetic

set_option maxRecDepth 100000

theorem cover_0 : coverBlock coverCtx table 0 46 0 0 chunks = true := by
  decide +kernel

theorem cover_1 : coverBlock coverCtx table 46 29 15 93 chunks = true := by
  decide +kernel

theorem cover_2 : coverBlock coverCtx table 75 29 31 16 chunks = true := by
  decide +kernel

theorem cover_3 : coverBlock coverCtx table 104 43 44 154 chunks = true := by
  decide +kernel

theorem cover_4 : coverBlock coverCtx table 147 34 61 13 chunks = true := by
  decide +kernel

theorem cover_5 : coverBlock coverCtx table 181 17 73 128 chunks = true := by
  decide +kernel

theorem cover_6 : coverBlock coverCtx table 198 1 91 122 chunks = true := by
  decide +kernel

end SquaresInCircles.Eight.Generated.Affine.DUpperAffine
