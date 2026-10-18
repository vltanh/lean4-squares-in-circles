module

public import SquaresInCircles.Eight.Generated.Affine.HLowerAffine.Data

/-! The angle coverage for the source arcs 0 to 255, checked by `decide +kernel`. -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.HLowerAffine
open Arithmetic

set_option maxRecDepth 100000

theorem cover_0 : coverBlock coverCtx table 0 42 0 0 chunks = true := by
  decide +kernel

theorem cover_1 : coverBlock coverCtx table 42 11 11 68 chunks = true := by
  decide +kernel

theorem cover_2 : coverBlock coverCtx table 53 14 28 1 chunks = true := by
  decide +kernel

theorem cover_3 : coverBlock coverCtx table 67 23 44 166 chunks = true := by
  decide +kernel

theorem cover_4 : coverBlock coverCtx table 90 17 57 52 chunks = true := by
  decide +kernel

theorem cover_5 : coverBlock coverCtx table 107 13 63 88 chunks = true := by
  decide +kernel

theorem cover_6 : coverBlock coverCtx table 120 32 79 62 chunks = true := by
  decide +kernel

theorem cover_7 : coverBlock coverCtx table 152 25 97 105 chunks = true := by
  decide +kernel

theorem cover_8 : coverBlock coverCtx table 177 15 114 41 chunks = true := by
  decide +kernel

theorem cover_9 : coverBlock coverCtx table 192 19 128 58 chunks = true := by
  decide +kernel

theorem cover_10 : coverBlock coverCtx table 211 23 145 56 chunks = true := by
  decide +kernel

theorem cover_11 : coverBlock coverCtx table 234 22 159 192 chunks = true := by
  decide +kernel

end SquaresInCircles.Eight.Generated.Affine.HLowerAffine
