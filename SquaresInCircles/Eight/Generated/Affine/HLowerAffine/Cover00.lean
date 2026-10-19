module

public import SquaresInCircles.Eight.Generated.Affine.HLowerAffine.Data

/-! The angle coverage for the source arcs 0 to 277, checked by `decide +kernel`. -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.HLowerAffine
open Arithmetic

set_option maxRecDepth 100000

theorem cover_0 : coverBlock coverCtx table true 0 44 0 0 chunks = true := by
  decide +kernel

theorem cover_1 : coverBlock coverCtx table true 44 12 12 11 chunks = true := by
  decide +kernel

theorem cover_2 : coverBlock coverCtx table true 56 23 29 2 chunks = true := by
  decide +kernel

theorem cover_3 : coverBlock coverCtx table true 79 21 42 129 chunks = true := by
  decide +kernel

theorem cover_4 : coverBlock coverCtx table true 100 13 51 77 chunks = true := by
  decide +kernel

theorem cover_5 : coverBlock coverCtx table true 113 31 62 113 chunks = true := by
  decide +kernel

theorem cover_6 : coverBlock coverCtx table true 144 26 80 34 chunks = true := by
  decide +kernel

theorem cover_7 : coverBlock coverCtx table true 170 20 98 95 chunks = true := by
  decide +kernel

theorem cover_8 : coverBlock coverCtx table true 190 27 112 91 chunks = true := by
  decide +kernel

theorem cover_9 : coverBlock coverCtx table true 217 22 127 171 chunks = true := by
  decide +kernel

theorem cover_10 : coverBlock coverCtx table true 239 25 145 50 chunks = true := by
  decide +kernel

theorem cover_11 : coverBlock coverCtx table true 264 14 158 82 chunks = true := by
  decide +kernel

end SquaresInCircles.Eight.Generated.Affine.HLowerAffine
