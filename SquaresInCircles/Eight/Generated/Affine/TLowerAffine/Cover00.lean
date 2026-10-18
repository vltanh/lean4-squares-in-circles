module

public import SquaresInCircles.Eight.Generated.Affine.TLowerAffine.Data

/-! The angle coverage for the source arcs 0 to 257, checked by `decide +kernel`. -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.TLowerAffine
open Arithmetic

set_option maxRecDepth 100000

theorem cover_0 : coverBlock coverCtx table 0 45 0 0 chunks = true := by
  decide +kernel

theorem cover_1 : coverBlock coverCtx table 45 18 12 58 chunks = true := by
  decide +kernel

theorem cover_2 : coverBlock coverCtx table 63 10 30 155 chunks = true := by
  decide +kernel

theorem cover_3 : coverBlock coverCtx table 73 22 48 5 chunks = true := by
  decide +kernel

theorem cover_4 : coverBlock coverCtx table 95 19 60 122 chunks = true := by
  decide +kernel

theorem cover_5 : coverBlock coverCtx table 114 14 70 140 chunks = true := by
  decide +kernel

theorem cover_6 : coverBlock coverCtx table 128 16 81 186 chunks = true := by
  decide +kernel

theorem cover_7 : coverBlock coverCtx table 144 23 100 22 chunks = true := by
  decide +kernel

theorem cover_8 : coverBlock coverCtx table 167 23 113 133 chunks = true := by
  decide +kernel

theorem cover_9 : coverBlock coverCtx table 190 24 126 77 chunks = true := by
  decide +kernel

theorem cover_10 : coverBlock coverCtx table 214 21 132 43 chunks = true := by
  decide +kernel

theorem cover_11 : coverBlock coverCtx table 235 23 145 161 chunks = true := by
  decide +kernel

end SquaresInCircles.Eight.Generated.Affine.TLowerAffine
