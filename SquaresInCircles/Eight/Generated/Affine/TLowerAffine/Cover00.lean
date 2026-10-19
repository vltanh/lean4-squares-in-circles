module

public import SquaresInCircles.Eight.Generated.Affine.TLowerAffine.Data

/-!
# Eight squares: the angle coverage of the affine table `TLowerAffine`, source arcs 0 to 266

The walks `coverBlock` over blocks of these source arcs, evaluated by the kernel.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.TLowerAffine
open Arithmetic

set_option maxRecDepth 100000

theorem cover_0 : coverBlock coverCtx table false 0 45 0 0 chunks = true := by
  decide +kernel

theorem cover_1 : coverBlock coverCtx table false 45 18 12 58 chunks = true := by
  decide +kernel

theorem cover_2 : coverBlock coverCtx table false 63 10 30 155 chunks = true := by
  decide +kernel

theorem cover_3 : coverBlock coverCtx table false 73 22 48 5 chunks = true := by
  decide +kernel

theorem cover_4 : coverBlock coverCtx table false 95 19 60 122 chunks = true := by
  decide +kernel

theorem cover_5 : coverBlock coverCtx table false 114 14 70 140 chunks = true := by
  decide +kernel

theorem cover_6 : coverBlock coverCtx table false 128 16 81 186 chunks = true := by
  decide +kernel

theorem cover_7 : coverBlock coverCtx table false 144 26 100 22 chunks = true := by
  decide +kernel

theorem cover_8 : coverBlock coverCtx table false 170 26 115 175 chunks = true := by
  decide +kernel

theorem cover_9 : coverBlock coverCtx table false 196 22 126 64 chunks = true := by
  decide +kernel

theorem cover_10 : coverBlock coverCtx table false 218 28 131 53 chunks = true := by
  decide +kernel

theorem cover_11 : coverBlock coverCtx table false 246 21 146 116 chunks = true := by
  decide +kernel

end SquaresInCircles.Eight.Generated.Affine.TLowerAffine
