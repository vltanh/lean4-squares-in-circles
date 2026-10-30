module

public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Data

/-!
# Eight squares: the angle coverage of the affine table `Mismatch01To015Affine`, source arcs 0 to 165

The walks `coverBlock` over blocks of these source arcs, evaluated by the kernel.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine
open Arithmetic

set_option maxRecDepth 100000

theorem cover_0 : coverBlock coverCtx table true 0 21 0 0 chunks = true := by
  decide +kernel

theorem cover_1 : coverBlock coverCtx table true 21 10 10 140 chunks = true := by
  decide +kernel

theorem cover_2 : coverBlock coverCtx table true 31 10 28 186 chunks = true := by
  decide +kernel

theorem cover_3 : coverBlock coverCtx table true 41 14 48 86 chunks = true := by
  decide +kernel

theorem cover_4 : coverBlock coverCtx table true 55 17 68 190 chunks = true := by
  decide +kernel

theorem cover_5 : coverBlock coverCtx table true 72 10 87 173 chunks = true := by
  decide +kernel

theorem cover_6 : coverBlock coverCtx table true 82 11 108 32 chunks = true := by
  decide +kernel

theorem cover_7 : coverBlock coverCtx table true 93 17 128 116 chunks = true := by
  decide +kernel

theorem cover_8 : coverBlock coverCtx table true 110 15 145 22 chunks = true := by
  decide +kernel

theorem cover_9 : coverBlock coverCtx table true 125 13 160 136 chunks = true := by
  decide +kernel

theorem cover_10 : coverBlock coverCtx table true 138 17 178 135 chunks = true := by
  decide +kernel

theorem cover_11 : coverBlock coverCtx table true 155 11 197 88 chunks = true := by
  decide +kernel

end SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine
