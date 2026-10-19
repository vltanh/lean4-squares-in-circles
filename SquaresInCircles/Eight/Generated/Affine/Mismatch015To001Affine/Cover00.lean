module

public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Data

/-!
# Eight squares: the angle coverage of the affine table `Mismatch015To001Affine`, source arcs 0 to 120

The walks `coverBlock` over blocks of these source arcs, evaluated by the kernel.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine
open Arithmetic

set_option maxRecDepth 100000

theorem cover_0 : coverBlock coverCtx table true 0 16 0 0 chunks = true := by
  decide +kernel

theorem cover_1 : coverBlock coverCtx table true 16 11 16 28 chunks = true := by
  decide +kernel

theorem cover_2 : coverBlock coverCtx table true 27 11 35 101 chunks = true := by
  decide +kernel

theorem cover_3 : coverBlock coverCtx table true 38 11 54 174 chunks = true := by
  decide +kernel

theorem cover_4 : coverBlock coverCtx table true 49 11 74 60 chunks = true := by
  decide +kernel

theorem cover_5 : coverBlock coverCtx table true 60 11 96 8 chunks = true := by
  decide +kernel

theorem cover_6 : coverBlock coverCtx table true 71 11 117 132 chunks = true := by
  decide +kernel

theorem cover_7 : coverBlock coverCtx table true 82 11 138 105 chunks = true := by
  decide +kernel

theorem cover_8 : coverBlock coverCtx table true 93 7 156 118 chunks = true := by
  decide +kernel

theorem cover_9 : coverBlock coverCtx table true 100 7 176 128 chunks = true := by
  decide +kernel

theorem cover_10 : coverBlock coverCtx table true 107 7 197 149 chunks = true := by
  decide +kernel

theorem cover_11 : coverBlock coverCtx table true 114 7 219 9 chunks = true := by
  decide +kernel

end SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine
