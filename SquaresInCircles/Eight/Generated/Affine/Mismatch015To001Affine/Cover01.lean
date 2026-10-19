module

public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Data

/-!
# Eight squares: the angle coverage of the affine table `Mismatch015To001Affine`, source arcs 121 to 320

The walks `coverBlock` over blocks of these source arcs, evaluated by the kernel.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine
open Arithmetic

set_option maxRecDepth 100000

theorem cover_12 : coverBlock coverCtx table true 121 8 239 7 chunks = true := by
  decide +kernel

theorem cover_13 : coverBlock coverCtx table true 129 12 260 53 chunks = true := by
  decide +kernel

theorem cover_14 : coverBlock coverCtx table true 141 21 276 103 chunks = true := by
  decide +kernel

theorem cover_15 : coverBlock coverCtx table true 162 18 292 153 chunks = true := by
  decide +kernel

theorem cover_16 : coverBlock coverCtx table true 180 17 310 122 chunks = true := by
  decide +kernel

theorem cover_17 : coverBlock coverCtx table true 197 21 329 47 chunks = true := by
  decide +kernel

theorem cover_18 : coverBlock coverCtx table true 218 12 347 111 chunks = true := by
  decide +kernel

theorem cover_19 : coverBlock coverCtx table true 230 12 366 49 chunks = true := by
  decide +kernel

theorem cover_20 : coverBlock coverCtx table true 242 12 384 159 chunks = true := by
  decide +kernel

theorem cover_21 : coverBlock coverCtx table true 254 22 402 161 chunks = true := by
  decide +kernel

theorem cover_22 : coverBlock coverCtx table true 276 24 419 12 chunks = true := by
  decide +kernel

theorem cover_23 : coverBlock coverCtx table true 300 21 438 149 chunks = true := by
  decide +kernel

end SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine
