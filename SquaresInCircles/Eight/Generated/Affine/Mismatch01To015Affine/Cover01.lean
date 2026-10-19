module

public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Data

/-!
# Eight squares: the angle coverage of the affine table `Mismatch01To015Affine`, source arcs 166 to 330

The walks `coverBlock` over blocks of these source arcs, evaluated by the kernel.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine
open Arithmetic

set_option maxRecDepth 100000

theorem cover_12 : coverBlock coverCtx table true 166 10 215 125 chunks = true := by
  decide +kernel

theorem cover_13 : coverBlock coverCtx table true 176 11 232 37 chunks = true := by
  decide +kernel

theorem cover_14 : coverBlock coverCtx table true 187 21 249 22 chunks = true := by
  decide +kernel

theorem cover_15 : coverBlock coverCtx table true 208 17 264 150 chunks = true := by
  decide +kernel

theorem cover_16 : coverBlock coverCtx table true 225 14 281 99 chunks = true := by
  decide +kernel

theorem cover_17 : coverBlock coverCtx table true 239 14 297 176 chunks = true := by
  decide +kernel

theorem cover_18 : coverBlock coverCtx table true 253 14 316 141 chunks = true := by
  decide +kernel

theorem cover_19 : coverBlock coverCtx table true 267 12 333 171 chunks = true := by
  decide +kernel

theorem cover_20 : coverBlock coverCtx table true 279 12 353 159 chunks = true := by
  decide +kernel

theorem cover_21 : coverBlock coverCtx table true 291 17 373 199 chunks = true := by
  decide +kernel

theorem cover_22 : coverBlock coverCtx table true 308 10 392 153 chunks = true := by
  decide +kernel

theorem cover_23 : coverBlock coverCtx table true 318 13 415 106 chunks = true := by
  decide +kernel

end SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine
