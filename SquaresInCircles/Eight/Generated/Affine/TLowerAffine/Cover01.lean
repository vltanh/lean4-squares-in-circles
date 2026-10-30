module

public import SquaresInCircles.Eight.Generated.Affine.TLowerAffine.Data

/-!
# Eight squares: the angle coverage of the affine table `TLowerAffine`, source arcs 267 to 302

The walks `coverBlock` over blocks of these source arcs, evaluated by the kernel.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.TLowerAffine
open Arithmetic

set_option maxRecDepth 100000

theorem cover_12 : coverBlock coverCtx table false 267 17 163 143 chunks = true := by
  decide +kernel

theorem cover_13 : coverBlock coverCtx table false 284 11 177 150 chunks = true := by
  decide +kernel

theorem cover_14 : coverBlock coverCtx table false 295 8 195 121 chunks = true := by
  decide +kernel

end SquaresInCircles.Eight.Generated.Affine.TLowerAffine
