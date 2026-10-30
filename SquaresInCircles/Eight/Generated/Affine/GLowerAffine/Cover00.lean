module

public import SquaresInCircles.Eight.Generated.Affine.GLowerAffine.Data

/-!
# Eight squares: the angle coverage of the affine table `GLowerAffine`, source arcs 0 to 113

The walks `coverBlock` over blocks of these source arcs, evaluated by the kernel.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.GLowerAffine
open Arithmetic

set_option maxRecDepth 100000

theorem cover_0 : coverBlock coverCtx table false 0 51 0 0 chunks = true := by
  decide +kernel

theorem cover_1 : coverBlock coverCtx table false 51 37 15 71 chunks = true := by
  decide +kernel

theorem cover_2 : coverBlock coverCtx table false 88 26 29 192 chunks = true := by
  decide +kernel

end SquaresInCircles.Eight.Generated.Affine.GLowerAffine
