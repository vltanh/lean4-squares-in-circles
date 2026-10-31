module

public import SquaresInCircles.Eight.Generated.Affine.GUpperAffine.Data

/-!
# Eight squares: the angle coverage of the affine table `GUpperAffine`, source arcs 0 to 121

The walks `coverBlock` over blocks of these source arcs, evaluated by the kernel.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.GUpperAffine
open Arithmetic

set_option maxRecDepth 100000

theorem cover_0 : coverBlock coverCtx table false 0 48 0 0 chunks = true := by
  decide +kernel

theorem cover_1 : coverBlock coverCtx table false 48 33 11 144 chunks = true := by
  decide +kernel

theorem cover_2 : coverBlock coverCtx table false 81 40 27 177 chunks = true := by
  decide +kernel

theorem cover_3 : coverBlock coverCtx table false 121 1 44 31 chunks = true := by
  decide +kernel

end SquaresInCircles.Eight.Generated.Affine.GUpperAffine
