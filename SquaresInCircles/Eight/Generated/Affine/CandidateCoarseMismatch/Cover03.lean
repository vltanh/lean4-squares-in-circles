module

public import SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.Data

/-! The angle coverage for the source arcs 448 to 461, checked by `decide +kernel`. -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch
open Arithmetic

set_option maxRecDepth 100000

theorem cover_36 : coverBlock coverCtx table true 448 6 515 151 chunks = true := by
  decide +kernel

theorem cover_37 : coverBlock coverCtx table true 454 6 531 140 chunks = true := by
  decide +kernel

theorem cover_38 : coverBlock coverCtx table true 460 2 547 40 chunks = true := by
  decide +kernel

end SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch
