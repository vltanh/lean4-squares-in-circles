module

public import SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.Data

/-! The angle coverage for the source arcs 434 to 461, checked by `decide +kernel`. -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch
open Arithmetic

set_option maxRecDepth 100000

theorem cover_36 : coverBlock coverCtx table 434 6 502 73 chunks = true := by
  decide +kernel

theorem cover_37 : coverBlock coverCtx table 440 6 518 74 chunks = true := by
  decide +kernel

theorem cover_38 : coverBlock coverCtx table 446 6 535 130 chunks = true := by
  decide +kernel

theorem cover_39 : coverBlock coverCtx table 452 6 551 123 chunks = true := by
  decide +kernel

theorem cover_40 : coverBlock coverCtx table 458 4 567 64 chunks = true := by
  decide +kernel

end SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch
