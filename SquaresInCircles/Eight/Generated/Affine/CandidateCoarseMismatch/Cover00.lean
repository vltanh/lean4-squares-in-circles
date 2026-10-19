module

public import SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.Data

/-! The angle coverage for the source arcs 0 to 163, checked by `decide +kernel`. -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch
open Arithmetic

set_option maxRecDepth 100000

theorem cover_0 : coverBlock coverCtx table true 0 30 0 0 chunks = true := by
  decide +kernel

theorem cover_1 : coverBlock coverCtx table true 30 29 13 173 chunks = true := by
  decide +kernel

theorem cover_2 : coverBlock coverCtx table true 59 18 19 194 chunks = true := by
  decide +kernel

theorem cover_3 : coverBlock coverCtx table true 77 13 37 129 chunks = true := by
  decide +kernel

theorem cover_4 : coverBlock coverCtx table true 90 8 56 70 chunks = true := by
  decide +kernel

theorem cover_5 : coverBlock coverCtx table true 98 6 73 112 chunks = true := by
  decide +kernel

theorem cover_6 : coverBlock coverCtx table true 104 6 90 124 chunks = true := by
  decide +kernel

theorem cover_7 : coverBlock coverCtx table true 110 6 107 78 chunks = true := by
  decide +kernel

theorem cover_8 : coverBlock coverCtx table true 116 9 123 43 chunks = true := by
  decide +kernel

theorem cover_9 : coverBlock coverCtx table true 125 17 138 158 chunks = true := by
  decide +kernel

theorem cover_10 : coverBlock coverCtx table true 142 11 149 79 chunks = true := by
  decide +kernel

theorem cover_11 : coverBlock coverCtx table true 153 11 159 159 chunks = true := by
  decide +kernel

end SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch
