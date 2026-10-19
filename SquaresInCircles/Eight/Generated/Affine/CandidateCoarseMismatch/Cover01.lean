module

public import SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.Data

/-!
# Eight squares: the angle coverage of the affine table `CandidateCoarseMismatch`, source arcs 164 to 315

The walks `coverBlock` over blocks of these source arcs, evaluated by the kernel.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch
open Arithmetic

set_option maxRecDepth 100000

theorem cover_12 : coverBlock coverCtx table true 164 12 164 83 chunks = true := by
  decide +kernel

theorem cover_13 : coverBlock coverCtx table true 176 9 166 5 chunks = true := by
  decide +kernel

theorem cover_14 : coverBlock coverCtx table true 185 8 175 199 chunks = true := by
  decide +kernel

theorem cover_15 : coverBlock coverCtx table true 193 7 189 2 chunks = true := by
  decide +kernel

theorem cover_16 : coverBlock coverCtx table true 200 7 203 50 chunks = true := by
  decide +kernel

theorem cover_17 : coverBlock coverCtx table true 207 21 220 52 chunks = true := by
  decide +kernel

theorem cover_18 : coverBlock coverCtx table true 228 18 239 90 chunks = true := by
  decide +kernel

theorem cover_19 : coverBlock coverCtx table true 246 18 259 2 chunks = true := by
  decide +kernel

theorem cover_20 : coverBlock coverCtx table true 264 15 274 171 chunks = true := by
  decide +kernel

theorem cover_21 : coverBlock coverCtx table true 279 17 294 119 chunks = true := by
  decide +kernel

theorem cover_22 : coverBlock coverCtx table true 296 12 311 7 chunks = true := by
  decide +kernel

theorem cover_23 : coverBlock coverCtx table true 308 8 323 171 chunks = true := by
  decide +kernel

end SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch
