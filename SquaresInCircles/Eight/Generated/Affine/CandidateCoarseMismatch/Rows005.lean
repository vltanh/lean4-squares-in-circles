module

public import SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.Context
public meta import SquaresInCircles.Eight.Certificates.Check

/-!
# Eight squares: rows 50000 to 59999 of the affine table `CandidateCoarseMismatch`

Each part of 200 rows passes `checkRows`, evaluated by the kernel.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch
open Arithmetic

set_option maxRecDepth 100000

/- Rows 50000 to 59999, in parts of 200. -/
checked_rows parts005 using ctx from "../../../../../data/eight/affine/CANDIDATE_COARSE_MISMATCH.rows" 50001 60001 by 200

end SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch
