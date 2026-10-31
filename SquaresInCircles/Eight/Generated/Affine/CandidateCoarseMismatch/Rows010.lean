module

public import SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.Context
public meta import SquaresInCircles.Eight.Certificates.Check

/-!
# Eight squares: rows 100000 to 109999 of the affine table `CandidateCoarseMismatch`

Each part of 200 rows passes `checkRows`, evaluated by the kernel.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch
open Arithmetic

set_option maxRecDepth 100000

/- Rows 100000 to 109999, in parts of 200. -/
checked_rows parts010 using ctx from "../../../../../data/eight/affine/CANDIDATE_COARSE_MISMATCH.rows" 100001 110001 by 200

end SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch
