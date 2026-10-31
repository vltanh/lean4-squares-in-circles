module

public import SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.Context
public meta import SquaresInCircles.Eight.Certificates.Check

/-!
# Eight squares: rows 90000 to 99999 of the affine table `CandidateCoarseMismatch`

Each part of 200 rows passes `checkRows`, evaluated by the kernel.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch
open Arithmetic

set_option maxRecDepth 100000

/- Rows 90000 to 99999, in parts of 200. -/
checked_rows parts009 using ctx from "../../../../../data/eight/affine/CANDIDATE_COARSE_MISMATCH.rows" 90001 100001 by 200

end SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch
