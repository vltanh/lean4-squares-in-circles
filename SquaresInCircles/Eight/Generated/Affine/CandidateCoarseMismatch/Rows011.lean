module

public import SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.Context
public meta import SquaresInCircles.Eight.Certificates.Check

/-!
# Eight squares: rows 110000 to 110424 of the affine table `CandidateCoarseMismatch`

Each part of 200 rows passes `checkRows`, evaluated by the kernel.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch
open Arithmetic

set_option maxRecDepth 100000

/- Rows 110000 to 110424, in parts of 200. -/
checked_rows parts011 using ctx from "../../../../../data/eight/affine/CANDIDATE_COARSE_MISMATCH.rows" 110001 110426 by 200

end SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch
