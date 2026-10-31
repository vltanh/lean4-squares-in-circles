module

public import SquaresInCircles.Eight.Arithmetic.WordProblems
public meta import SquaresInCircles.Eight.Certificates.Check

/-!
# Eight squares: the pair table `Second4`

Its 218 arcs, 1314 rows and 60 problems satisfy the four obligations of
`Certificates/Check.lean`: context enclosure, label bounds, row validity and coverage. The
resulting theorem `sound` proves every problem.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Pairs.Second4
open Arithmetic Arithmetic.PairCover

set_option maxRecDepth 100000

checked_pair_table "../../../../data/eight/pairs/second_4" "../../../../data/eight/pairs/Second4.meta.json"
  ((9789/2500)) (0) ((17953/20000))
  ((WordGeometry.wrongCases .second 4).map fun c =>
    WordGeometry.wrongPairProblem .second 4 c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2)

end SquaresInCircles.Eight.Generated.Pairs.Second4
