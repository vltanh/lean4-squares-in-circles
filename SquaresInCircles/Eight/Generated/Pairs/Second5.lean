module

public import SquaresInCircles.Eight.Arithmetic.WordProblems
public meta import SquaresInCircles.Eight.Certificates.Check

/-!
# Eight squares: the pair table `Second5`

Its 277 arcs, 1578 rows and 104 problems satisfy the four obligations of
`Certificates/Check.lean`: context enclosure, label bounds, row validity and coverage. The
resulting theorem `sound` proves every problem.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Pairs.Second5
open Arithmetic Arithmetic.PairCover

set_option maxRecDepth 100000

checked_pair_table "../../../../data/eight/pairs/second_5" "../../../../data/eight/pairs/Second5.meta.json"
  ((9789/2500)) (0) ((17953/20000))
  ((WordGeometry.wrongCases .second 5).map fun c =>
    WordGeometry.wrongPairProblem .second 5 c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2)

end SquaresInCircles.Eight.Generated.Pairs.Second5
