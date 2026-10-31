module

public import SquaresInCircles.Eight.Arithmetic.WordProblems
public meta import SquaresInCircles.Eight.Certificates.Check

/-!
# Eight squares: the pair table `Common1`

Its 12 arcs, 176 rows and 72 problems satisfy the four obligations of `Certificates/Check.lean`:
context enclosure, label bounds, row validity and coverage. The resulting theorem `sound` proves
every problem.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Pairs.Common1
open Arithmetic Arithmetic.PairCover

set_option maxRecDepth 100000

checked_pair_table "../../../../data/eight/pairs/common_1" "../../../../data/eight/pairs/Common1.meta.json"
  ((9789/2500)) (0) ((157/200))
  ((WordGeometry.commonCases 1).map fun c =>
    WordGeometry.commonPairProblem 1 c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2)

end SquaresInCircles.Eight.Generated.Pairs.Common1
