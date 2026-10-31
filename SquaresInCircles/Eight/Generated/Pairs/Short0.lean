module

public import SquaresInCircles.Eight.Arithmetic.WordProblems
public meta import SquaresInCircles.Eight.Certificates.Check

/-!
# Eight squares: the pair table `Short0`

Its 16 arcs, 126 rows and 42 problems satisfy the four obligations of `Certificates/Check.lean`:
context enclosure, label bounds, row validity and coverage. The resulting theorem `sound` proves
every problem.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Pairs.Short0
open Arithmetic Arithmetic.PairCover

set_option maxRecDepth 100000

checked_pair_table "../../../../data/eight/pairs/short_0" "../../../../data/eight/pairs/Short0.meta.json"
  ((9789/2500)) (0) ((17953/20000))
  ((WordGeometry.wrongCases .short 0).map fun c =>
    WordGeometry.wrongPairProblem .short 0 c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2)

end SquaresInCircles.Eight.Generated.Pairs.Short0
