module

public import SquaresInCircles.Eight.Arithmetic.FourTypeProblems
public meta import SquaresInCircles.Eight.Certificates.Check

/-!
# Eight squares: the pair table `FourTypeMiddleHigh`

Its 6 arcs, 43 rows and 8 problems satisfy the four obligations of `Certificates/Check.lean`:
context enclosure, label bounds, row validity and coverage. The resulting theorem `sound` proves
every problem.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Pairs.FourTypeMiddleHigh
open Arithmetic Arithmetic.PairCover

set_option maxRecDepth 100000

checked_pair_table "../../../../data/eight/pairs/four_type_middle_high" "../../../../data/eight/pairs/FourTypeMiddleHigh.meta.json"
  ((9789/2500)) ((9/50)) ((4463/5000))
  (FourType.fourTypeCases.map fun c =>
    FourType.fourTypeProblem .middle .high c.1 c.2.1 c.2.2)

end SquaresInCircles.Eight.Generated.Pairs.FourTypeMiddleHigh
