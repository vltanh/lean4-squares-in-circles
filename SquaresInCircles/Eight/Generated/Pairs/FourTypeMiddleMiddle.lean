module

public import SquaresInCircles.Eight.Arithmetic.FourTypeProblems
public meta import SquaresInCircles.Eight.Certificates.Check

/-!
# Eight squares: the pair table `FourTypeMiddleMiddle`

Its 16 arcs, 60 rows and 8 problems satisfy the four obligations of `Certificates/Check.lean`:
context enclosure, label bounds, row validity and coverage. The resulting theorem `sound` proves
every problem.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Pairs.FourTypeMiddleMiddle
open Arithmetic Arithmetic.PairCover

set_option maxRecDepth 100000

checked_pair_table "../../../../data/eight/pairs/four_type_middle_middle" "../../../../data/eight/pairs/FourTypeMiddleMiddle.meta.json"
  ((9789/2500)) ((9/50)) ((557/625))
  (FourType.fourTypeCases.map fun c =>
    FourType.fourTypeProblem .middle .middle c.1 c.2.1 c.2.2)

end SquaresInCircles.Eight.Generated.Pairs.FourTypeMiddleMiddle
