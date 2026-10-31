module

public import SquaresInCircles.Eight.Arithmetic.FourTypeProblems
public meta import SquaresInCircles.Eight.Certificates.Check

/-!
# Eight squares: the pair table `FourTypeHighMiddle`

Its 11 arcs, 42 rows and 8 problems satisfy the four obligations of `Certificates/Check.lean`:
context enclosure, label bounds, row validity and coverage. The resulting theorem `sound` proves
every problem.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Pairs.FourTypeHighMiddle
open Arithmetic Arithmetic.PairCover

set_option maxRecDepth 100000

checked_pair_table "../../../../data/eight/pairs/four_type_high_middle" "../../../../data/eight/pairs/FourTypeHighMiddle.meta.json"
  ((9789/2500)) ((9/50)) ((4463/5000))
  (FourType.fourTypeCases.map fun c =>
    FourType.fourTypeProblem .high .middle c.1 c.2.1 c.2.2)

end SquaresInCircles.Eight.Generated.Pairs.FourTypeHighMiddle
