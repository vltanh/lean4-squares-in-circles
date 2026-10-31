module

public import SquaresInCircles.Eight.Arithmetic.FourTypeProblems
public meta import SquaresInCircles.Eight.Certificates.Check

/-!
# Eight squares: the pair table `FourTypeCoreCornerLow`

Its 4 arcs, 39 rows and 8 problems satisfy the four obligations of `Certificates/Check.lean`:
context enclosure, label bounds, row validity and coverage. The resulting theorem `sound` proves
every problem.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Pairs.FourTypeCoreCornerLow
open Arithmetic Arithmetic.PairCover

set_option maxRecDepth 100000

checked_pair_table "../../../../data/eight/pairs/four_type_core_corner_low" "../../../../data/eight/pairs/FourTypeCoreCornerLow.meta.json"
  ((9789/2500)) ((9/50)) ((91/100))
  (FourType.fourTypeCases.map fun c =>
    FourType.fourTypeProblem .coreCorner .low c.1 c.2.1 c.2.2)

end SquaresInCircles.Eight.Generated.Pairs.FourTypeCoreCornerLow
