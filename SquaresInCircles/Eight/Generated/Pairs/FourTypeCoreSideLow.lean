module

public import SquaresInCircles.Eight.Arithmetic.FourTypeProblems
public meta import SquaresInCircles.Eight.Certificates.Check

/-!
# Eight squares: the pair table `FourTypeCoreSideLow`

Its 4 arcs, 47 rows and 8 problems satisfy the four obligations of `Certificates/Check.lean`:
context enclosure, label bounds, row validity and coverage. The resulting theorem `sound` proves
every problem.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Pairs.FourTypeCoreSideLow
open Arithmetic Arithmetic.PairCover

set_option maxRecDepth 100000

checked_pair_table "../../../../data/eight/pairs/four_type_core_side_low" "../../../../data/eight/pairs/FourTypeCoreSideLow.meta.json"
  ((9789/2500)) ((9/50)) ((91/100))
  (FourType.fourTypeCases.map fun c =>
    FourType.fourTypeProblem .coreSide .low c.1 c.2.1 c.2.2)

end SquaresInCircles.Eight.Generated.Pairs.FourTypeCoreSideLow
