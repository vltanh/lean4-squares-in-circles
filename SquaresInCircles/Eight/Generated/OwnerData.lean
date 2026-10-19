module

public import SquaresInCircles.Eight.Generated.Owner.Tables
public import SquaresInCircles.Eight.Generated.Owner.Bundles

/-!
# Eight squares: the owner tables and tilt bundles

`mixedTables` lists the seven owner tables of the mixed mode (`Generated/Owner/Tables.lean`), and
`tiltLeft` and `tiltRight` the 22 and 19 tilt bundles (`Generated/Owner/Bundles.lean`), whose
intervals form closed chains over the two tails `[0, 1001/20000]` and `[2/25, 3/8]` of the
positive half-angle chart, as the kernel checks (`tilt_left_cover`, `tilt_right_cover`). The
nonpositive half-angles are excluded by `negative_tilt_excluded`.
-/

@[expose] public section
noncomputable section
set_option maxRecDepth 1000000
open scoped BigOperators
open SquaresInCircles.Eight.Candidate
open SquaresInCircles.Eight.Candidate.Dual
namespace SquaresInCircles.Eight.Generated.Owner

/-- The seven owner tables of the mixed mode. -/
def mixedTables : List OwnerTable := [mixedTable000, mixedTable003, mixedTable004, mixedTable007, mixedTable008, mixedTable011, mixedTable012]

/-- The tilt bundles of the tail `[0, 1001/20000]`. -/
def tiltLeft : List TiltBundle := [tiltBundle018, tiltBundle019, tiltBundle020, tiltBundle021, tiltBundle022, tiltBundle023, tiltBundle024, tiltBundle025, tiltBundle026, tiltBundle027, tiltBundle028, tiltBundle029, tiltBundle030, tiltBundle031, tiltBundle032, tiltBundle033, tiltBundle034, tiltBundle035, tiltBundle036, tiltBundle037, tiltBundle038, tiltBundle039]

/-- The intervals of `tiltLeft` form a closed chain over `[0, 1001/20000]`. -/
theorem tilt_left_cover : Arithmetic.ClosedChain 0 (1001/20000)
    (tiltLeft.map TiltBundle.interval) := by decide +kernel

/-- The tilt bundles of the tail `[2/25, 3/8]`. -/
def tiltRight : List TiltBundle := [tiltBundle040, tiltBundle041, tiltBundle042, tiltBundle043, tiltBundle044, tiltBundle045, tiltBundle046, tiltBundle047, tiltBundle048, tiltBundle049, tiltBundle050, tiltBundle051, tiltBundle052, tiltBundle053, tiltBundle054, tiltBundle055, tiltBundle056, tiltBundle057, tiltBundle058]

/-- The intervals of `tiltRight` form a closed chain over `[2/25, 3/8]`. -/
theorem tilt_right_cover : Arithmetic.ClosedChain (2/25) (3/8)
    (tiltRight.map TiltBundle.interval) := by decide +kernel

end SquaresInCircles.Eight.Generated.Owner
