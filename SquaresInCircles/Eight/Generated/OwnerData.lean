module

public import SquaresInCircles.Eight.Generated.Owner.Tables
public import SquaresInCircles.Eight.Generated.Owner.Bundles

/-!
# Eight squares: the owner tables and tilt bundles

`mixedTables` lists the owner tables of the mixed mode, and `tiltLeft` and `tiltRight` the tilt
bundles whose intervals cover the two tails
`[0, 1001/20000]` and `[2/25, 3/8]` of the positive half-angle chart; the nonpositive half-angles
are excluded by `negative_tilt_excluded`.
-/

@[expose] public section
noncomputable section
set_option maxRecDepth 1000000
open scoped BigOperators
open SquaresInCircles.Eight.Candidate
open SquaresInCircles.Eight.Candidate.Dual
namespace SquaresInCircles.Eight.Generated.Owner

def mixedTables : List OwnerTable := [mixedTable000, mixedTable003, mixedTable004, mixedTable007, mixedTable008, mixedTable011, mixedTable012]

def tiltLeft : List TiltBundle := [tiltBundle018, tiltBundle019, tiltBundle020, tiltBundle021, tiltBundle022, tiltBundle023, tiltBundle024, tiltBundle025, tiltBundle026, tiltBundle027, tiltBundle028, tiltBundle029, tiltBundle030, tiltBundle031, tiltBundle032, tiltBundle033, tiltBundle034, tiltBundle035, tiltBundle036, tiltBundle037, tiltBundle038, tiltBundle039]

theorem tilt_left_cover : Arithmetic.ClosedChain 0 (1001/20000)
    (tiltLeft.map TiltBundle.interval) := by decide +kernel

def tiltRight : List TiltBundle := [tiltBundle040, tiltBundle041, tiltBundle042, tiltBundle043, tiltBundle044, tiltBundle045, tiltBundle046, tiltBundle047, tiltBundle048, tiltBundle049, tiltBundle050, tiltBundle051, tiltBundle052, tiltBundle053, tiltBundle054, tiltBundle055, tiltBundle056, tiltBundle057, tiltBundle058]

theorem tilt_right_cover : Arithmetic.ClosedChain (2/25) (3/8)
    (tiltRight.map TiltBundle.interval) := by decide +kernel

end SquaresInCircles.Eight.Generated.Owner
