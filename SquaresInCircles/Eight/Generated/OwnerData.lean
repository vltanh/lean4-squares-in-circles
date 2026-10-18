module

public import SquaresInCircles.Eight.Generated.Owner.Quarter000
public import SquaresInCircles.Eight.Generated.Owner.Quarter001
public import SquaresInCircles.Eight.Generated.Owner.Quarter002
public import SquaresInCircles.Eight.Generated.Owner.Quarter003
public import SquaresInCircles.Eight.Generated.Owner.Quarter004
public import SquaresInCircles.Eight.Generated.Owner.Quarter005
public import SquaresInCircles.Eight.Generated.Owner.Quarter006
public import SquaresInCircles.Eight.Generated.Owner.Quarter007
public import SquaresInCircles.Eight.Generated.Owner.Quarter012
public import SquaresInCircles.Eight.Generated.Owner.Quarter013
public import SquaresInCircles.Eight.Generated.Owner.Quarter014
public import SquaresInCircles.Eight.Generated.Owner.Quarter015
public import SquaresInCircles.Eight.Generated.Owner.Quarter016
public import SquaresInCircles.Eight.Generated.Owner.Quarter017
public import SquaresInCircles.Eight.Generated.Owner.Quarter018
public import SquaresInCircles.Eight.Generated.Owner.Quarter019
public import SquaresInCircles.Eight.Generated.Owner.Quarter024
public import SquaresInCircles.Eight.Generated.Owner.Quarter025
public import SquaresInCircles.Eight.Generated.Owner.Quarter026
public import SquaresInCircles.Eight.Generated.Owner.Quarter027
public import SquaresInCircles.Eight.Generated.Owner.Quarter028
public import SquaresInCircles.Eight.Generated.Owner.Quarter029
public import SquaresInCircles.Eight.Generated.Owner.Quarter030
public import SquaresInCircles.Eight.Generated.Owner.Quarter031
public import SquaresInCircles.Eight.Generated.Owner.Quarter036
public import SquaresInCircles.Eight.Generated.Owner.Quarter037
public import SquaresInCircles.Eight.Generated.Owner.Quarter038
public import SquaresInCircles.Eight.Generated.Owner.Quarter039
public import SquaresInCircles.Eight.Generated.Owner.Quarter040
public import SquaresInCircles.Eight.Generated.Owner.Quarter041
public import SquaresInCircles.Eight.Generated.Owner.Quarter042
public import SquaresInCircles.Eight.Generated.Owner.Quarter043
public import SquaresInCircles.Eight.Generated.Owner.Mixed000
public import SquaresInCircles.Eight.Generated.Owner.Mixed001
public import SquaresInCircles.Eight.Generated.Owner.Mixed002
public import SquaresInCircles.Eight.Generated.Owner.Mixed003
public import SquaresInCircles.Eight.Generated.Owner.Mixed004
public import SquaresInCircles.Eight.Generated.Owner.Mixed005
public import SquaresInCircles.Eight.Generated.Owner.Mixed006
public import SquaresInCircles.Eight.Generated.Owner.Mixed007
public import SquaresInCircles.Eight.Generated.Owner.Mixed008
public import SquaresInCircles.Eight.Generated.Owner.Mixed009
public import SquaresInCircles.Eight.Generated.Owner.Mixed010
public import SquaresInCircles.Eight.Generated.Owner.Mixed011
public import SquaresInCircles.Eight.Generated.Owner.Mixed012
public import SquaresInCircles.Eight.Generated.Owner.Mixed013
public import SquaresInCircles.Eight.Generated.Owner.Mixed014
public import SquaresInCircles.Eight.Generated.Owner.Tilt018
public import SquaresInCircles.Eight.Generated.Owner.Tilt019
public import SquaresInCircles.Eight.Generated.Owner.Tilt020
public import SquaresInCircles.Eight.Generated.Owner.Tilt021
public import SquaresInCircles.Eight.Generated.Owner.Tilt022
public import SquaresInCircles.Eight.Generated.Owner.Tilt023
public import SquaresInCircles.Eight.Generated.Owner.Tilt024
public import SquaresInCircles.Eight.Generated.Owner.Tilt025
public import SquaresInCircles.Eight.Generated.Owner.Tilt026
public import SquaresInCircles.Eight.Generated.Owner.Tilt027
public import SquaresInCircles.Eight.Generated.Owner.Tilt028
public import SquaresInCircles.Eight.Generated.Owner.Tilt029
public import SquaresInCircles.Eight.Generated.Owner.Tilt030
public import SquaresInCircles.Eight.Generated.Owner.Tilt031
public import SquaresInCircles.Eight.Generated.Owner.Tilt032
public import SquaresInCircles.Eight.Generated.Owner.Tilt033
public import SquaresInCircles.Eight.Generated.Owner.Tilt034
public import SquaresInCircles.Eight.Generated.Owner.Tilt035
public import SquaresInCircles.Eight.Generated.Owner.Tilt036
public import SquaresInCircles.Eight.Generated.Owner.Tilt037
public import SquaresInCircles.Eight.Generated.Owner.Tilt038
public import SquaresInCircles.Eight.Generated.Owner.Tilt039
public import SquaresInCircles.Eight.Generated.Owner.Tilt040
public import SquaresInCircles.Eight.Generated.Owner.Tilt041
public import SquaresInCircles.Eight.Generated.Owner.Tilt042
public import SquaresInCircles.Eight.Generated.Owner.Tilt043
public import SquaresInCircles.Eight.Generated.Owner.Tilt044
public import SquaresInCircles.Eight.Generated.Owner.Tilt045
public import SquaresInCircles.Eight.Generated.Owner.Tilt046
public import SquaresInCircles.Eight.Generated.Owner.Tilt047
public import SquaresInCircles.Eight.Generated.Owner.Tilt048
public import SquaresInCircles.Eight.Generated.Owner.Tilt049
public import SquaresInCircles.Eight.Generated.Owner.Tilt050
public import SquaresInCircles.Eight.Generated.Owner.Tilt051
public import SquaresInCircles.Eight.Generated.Owner.Tilt052
public import SquaresInCircles.Eight.Generated.Owner.Tilt053
public import SquaresInCircles.Eight.Generated.Owner.Tilt054
public import SquaresInCircles.Eight.Generated.Owner.Tilt055
public import SquaresInCircles.Eight.Generated.Owner.Tilt056
public import SquaresInCircles.Eight.Generated.Owner.Tilt057
public import SquaresInCircles.Eight.Generated.Owner.Tilt058

/-! Generated F8 rational data and algebraic proof source. Uncompiled.
No replay status or external decision procedure is a theorem premise. -/

@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open scoped BigOperators
open SquaresInCircles.Eight.Candidate
open SquaresInCircles.Eight.Candidate.Dual
namespace SquaresInCircles.Eight.Generated.Owner

def quarterTables : List OwnerTable := [quarterTable000, quarterTable001, quarterTable002, quarterTable003, quarterTable004, quarterTable005, quarterTable006, quarterTable007, quarterTable012, quarterTable013, quarterTable014, quarterTable015, quarterTable016, quarterTable017, quarterTable018, quarterTable019, quarterTable024, quarterTable025, quarterTable026, quarterTable027, quarterTable028, quarterTable029, quarterTable030, quarterTable031, quarterTable036, quarterTable037, quarterTable038, quarterTable039, quarterTable040, quarterTable041, quarterTable042, quarterTable043]

theorem quarter_table_modes : ∀ T ∈ quarterTables, T.mode = .quarter := by
  intro T hT
  simp only [quarterTables, List.mem_cons, List.mem_singleton] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

def mixedTables : List OwnerTable := [mixedTable000, mixedTable001, mixedTable002, mixedTable003, mixedTable004, mixedTable005, mixedTable006, mixedTable007, mixedTable008, mixedTable009, mixedTable010, mixedTable011, mixedTable012, mixedTable013, mixedTable014]

theorem mixed_table_modes : ∀ T ∈ mixedTables, T.mode = .mixed := by
  intro T hT
  simp only [mixedTables, List.mem_cons, List.mem_singleton] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The nonpositive half-chart is excluded by the four-circle stress. -/
def tiltLeft : List TiltBundle := [tiltBundle018, tiltBundle019, tiltBundle020, tiltBundle021, tiltBundle022, tiltBundle023, tiltBundle024, tiltBundle025, tiltBundle026, tiltBundle027, tiltBundle028, tiltBundle029, tiltBundle030, tiltBundle031, tiltBundle032, tiltBundle033, tiltBundle034, tiltBundle035, tiltBundle036, tiltBundle037, tiltBundle038, tiltBundle039]

theorem tilt_left_cover : Arithmetic.ClosedChain 0 (1001/20000)
    (tiltLeft.map TiltBundle.interval) := by decide

def tiltRight : List TiltBundle := [tiltBundle040, tiltBundle041, tiltBundle042, tiltBundle043, tiltBundle044, tiltBundle045, tiltBundle046, tiltBundle047, tiltBundle048, tiltBundle049, tiltBundle050, tiltBundle051, tiltBundle052, tiltBundle053, tiltBundle054, tiltBundle055, tiltBundle056, tiltBundle057, tiltBundle058]

theorem tilt_right_cover : Arithmetic.ClosedChain (2/25) (3/8)
    (tiltRight.map TiltBundle.interval) := by decide


end SquaresInCircles.Eight.Generated.Owner
