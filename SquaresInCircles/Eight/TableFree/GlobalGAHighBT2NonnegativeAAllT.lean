module

public import SquaresInCircles.Eight.TableFree.GlobalGAHighBT2NonnegativeAPositiveTD2

/-!
# Entire original high-GA BT2 branch with nonnegative A selected total

The three source-level sectors are already proved in the imported
modules: arbitrary E with TD0; arbitrary E with nonpositive TD2;
arbitrary E with positive TD2. Their actual TD-owner and signed-error
split exhausts every physical weak TD0/TD2 choice. The selected A total
may contain positive and negative constituents. Nothing is assumed
about E's radial kind, DE/EH selection, or error total.

The proof has no transported-source premise and no generated lookup.
Uncompiled source transcription; kernel verification deferred.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.HighGABT2
open Candidate SignedCycle

/-- The entire nonnegative-A half of the high-GA BT2 source obligation,
on the original q and with every retained weak selected owner. -/
theorem nonnegative_A_all_T_false {q : ℝ} {C : SignedCycle}
    (I : GlobalGA.SourceDomain q C)
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hBT : C.Feasible B 2)
    (ha : 0≤aTotal I) : False := by
  have ht : I.owner T=0∨I.owner T=2 := by
    simpa [GlobalGA.highGAOwners,T] using I.allowed T
  rcases ht with ht|ht
  · have hTD : C.Feasible T 0 := by simpa [ht] using I.feasible T
    exact nonnegative_A_TD0_false I hqL hqU hBT hTD ha
  · have hTD : C.Feasible T 2 := by simpa [ht] using I.feasible T
    by_cases hz : delta C.theta T≤0
    · exact nonnegative_A_nonpositive_TD2_false I hqL hqU hBT hTD hz ha
    · exact nonnegative_A_positive_TD2_false I hqL hqU hBT hTD
        (lt_of_not_ge hz).le ha

end SquaresInCircles.Eight.TableFree.HighGABT2
