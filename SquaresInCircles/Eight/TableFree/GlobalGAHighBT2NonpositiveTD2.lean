module

public import SquaresInCircles.Eight.TableFree.GlobalGAHighBT2NonnegativeATD0
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeENonpositiveTDSource

/-!
# All E regimes, nonnegative selected A and nonpositive original TD2

A signed A total from the retained two A edges may contain opposite
individual signs. The actual TD2 error is nonpositive, including zero.
The short A source and the high A source already give all E-case
contradictions, for original weak owners at the same q. This file
connects those two interval domains under a single original source
without choosing any E owner or changing E.

Uncompiled source only, no Lean or CI.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.HighGABT2
open Candidate SignedCycle
variable {q : ℝ} {C : SignedCycle} (I : GlobalGA.SourceDomain q C)

/-- BT2/TD2 with nonpositive actual TD2 error, any E owner/radial/sign,
and nonnegative selected A total, is impossible on the original cycle. -/
theorem nonnegative_A_nonpositive_TD2_false
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 2)
    (ht : delta C.theta T≤0)
    (ha : 0≤aTotal I) : False := by
  have hGA : C.Feasible G (if gaFlag I then 3 else 2) := by
    rw [←ga_owner I]
    exact I.feasible G
  have hAB : C.Feasible A (if abFlag I then 2 else 0) := by
    rw [←ab_owner I]
    exact I.feasible A
  have ha' : 0≤GlobalGA.PairedE.LowA.aTotal C (gaFlag I) (abFlag I) := by
    simpa [aTotal,GlobalGA.NonnegativeTotals.Source.aTotal,
      GlobalGA.PairedE.LowA.aTotal,GlobalGA.PairedE.total] using ha
  by_cases hlow : GlobalGA.PairedE.LowA.aTotal C (gaFlag I) (abFlag I)≤1/6
  · exact GlobalGA.NegativeELowA.source_false
      I hqL hqU (gaFlag I) (abFlag I) true
      hGA hAB hBT (by simpa using hTD)
      ⟨ha',hlow⟩ (by intro _; exact ht)
  · exact GlobalGA.NegativeENonpositiveTD.source_false
      I hqL hqU (gaFlag I) (abFlag I)
      hGA hAB hBT hTD ha' ht

end SquaresInCircles.Eight.TableFree.HighGABT2
