module

public import SquaresInCircles.Eight.TableFree.GlobalGAHighBT2NonnegativeTotals
public import SquaresInCircles.Eight.TableFree.GlobalGANonnegativeATD0Source

/-!
# Whole original BT2/TD0 source sector with nonnegative A primary total

The complete E-case theorem is already present in
GlobalGANonnegativeATD0Source. This module supplies its actual A owner
selection from GlobalGA.SourceDomain; no specific E radial kind, EH/DE
owner, or E-error sign is assumed. The initial T owner 0 is retained,
with its original arbitrary signed angular error.

The nonnegative A flag is the sum of all originally retained A primary
errors (not a sign assumption on individual A angles). Source-only Lean
transcription; Lean, lake, tests and CI were not run.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.HighGABT2
open Candidate SignedCycle

variable {q : ℝ} {C : SignedCycle} (I : GlobalGA.SourceDomain q C)

/-- Every original BT2/TD0 source with a nonnegative selected A total
is excluded, even when its E primaries both have negative signed total.
The original q and all seven weak separators are unchanged. -/
theorem nonnegative_A_TD0_false
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 0)
    (ha : 0≤aTotal I) : False := by
  have hGA : C.Feasible G (if gaFlag I then 3 else 2) := by
    rw [←ga_owner I]
    exact I.feasible G
  have hAB : C.Feasible A (if abFlag I then 2 else 0) := by
    rw [←ab_owner I]
    exact I.feasible A
  have ha' : 0≤GlobalGA.PairedE.LowA.aTotal C (gaFlag I) (abFlag I) := by
    simpa [aTotal,GlobalGA.NonnegativeTotals.Source.aTotal,
      GlobalGA.PairedE.LowA.aTotal,GlobalGA.PairedE.total]
      using ha
  exact GlobalGA.NonnegativeATD0.source_false I hqL hqU
    (gaFlag I) (abFlag I) hGA hAB hBT hTD ha'

end SquaresInCircles.Eight.TableFree.HighGABT2
