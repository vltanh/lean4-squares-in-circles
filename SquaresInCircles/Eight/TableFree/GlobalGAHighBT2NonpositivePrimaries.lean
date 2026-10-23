module

public import SquaresInCircles.Eight.TableFree.GlobalGAHighBT2NonnegativeAAllT
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeCoreESource
public import SquaresInCircles.Eight.TableFree.GlobalGAPairedENegativeSource
public import SquaresInCircles.Eight.TableFree.GlobalGAOuterESelection

/-!
# BT2 with nonpositive selected A/T primary errors, arbitrary E

The original source owner flags are used literally: if an A primary is
selected, its own real angular error must be nonpositive. An unselected
primary has no sign restriction. The T primary is treated similarly.

When E is true-core, the complete core-E negative-source contradiction
already exhausts both E signs and all E owner alternatives. When E is
outer, pointwise same-state E reselection makes its selected total
nonnegative, and the original all-A/E signed stress excludes the source.
No A/T/E geometric point is changed in this branch. Weak ties are kept.

This is a source draft, not an ordinary-kernel verified result.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.HighGABT2
open Candidate SignedCycle

variable {q : ℝ} {C : SignedCycle} (I : GlobalGA.SourceDomain q C)

def tdFlag : Bool := decide (I.owner T=2)

theorem td_owner : I.owner T=(if tdFlag I then 2 else 0) := by
  have h : I.owner T=0∨I.owner T=2 := by
    simpa [GlobalGA.highGAOwners,T] using I.allowed T
  rcases h with h|h
  · simp [tdFlag,h]
  · simp [tdFlag,h]

theorem gaFlag_true (h : gaFlag I=true) : I.owner G=3 := by
  simpa [gaFlag] using h

theorem abFlag_true (h : abFlag I=true) : I.owner A=2 := by
  simpa [abFlag] using h

theorem tdFlag_true (h : tdFlag I=true) : I.owner T=2 := by
  simpa [tdFlag] using h

/-- An original source whose actually selected A/T primary errors are
all nonpositive is impossible, regardless of E radial kind/owners/errors.
No condition is imposed on the A total of omitted primary errors. -/
theorem nonpositive_A_T_primaries_false
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hBT : C.Feasible B 2)
    (hga : I.owner G=3 → delta C.theta G≤0)
    (hab : I.owner A=2 → delta C.theta A≤0)
    (htd : I.owner T=2 → delta C.theta T≤0) : False := by
  rcases I.radial E with houter|hcore
  · let S := GlobalGA.OuterE.select I hqU houter
    have hGA : C.Feasible G (if gaFlag I then 3 else 2) := by
      rw [←ga_owner I]
      exact I.feasible G
    have hAB : C.Feasible A (if abFlag I then 2 else 0) := by
      rw [←ab_owner I]
      exact I.feasible A
    have hTD : C.Feasible T (if tdFlag I then 2 else 0) := by
      rw [←td_owner I]
      exact I.feasible T
    exact GlobalGA.PairedE.Negative.actual_false
      (gaFlag I) (abFlag I) (tdFlag I) S.de S.eh
      I.necessary.sorted I.necessary.contained I.necessary.core hqU
      I.H_positive.le I.G_negative.le I.B_negative.le I.D_negative.le
      I.positive_variation.le (original_HG I)
      hGA hAB hBT hTD S.DE S.EH
      (fun h => hga (gaFlag_true I h))
      (fun h => hab (abFlag_true I h))
      (fun h => htd (tdFlag_true I h))
      S.total_nonneg
  · exact GlobalGA.CoreENegativeTotal.source_false I hqL hqU
      hcore hBT hga hab htd

end SquaresInCircles.Eight.TableFree.HighGABT2
