module

public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsSourceData
public import SquaresInCircles.Eight.Owners.GA.SourceDomain

/-!
# Eight squares: the owner flags of a high-GA source domain

The stress of nonnegative A and E totals `NonnegativeTotals.all_TD_false` is a single scalar proof
for TD0, positive TD2 and negative TD2, with four Boolean owner flags. Here the flags `gaFlag`,
`abFlag`, `deFlag` and `ehFlag` are read off the seven chosen weak axes of a `SourceDomain`
(`ga_owner`, `ab_owner`, `de_owner`, `eh_owner`), and `aTotal` and `eTotal` are the signed totals of
the selected A and E primaries. No GA, AB, DE or EH witness is changed. Neither the signs of the
single A and E errors nor the radial kind of T are restricted.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate SignedCycle
namespace HighGABT2

variable {q : ℝ} {C : SignedCycle} (I : GlobalGA.SourceDomain q C)

/-- The primary flags are the owners of the source domain itself: GA3, AB2, DE3 and EH1. -/
def gaFlag : Bool := decide (I.owner G=3)
def abFlag : Bool := decide (I.owner A=2)
def deFlag : Bool := decide (I.owner D=3)
def ehFlag : Bool := decide (I.owner E=1)

theorem ga_owner :
    I.owner G=(if gaFlag I then 3 else 2) := by
  have h : I.owner G=2∨I.owner G=3 := by
    simpa [GlobalGA.highGAOwners,G] using I.allowed G
  rcases h with h|h
  · simp [gaFlag,h]
  · simp [gaFlag,h]

theorem ab_owner :
    I.owner A=(if abFlag I then 2 else 0) := by
  have h : I.owner A=0∨I.owner A=2 := by
    simpa [GlobalGA.highGAOwners,A] using I.allowed A
  rcases h with h|h
  · simp [abFlag,h]
  · simp [abFlag,h]

theorem de_owner :
    I.owner D=(if deFlag I then 3 else 2) := by
  have h : I.owner D=2∨I.owner D=3 := by
    simpa [GlobalGA.highGAOwners,D] using I.allowed D
  rcases h with h|h
  · simp [deFlag,h]
  · simp [deFlag,h]

theorem eh_owner :
    I.owner E=(if ehFlag I then 1 else 0) := by
  have h : I.owner E=0∨I.owner E=1 := by
    simpa [GlobalGA.highGAOwners,E] using I.allowed E
  rcases h with h|h
  · simp [ehFlag,h]
  · simp [ehFlag,h]

/-- The signed totals of the selected A and E primaries. An unselected primary contributes zero,
even when the error of its secondary is nonzero; the two primaries may have errors of opposite
signs. -/
def aTotal : ℝ :=
  GlobalGA.NonnegativeTotals.Source.aTotal C (gaFlag I) (abFlag I)
def eTotal : ℝ :=
  GlobalGA.NonnegativeTotals.Source.eTotal C (deFlag I) (ehFlag I)

include I in
theorem original_HG : C.Feasible H 0∨C.Feasible H 2 := by
  have h : I.owner H=0∨I.owner H=2 := by
    simpa [GlobalGA.highGAOwners,H] using I.allowed H
  rcases h with h|h
  · exact Or.inl (by simpa [h] using I.feasible H)
  · exact Or.inr (by simpa [h] using I.feasible H)

include I in
theorem original_TD : C.Feasible T 0∨C.Feasible T 2 := by
  have h : I.owner T=0∨I.owner T=2 := by
    simpa [GlobalGA.highGAOwners,T] using I.allowed T
  rcases h with h|h
  · exact Or.inl (by simpa [h] using I.feasible T)
  · exact Or.inr (by simpa [h] using I.feasible T)

end HighGABT2
end SquaresInCircles.Eight
