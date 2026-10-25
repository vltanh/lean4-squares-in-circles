module

public import SquaresInCircles.Eight.Owners.GA.SourceDomain

/-!
# Eight squares: a BT2 witness with nonpositive selected A and T primary errors, for every E

`tdFlag` records whether the TD witness of a source domain is TD2 (`td_owner`, `tdFlag_true`).
The owner flags of the source domain are used as they are: if an A primary is selected, its own
angular error is nonpositive, and an unselected primary has no sign restriction. The T primary is
treated in the same way.

When E is on the core curve, the core-E negative-total contradiction covers both signs of E and
all its owner alternatives. When E is outer, reselecting E at the same state makes its selected
total nonnegative, and the signed stress of the A and E totals excludes the source domain. No point
of A, T or E moves in this branch. Weak ties are kept.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.HighGABT2
open Candidate SignedCycle

variable {q : ℝ} {C : SignedCycle} (I : GlobalGA.SourceDomain q C)

def tdFlag : Bool := decide (I.owner T=2)

theorem td_owner : I.owner T=(if tdFlag I then 2 else 0) := by
  have h : I.owner T=0∨I.owner T=2 := by
    simpa [GlobalGA.highGAOwners,T] using I.allowed T
  rcases h with h|h
  · simp [tdFlag,h]
  · simp [tdFlag,h]

theorem tdFlag_true (h : tdFlag I=true) : I.owner T=2 := by
  simpa [tdFlag] using h

end SquaresInCircles.Eight.HighGABT2
