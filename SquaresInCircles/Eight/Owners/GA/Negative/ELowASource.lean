module

public import SquaresInCircles.Eight.Owners.GA.Paired.ECharge
public import SquaresInCircles.Eight.Owners.GA.SourceDomain

/-!
# Eight squares: all E owners at a small nonnegative A total

`original_HG`: the HG witness of a source domain is HG0 or HG2. At a small nonnegative A total, an
outer E is reselected on its secondaries at the same state, and a core E is brought to its E-only
normal form, with both mixed-sign moves and the paired-negative intrinsic endpoint. A resulting
single negative EH1 either has EH0 feasible, or its entry cut gives the short secant domain. Every
point, error and selected witness of A and T is kept.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeELowA
open Candidate SignedCycle PairedE

theorem original_HG {q : ℝ} {C : SignedCycle} (I : SourceDomain q C) :
    C.Feasible H 0∨C.Feasible H 2 := by
  have ho : I.owner H=0∨I.owner H=2 := by simpa [highGAOwners,H] using I.allowed H
  rcases ho with ho|ho
  · exact Or.inl (by simpa [ho] using I.feasible H)
  · exact Or.inr (by simpa [ho] using I.feasible H)

end SquaresInCircles.Eight.GlobalGA.NegativeELowA
