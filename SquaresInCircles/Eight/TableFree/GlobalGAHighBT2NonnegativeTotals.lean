module

public import SquaresInCircles.Eight.TableFree.GlobalGAHighBT2FiniteDispatch
public import SquaresInCircles.Eight.TableFree.GlobalGANonnegativeTotalsNegativeTDSource

/-!
# Whole original-source nonnegative A/E quadrant of the remaining BT2 gate

The already drafted NonnegativeTotals.NegativeTD.Source.all_TD_false contains
a single scalar proof for TD0, positive TD2 and negative TD2. Here its four
Boolean owner flags are recovered from the seven *actual* chosen weak axes of
SourceDomain. No GA/AB/DE/EH witness is silently changed or postulated.
Neither the individual A/E error signs nor T's radial kind are restricted.

Source-only Lean transcription. No compilation, tests or CI were run.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate SignedCycle
namespace HighGABT2

variable {q : ℝ} {C : SignedCycle} (I : GlobalGA.SourceDomain q C)

/-- Primary flags are exactly the initially retained high-GA source
owners, not new maximising or transport-selected witnesses. -/
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

/-- The precise signed totals of the selected original A/E primaries.
An absent primary contributes zero, even when its secondary error is
nonzero; both primaries may have opposite signed errors. -/
def aTotal : ℝ :=
  GlobalGA.NonnegativeTotals.Source.aTotal C (gaFlag I) (abFlag I)
def eTotal : ℝ :=
  GlobalGA.NonnegativeTotals.Source.eTotal C (deFlag I) (ehFlag I)

theorem original_HG : C.Feasible H 0∨C.Feasible H 2 := by
  have h : I.owner H=0∨I.owner H=2 := by
    simpa [GlobalGA.highGAOwners,H] using I.allowed H
  rcases h with h|h
  · exact Or.inl (by simpa [h] using I.feasible H)
  · exact Or.inr (by simpa [h] using I.feasible H)

theorem original_TD : C.Feasible T 0∨C.Feasible T 2 := by
  have h : I.owner T=0∨I.owner T=2 := by
    simpa [GlobalGA.highGAOwners,T] using I.allowed T
  rcases h with h|h
  · exact Or.inl (by simpa [h] using I.feasible T)
  · exact Or.inr (by simpa [h] using I.feasible T)

/-- The full nonnegative A/E selected-total BT2 source sector is
impossible for either real signed TD2 error and every weak zero tie.
The source is not moved; all seven feasibility hypotheses are obtained
from its actual witnesses. -/
theorem nonnegative_AE_false (hq : q≤qCap)
    (hBT : C.Feasible B 2) (ha : 0≤aTotal I) (he : 0≤eTotal I) : False := by
  have hGA : C.Feasible G (if gaFlag I then 3 else 2) := by
    rw [←ga_owner I]
    exact I.feasible G
  have hAB : C.Feasible A (if abFlag I then 2 else 0) := by
    rw [←ab_owner I]
    exact I.feasible A
  have hDE : C.Feasible D (if deFlag I then 3 else 2) := by
    rw [←de_owner I]
    exact I.feasible D
  have hEH : C.Feasible E (if ehFlag I then 1 else 0) := by
    rw [←eh_owner I]
    exact I.feasible E
  exact GlobalGA.NonnegativeTotals.NegativeTD.Source.all_TD_false
    (gaFlag I) (abFlag I) (deFlag I) (ehFlag I)
    I.necessary.sorted I.necessary.contained (I.necessary.core T) hq
    I.H_positive.le I.G_negative.le I.B_negative.le I.D_negative.le
    I.positive_variation.le ha he
    (original_HG I) hGA hAB hBT (original_TD I) hDE hEH

end HighGABT2
end SquaresInCircles.Eight.TableFree
