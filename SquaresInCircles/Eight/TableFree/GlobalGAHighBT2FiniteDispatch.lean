module

public import SquaresInCircles.Eight.TableFree.GlobalGAHighOwnerExit

/-!
# Exhaustive finite terminal dispatcher for the remaining high-GA BT2 gate

Uncompiled Lean proof of the *logic* of the finite partition.  It partitions
the actual current same-radius source by the retained TD owner, then by
its signed TD2 error or E radial kind. Every weak tie is included. It does
not claim the four remaining mathematical exclusions are already proved.

The source still has all seven real signed witnesses. Neither a specific
A/E-primary sign nor a high/low E witness is chosen by this dispatcher.
There are no new axioms, admissions, or generated word/owner inputs.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate SignedCycle

/-- BT2 and the actual TD0 owner on one high-GA source. -/
def HighGABT2TD0Exclusion : Prop :=
  ∀ {q : ℝ} {C : SignedCycle} (I : GlobalGA.SourceDomain q C),
    qLow≤q → q≤qCap → C.Feasible B 2 → C.Feasible T 0 → False

/-- BT2 and the actual TD2 owner on one high-GA source. -/
def HighGABT2TD2Exclusion : Prop :=
  ∀ {q : ℝ} {C : SignedCycle} (I : GlobalGA.SourceDomain q C),
    qLow≤q → q≤qCap → C.Feasible B 2 → C.Feasible T 2 → False

/-- The source's actual T owner is exactly 0 or 2. Both feasible
alternatives are retained at zero error; no strict case is needed. -/
theorem high_GA_BT2_of_TD_cases
    (hTD0 : HighGABT2TD0Exclusion)
    (hTD2 : HighGABT2TD2Exclusion) : HighGABT2Exclusion := by
  intro q C I hqL hqU hBT
  have ho : I.owner T=0∨I.owner T=2 := by
    simpa [GlobalGA.highGAOwners,T] using I.allowed T
  rcases ho with ho|ho
  · exact hTD0 I hqL hqU hBT (by simpa [ho] using I.feasible T)
  · exact hTD2 I hqL hqU hBT (by simpa [ho] using I.feasible T)

/-- Signed TD2 error ≤0; equality and simultaneous weak ties are included. -/
def HighGABT2TD2Nonpositive : Prop :=
  ∀ {q : ℝ} {C : SignedCycle} (I : GlobalGA.SourceDomain q C),
    qLow≤q → q≤qCap → C.Feasible B 2 → C.Feasible T 2 →
      delta C.theta T≤0 → False

/-- Strictly positive signed TD2 error. No A/E sign is assumed. -/
def HighGABT2TD2Positive : Prop :=
  ∀ {q : ℝ} {C : SignedCycle} (I : GlobalGA.SourceDomain q C),
    qLow≤q → q≤qCap → C.Feasible B 2 → C.Feasible T 2 →
      0<delta C.theta T → False

/-- The two actual TD2 sign halves cover all real errors, including zero. -/
theorem high_GA_BT2_TD2_of_sign_cases
    (hn : HighGABT2TD2Nonpositive)
    (hp : HighGABT2TD2Positive) : HighGABT2TD2Exclusion := by
  intro q C I hqL hqU hBT hTD
  by_cases hz : delta C.theta T≤0
  · exact hn I hqL hqU hBT hTD hz
  · exact hp I hqL hqU hBT hTD (lt_of_not_ge hz)

/-- Actual outer E, both weak E owners and every signed A/E total. -/
def HighGABT2TD0Outer : Prop :=
  ∀ {q : ℝ} {C : SignedCycle} (I : GlobalGA.SourceDomain q C),
    qLow≤q → q≤qCap → C.Feasible B 2 → C.Feasible T 0 →
      (C.point E).Outer q → False

/-- Actual true-core E, both weak E owners and every signed A/E total. -/
def HighGABT2TD0Core : Prop :=
  ∀ {q : ℝ} {C : SignedCycle} (I : GlobalGA.SourceDomain q C),
    qLow≤q → q≤qCap → C.Feasible B 2 → C.Feasible T 0 →
      (C.point E).Core → False

/-- Exactly the two actual E radial cases; original physical q unchanged. -/
theorem high_GA_BT2_TD0_of_radial_cases
    (ho : HighGABT2TD0Outer)
    (hc : HighGABT2TD0Core) : HighGABT2TD0Exclusion := by
  intro q C I hqL hqU hBT hTD
  rcases I.radial E with houter|hcore
  · exact ho I hqL hqU hBT hTD houter
  · exact hc I hqL hqU hBT hTD hcore

/-- Final *logical* dispatcher from exactly four whole-domain excluded
sectors. Its four inputs must be proved by geometric source inequalities
and A/E normal forms, not postulated. -/
theorem high_GA_BT2_exclusion_of_four_sectors
    (hOuter : HighGABT2TD0Outer) (hCore : HighGABT2TD0Core)
    (hNonpos : HighGABT2TD2Nonpositive)
    (hPositive : HighGABT2TD2Positive) : HighGABT2Exclusion :=
  high_GA_BT2_of_TD_cases
    (high_GA_BT2_TD0_of_radial_cases hOuter hCore)
    (high_GA_BT2_TD2_of_sign_cases hNonpos hPositive)

end SquaresInCircles.Eight.TableFree
