module

public import SquaresInCircles.Eight.TableFree.GlobalGAHighBT2CoreEFirstAllT
public import SquaresInCircles.Eight.TableFree.GlobalGAHighBT2ReducedANegativeOuterE
public import SquaresInCircles.Eight.TableFree.GlobalGAHighOwnerExit

/-!
# Unconditional original high-GA BT2 exclusion

This is the final whole-domain mathematical dispatch for the high-GA
BT2 sector, not a definition of the obligation and not a case-restricted
adapter. For original outer E, A normalization alone suffices: the
transported A total is either nonnegative or genuinely negative, and
the existing source results cover both actual TD owners/signs. For
original true-core E, E normalization must happen before A motion;
the exhaustive core-E all-T source theorem proves that alternative.

The selected seven original weak axes, signed angular errors, radial
alternatives, and actual squared radius q are retained through every
source-domain transport. Any moved-A object is used only as a necessary
SignedCycle, not as a reconstructed original packing.

No axiom, generated owner table, compatibility capture or admission.
This is an uncompiled Lean draft and is not kernel-verified.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate SignedCycle

/-- A proof body for the previously *uninhabited* whole-domain
HighGABT2Exclusion proposition. The source is an arbitrary high-GA
physical owner system with both weak radial and signed alternatives. -/
theorem high_GA_BT2_exclusion : HighGABT2Exclusion := by
  intro q C I hqL hqU hBT
  rcases I.radial E with houter|hcore
  · obtain ⟨O⟩ := HighGABT2.A_normalize I hqL hqU
    by_cases ha : 0≤GlobalGA.NegativeANormalForm.total O.ga O.ab
        (delta O.cycle.theta G) (delta O.cycle.theta A)
    · exact HighGABT2.reduced_nonnegative_A_outer_E_false
        I O hqU hBT houter ha
    · exact HighGABT2.negative_A_outer_E_all_T_false
        I O hqL hqU houter hBT ha
  · exact HighGABT2.core_E_all_T_false I hqL hqU hcore hBT

/-- Strict original high-GA owner exclusion, including all ties and
each selected normal, is now a consequence, not a construction premise. -/
theorem high_GA_original_source_false
    {q : ℝ} {C : SignedCycle} (I : GlobalGA.SourceDomain q C)
    (hqL : qLow≤q) (hqU : q≤qCap) : False :=
  high_GA_source_false_of_BT2_exclusion high_GA_BT2_exclusion I hqL hqU

/-- The original physical GA owner must be low in every feasible
physical frame at the sharp working radius. No hypothetical new owner
is selected after transporting G or T. -/
theorem original_GA_low
    {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0)
    (hqL : qLow≤q) (hE : C.tangent E≤0) :
    ∀ j : Fin 4,
      (forwardAxis j).Feasible (C.square G) (C.square A) →
        j=0∨j=1 :=
  original_GA_low_of_BT2_exclusion
    high_GA_BT2_exclusion F hq hqL hE

end SquaresInCircles.Eight.TableFree
