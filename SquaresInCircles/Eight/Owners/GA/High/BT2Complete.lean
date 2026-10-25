module

public import SquaresInCircles.Eight.Owners.GA.High.BT2CoreEFirstAllT
public import SquaresInCircles.Eight.Owners.GA.High.BT2ReducedANegativeOuterE
public import SquaresInCircles.Eight.Owners.GA.High.OwnerExit

/-!
# Eight squares: no high `GA` witness with a `BT2` witness

`high_GA_BT2_exclusion` proves `HighGABT2Exclusion`. When `E` is outer, normalizing `A`
suffices: the transported total of `A` is nonnegative or negative, and both owners and signs of
`TD` are excluded. When `E` is a core square, `E` is normalized before `A` moves, and the
core-`E` theorem for every sign of `T` excludes that case. The transports keep the seven
separating axes, the signed angular errors, the radial kinds and the squared radius `q`; a cycle
with `A` moved is used only as a signed cycle, not as a packing.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate SignedCycle

/-- No source domain of a high `GA` witness has a `BT2` witness, for every radial kind and
sign. -/
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

end SquaresInCircles.Eight
