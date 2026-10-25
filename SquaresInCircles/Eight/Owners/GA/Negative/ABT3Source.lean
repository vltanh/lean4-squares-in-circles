module

public import SquaresInCircles.Eight.Owners.GA.Negative.ABT3ShortESource
public import SquaresInCircles.Eight.Owners.GA.Negative.ABT3LongSource

/-!
# Eight squares: negative A and positive BT3 with every nonnegative signed E total

The two
original flat A normal forms are covered, as are all four E-owner
selections and their mixed individual signs. The comparison at e=s
joins the shorter and longer E proofs with no strict endpoint gap.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeABT3
open Candidate Secondary SignedStress

theorem original {q s : ℝ} {C : SignedCycle} {hg : Fin 4} (atG de eh : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hs : s∈Icc 0 (Explicit.angleCut atG)) (ha : Source.aError C atG= -s)
    (hflat : (C.point A).a=7/12) (hAy : 0≤(C.point A).y)
    (hcut : (C.point A).y≤ if atG then 39/250 else 1/2)
    (he : 0≤PairedE.cycleTotal C de eh) (hz : 0≤delta C.theta B)
    (hhg : hg=0∨hg=2) (hHG : C.Feasible H hg)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2)) (hBT : C.Feasible B 3)
    (hTD : C.Feasible T 0) (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0)) : False := by
  by_cases hes : PairedE.cycleTotal C de eh≤ s
  · exact ShortE.original atG de eh hsorted hcontained hq hHy hGy hBy hDy hvar
      hs ha hflat hAy hcut ⟨he,hes⟩ hz hhg hHG hGA hAB hBT hTD hDE hEH
  · exact LongE.original atG de eh hsorted hcontained hq hHy hGy hBy hDy hvar
      hs ha hflat hAy (lt_of_not_ge hes).le hz hhg hHG hGA hAB hBT hTD hDE hEH

end SquaresInCircles.Eight.GlobalGA.NegativeABT3
