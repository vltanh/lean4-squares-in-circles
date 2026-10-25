module

public import SquaresInCircles.Eight.TableFree.GlobalGAHighBT2CoreEFirstPositiveTD2
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeAShortESource
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeALongESource

/-!
# Negative-A, nonnegative-E source contradiction, any E radial kind

This is the literal short/long signed-E split of the hand proof,
expressed solely on a necessary SignedCycle at the original squared
radius. In particular it is valid when the *original* E was true-core
and was normalized before A, and does not assume the transported A
or E locations define another physical packing.

Inputs include the real chosen DE/EH axes and the nonnegative
sum of their selected signed primary errors. The A genuine-primary
flat/tangent cut is derived by the entry theorem in the callers.
No source owner is manufactured and zero weak ties are retained.

Source draft only; no Lean compilation or CI has been performed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.HighGABT2
open Candidate SignedCycle

/-- A genuinely negative single A primary, with nonnegative selected
E total, positive TD2, and arbitrary actual weak HG owner, is impossible.
The selected E owners may be D2/E0, D3/E0, D2/E1 or D3/E1, and their
individual signed errors are *not* assumed to be nonnegative. -/
theorem negative_A_nonnegative_E_positive_TD2_raw_false
    {q s : ℝ} {C : SignedCycle}
    (atG de eh : Bool)
    (hsorted : ∀i,(C.point i).Sorted)
    (hcontained : ∀i,(C.point i).Contained q)
    (hqU : q≤qCap)
    (hH : 0≤(C.point H).y) (hG : (C.point G).y≤0)
    (hB : (C.point B).y≤0) (hD : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hs : s∈Icc 0 (GlobalGA.NegativeAPositiveTD.Explicit.angleCut atG))
    (ha : GlobalGA.NegativeAPositiveTD.Source.aError C atG= -s)
    (hflat : (C.point A).a=7/12)
    (hAy : 0≤(C.point A).y)
    (hcut : (C.point A).y≤ if atG then 39/250 else 1/2)
    (he : 0≤GlobalGA.PairedE.cycleTotal C de eh)
    (hz : 0≤delta C.theta T)
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 2)
    (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0)) : False := by
  have hfinish (hg : Fin 4) (hhg : hg=0∨hg=2)
      (hHG' : C.Feasible H hg) : False := by
    by_cases hsmall : GlobalGA.PairedE.cycleTotal C de eh≤ s
    · exact GlobalGA.NegativeA.ShortE.original atG de eh
        hsorted hcontained hqU hH hG hB hD hvar hs ha hflat
        hAy hcut ⟨he,hsmall⟩ hz hhg hHG'
        hGA hAB hBT hTD hDE hEH
    · exact GlobalGA.NegativeA.LongE.original atG de eh
        hsorted hcontained hqU hH hG hB hD hvar hs ha hflat
        hAy (le_of_lt (lt_of_not_ge hsmall)) hz hhg hHG'
        hGA hAB hBT hTD hDE hEH
  rcases hHG with hh|hh
  · exact hfinish 0 (Or.inl rfl) hh
  · exact hfinish 2 (Or.inr rfl) hh

end SquaresInCircles.Eight.TableFree.HighGABT2
