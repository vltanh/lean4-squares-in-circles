module

public import SquaresInCircles.Eight.Owners.GA.Negative.ALongESource
public import SquaresInCircles.Eight.Owners.GA.Negative.AShortESource

/-!
# Eight squares: negative A and nonnegative E, for every radial kind of E

`negative_A_nonnegative_E_positive_TD2_raw_false` splits the signed E total against the angle `s`
of the negative A primary: a short total `≤ s` is excluded by `NegativeA.ShortE.original`, a long
one by `NegativeA.LongE.original`. It is stated on a signed cycle at the squared radius `q` that
satisfies the necessary inequalities, so it applies when E was on the core curve and was
normalized before A moved; the moved A and E need not form a packing.

The inputs are the chosen DE and EH axes and the nonnegative sum of their selected signed primary
errors. The flat and tangent cuts of the negative A primary are hypotheses, given by the entry
theorems. Weak ties with zero slack are kept.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.HighGABT2
open Candidate SignedCycle

/-- A single negative A primary, with a nonnegative selected E total, positive TD2 and either weak
HG owner, is impossible. The selected E owners may be D2/E0, D3/E0, D2/E1 or D3/E1, and their
signed errors need not be nonnegative one by one. -/
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

end SquaresInCircles.Eight.HighGABT2
