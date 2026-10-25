module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeABT3ShortESource
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeABT3LongSource

/-!
# Negative A and positive BT3 with every nonnegative signed E total

Uncompiled final source theorem of the negative-A BT3 note. The two
original flat A normal forms are covered, as are all four E-owner
selections and their mixed individual signs. The comparison at e=s
joins the shorter and longer E proofs with no strict endpoint gap.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3
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

theorem frame_flat_false {q s : ℝ} {C : BoundaryCycle q} {hg : Fin 4}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0)
    (atG de eh : Bool) (hs : s∈Icc 0 (Explicit.angleCut atG))
    (ha : Source.aError (SignedCycle.atFrame F) atG= -s)
    (hflat : ((SignedCycle.atFrame F).point A).a=7/12)
    (hAy : 0≤((SignedCycle.atFrame F).point A).y)
    (hcut : ((SignedCycle.atFrame F).point A).y≤ if atG then 39/250 else 1/2)
    (he : 0≤PairedE.cycleTotal (SignedCycle.atFrame F) de eh)
    (hz : 0≤delta F.theta B) (hhg : hg=0∨hg=2)
    (hHG : (forwardAxis hg).Feasible (C.square H) (C.square G))
    (hGA : (forwardAxis (if atG then 3 else 2)).Feasible (C.square G) (C.square A))
    (hAB : (forwardAxis (if atG then 0 else 2)).Feasible (C.square A) (C.square B))
    (hBT : (forwardAxis 3).Feasible (C.square B) (C.square T))
    (hTD : (forwardAxis 0).Feasible (C.square T) (C.square D))
    (hDE : (forwardAxis (if de then 3 else 2)).Feasible (C.square D) (C.square E))
    (hEH : (forwardAxis (if eh then 1 else 0)).Feasible (C.square E) (C.square H)) : False := by
  by_cases hes : PairedE.cycleTotal (SignedCycle.atFrame F) de eh≤ s
  · exact ShortE.frame_flat_false F hq hE atG de eh hs ha hflat hAy hcut
      ⟨he,hes⟩ hz hhg hHG hGA hAB hBT hTD hDE hEH
  · exact LongE.frame_flat_false F hq hE atG de eh hs ha hflat hAy
      (lt_of_not_ge hes).le hz hhg hHG hGA hAB hBT hTD hDE hEH

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3
