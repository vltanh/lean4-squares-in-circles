module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHBT3Source

/-!
# Original physical EH1 / BT3 exclusion and weak EH ties

Uncompiled source integration. A secondary EH0 already present on the
original pair is handled by its own existing source theorem. A selected
EH1 of nonnegative error uses the nonnegative-total theorem. The sole
negative EH1 uses the new four-family contradiction. No angle or point
is transported, and no physical witness is invented.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.Source
open Candidate Secondary PositiveAngularEnvelope

/-- All EH errors and both actual EH owners, with DE2 and nonnegative
selected A total. The equality case of every sign split is included. -/
theorem all_EH_false {Q : ℝ} {C : SignedCycle} (ga ab : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q) (hQ : Q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point Candidate.D).y≤0)
    (hEy : (C.point E).y≤0) (hEc : (C.point E).Core)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta B)
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 3) (hTD : C.Feasible T 0)
    (hDE : C.Feasible Candidate.D 2) (hEH : C.Feasible E 0∨C.Feasible E 1) : False := by
  by_cases hzero : C.Feasible E 0
  · have he : 0≤PositiveBT3.Source.eTotal C false false := by
      simp [PositiveBT3.Source.eTotal,PairedE.total,PairedE.selected]
    exact PositiveBT3.Source.actual_false ga ab false false hsorted hcontained hQ
      hHy hGy hBy hDy hvar ha hz he hHG hGA hAB hBT hTD hDE hzero
  · have hprimary : C.Feasible E 1 := hEH.resolve_left hzero
    by_cases hsign : 0≤delta C.theta E
    · have he : 0≤PositiveBT3.Source.eTotal C false true := by
        simpa [PositiveBT3.Source.eTotal,PairedE.total,PairedE.selected] using hsign
      exact PositiveBT3.Source.actual_false ga ab false true hsorted hcontained hQ
        hHy hGy hBy hDy hvar ha hz he hHG hGA hAB hBT hTD hDE hprimary
    · exact actual_false ga ab hsorted hcontained hQ hHy hGy hBy hDy hEy hEc
        hvar ha hz (lt_of_not_ge hsign) hzero hHG hGA hAB hBT hTD hDE hprimary

/-- Original-radius physical version. The HG witness is extracted from
the original frame, not supplied as a favorable representative. -/
theorem frame_false {Q : ℝ} {C : BoundaryCycle Q}
    (F : Candidate.Frame C) (hQ : Q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0)
    (ga ab : Bool) (hEc : ((SignedCycle.atFrame F).point E).Core)
    (ha : 0≤aTotal (SignedCycle.atFrame F) ga ab) (hz : 0≤delta F.theta B)
    (hGA : (forwardAxis (if ga then 3 else 2)).Feasible (C.square G) (C.square A))
    (hAB : (forwardAxis (if ab then 2 else 0)).Feasible (C.square A) (C.square B))
    (hBT : (forwardAxis 3).Feasible (C.square B) (C.square T))
    (hTD : (forwardAxis 0).Feasible (C.square T) (C.square Candidate.D))
    (hDE : (forwardAxis 2).Feasible (C.square Candidate.D) (C.square E))
    (hEH : (forwardAxis 0).Feasible (C.square E) (C.square H)∨
      (forwardAxis 1).Feasible (C.square E) (C.square H)) : False := by
  have hn := SignedCycle.atFrame_necessary F
  have hv := FramePhysicalTransport.candidate_variations F hQ
  obtain ⟨hH,hHy,hB,hBy,hD,hDy⟩ := GlobalOriginalOwners.atFrame_anchors F hQ hE
  have hhigh : (if ga then (3:Fin 4) else 2)=2∨(if ga then (3:Fin 4) else 2)=3 := by
    cases ga <;> simp
  have hG := GlobalQuarterOuter.frame_high_anchor F hQ G (by norm_num [word,G])
    (if ga then 3 else 2) hhigh (by simpa [G,A,next] using hGA)
  have hGy : ((SignedCycle.atFrame F).point G).y≤0 :=
    ((SignedCycle.atFrame_y_neg_iff F G).2 hG.2).le
  have hEy : ((SignedCycle.atFrame F).point E).y≤0 :=
    (SignedCycle.atFrame_y_nonpos_iff F E).2 hE
  let j := SignedCycle.retainedOwner F H
  have hj := (SignedCycle.atFrame_feasible F H j).1 (SignedCycle.retainedOwner_feasible F H)
  have hHG : (SignedCycle.atFrame F).Feasible H 0∨(SignedCycle.atFrame F).Feasible H 2 := by
    rcases GlobalZeroSign.of_frame F hQ H (by norm_num [word,H]) j hj with hh|hh
    · exact Or.inl (by simpa [hh.1] using SignedCycle.retainedOwner_feasible F H)
    · exact Or.inr (by simpa [hh.1] using SignedCycle.retainedOwner_feasible F H)
  apply all_EH_false ga ab hn.sorted hn.contained hQ.2 hHy.le hGy hBy.le hDy.le
    hEy hEc hv.1.le ha hz hHG
  · exact (SignedCycle.atFrame_feasible F G _).2 (by simpa [G,A,next] using hGA)
  · exact (SignedCycle.atFrame_feasible F A _).2 (by simpa [A,B,next] using hAB)
  · exact (SignedCycle.atFrame_feasible F B 3).2 (by simpa [B,T,next] using hBT)
  · exact (SignedCycle.atFrame_feasible F T 0).2 (by simpa [T,Candidate.D,next] using hTD)
  · exact (SignedCycle.atFrame_feasible F Candidate.D 2).2 (by simpa [Candidate.D,E,next] using hDE)
  · rcases hEH with hh|hh
    · exact Or.inl ((SignedCycle.atFrame_feasible F E 0).2 (by simpa [E,H,next] using hh))
    · exact Or.inr ((SignedCycle.atFrame_feasible F E 1).2 (by simpa [E,H,next] using hh))

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.Source
