module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2Source
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeAFrameEntry

/-!
# The negative-flat-A / TD2 contradiction at the original boundary frame

Uncompiled source. The completed scalar-and-angle proof is applied to
the original physical owner witnesses, with the H/B/D anchors and G
sign supplied by the existing original-frame lemmas.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD
open Candidate Secondary

theorem frame_flat_false {q s : ℝ} {C : BoundaryCycle q} {hg : Fin 4}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0)
    (atG : Bool) (hs : s∈Icc 0 (Explicit.angleCut atG))
    (ha : Source.aError (SignedCycle.atFrame F) atG=-s)
    (hflat : ((SignedCycle.atFrame F).point A).a=7/12) (hz : 0≤delta F.theta T)
    (hhg : hg=0∨hg=2)
    (hHG : (forwardAxis hg).Feasible (C.square H) (C.square G))
    (hGA : (forwardAxis (if atG then 3 else 2)).Feasible (C.square G) (C.square A))
    (hAB : (forwardAxis (if atG then 0 else 2)).Feasible (C.square A) (C.square B))
    (hBT : (forwardAxis 2).Feasible (C.square B) (C.square T))
    (hTD : (forwardAxis 2).Feasible (C.square T) (C.square D))
    (hDE : (forwardAxis 2).Feasible (C.square D) (C.square E))
    (hEH : (forwardAxis 0).Feasible (C.square E) (C.square H)) : False := by
  let S := SignedCycle.atFrame F
  have hn := SignedCycle.atFrame_necessary F
  have hv := FramePhysicalTransport.candidate_variations F hq
  obtain ⟨hH,hHy,hB,hBy,hD,hDy⟩ := GlobalOriginalOwners.atFrame_anchors F hq hE
  have hhigh : (if atG then (3:Fin 4) else 2)=2∨(if atG then (3:Fin 4) else 2)=3 := by
    cases atG <;> simp
  have hG := GlobalQuarterOuter.frame_high_anchor F hq G (by norm_num [word,G])
    (if atG then 3 else 2) hhigh (by simpa [G,A,next] using hGA)
  have hGy : (S.point G).y≤0 := ((SignedCycle.atFrame_y_neg_iff F G).2 hG.2).le
  apply Source.original atG hn.sorted hn.contained hq.2 hHy.le hGy hBy.le hDy.le
    hv.1.le hs ha hflat hz hhg
  · exact (SignedCycle.atFrame_feasible F H hg).2 (by simpa [H,G,next] using hHG)
  · exact (SignedCycle.atFrame_feasible F G (if atG then 3 else 2)).2 (by simpa [G,A,next] using hGA)
  · exact (SignedCycle.atFrame_feasible F A (if atG then 0 else 2)).2 (by simpa [A,B,next] using hAB)
  · exact (SignedCycle.atFrame_feasible F B 2).2 (by simpa [B,T,next] using hBT)
  · exact (SignedCycle.atFrame_feasible F T 2).2 (by simpa [T,D,next] using hTD)
  · exact (SignedCycle.atFrame_feasible F D 2).2 (by simpa [D,E,next] using hDE)
  · exact (SignedCycle.atFrame_feasible F E 0).2 (by simpa [E,H,next] using hEH)

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD
