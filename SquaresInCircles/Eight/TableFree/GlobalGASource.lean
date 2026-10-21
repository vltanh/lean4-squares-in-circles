module

public import SquaresInCircles.Eight.TableFree.GlobalOriginalOwners
public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveTDExclusion

/-!
# The full secondary-A/E high-GA row on the original boundary

The source bridge derives the anchor signs, true-core inequalities,
both possible original HG/TD owners, and the full signed variation
budget.  Its supplied hypotheses are only actual weak axes on the
five prescribed edges.  No support reserve or ordered frame is an
input.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalGA

open Candidate

theorem frame_secondary_row_false {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0)
    (hGA : (forwardAxis 2).Feasible (C.square G) (C.square A))
    (hAB : (forwardAxis 0).Feasible (C.square A) (C.square B))
    (hBT : (forwardAxis 2).Feasible (C.square B) (C.square T))
    (hDE : (forwardAxis 2).Feasible (C.square D) (C.square E))
    (hEH : (forwardAxis 0).Feasible (C.square E) (C.square H)) : False := by
  have hn := SignedCycle.atFrame_necessary F
  have hanchors := GlobalOriginalOwners.atFrame_anchors F hq hE
  have hG := GlobalQuarterOuter.frame_high_anchor F hq G
    (by norm_num [word,G]) 2 (Or.inl rfl) (by simpa [G,A,next] using hGA)
  have hz (i : Vertex) (hi : word i=0) :
      (SignedCycle.atFrame F).Feasible i 0 ∨ (SignedCycle.atFrame F).Feasible i 2 := by
    let j := SignedCycle.retainedOwner F i
    have hf : (SignedCycle.atFrame F).Feasible i j := SignedCycle.retainedOwner_feasible F i
    have ha := (SignedCycle.atFrame_feasible F i j).1 hf
    rcases GlobalZeroSign.of_frame F hq i hi j ha with hh | hh
    · exact Or.inl (by simpa [hh.1] using hf)
    · exact Or.inr (by simpa [hh.1] using hf)
  apply Secondary.actual_secondary_either_TD_false hn.sorted hn.contained (hn.core T)
    (show q≤qCap from hq.2)
    hanchors.2.1.le
    ((SignedCycle.atFrame_y_neg_iff F G).2 hG.2).le
    hanchors.2.2.2.1.le hanchors.2.2.2.2.2.le
    (FramePhysicalTransport.candidate_variations F hq).1.le
    (hz H (by norm_num [word,H]))
  · exact (SignedCycle.atFrame_feasible F G 2).2 (by simpa [G,A,next] using hGA)
  · exact (SignedCycle.atFrame_feasible F A 0).2 (by simpa [A,B,next] using hAB)
  · exact (SignedCycle.atFrame_feasible F B 2).2 (by simpa [B,T,next] using hBT)
  · exact hz T (by norm_num [word,T])
  · exact (SignedCycle.atFrame_feasible F D 2).2 (by simpa [D,E,next] using hDE)
  · exact (SignedCycle.atFrame_feasible F E 0).2 (by simpa [E,H,next] using hEH)

end SquaresInCircles.Eight.TableFree.GlobalGA
