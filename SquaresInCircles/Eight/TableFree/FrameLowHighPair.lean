module

public import SquaresInCircles.Eight.TableFree.FrameLowHighSourceAxes
public import SquaresInCircles.Eight.TableFree.FrameHighLowSecondary
public import SquaresInCircles.Eight.TableFree.FrameHighLowPrimary

/-!
# The complete original low/high frame-pair entry

Both ordered type arcs, all original tangent signs, every original
weak separating owner, and both intrinsic endpoint ties are included.
The target axes use exact reflected reversal.  No concentrated frame,
preferred owner, or contact conclusion is assumed.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameLowHighPair
open FramePair FrameCircleArc
open FrameLowHighSourceAxes FrameHighLowSecondary FrameHighLowPrimary

theorem low_high_pair (s t : FramePair.State) (hs : s.branch=.low)
    (ht : t.branch=.high) (j : Fin 4) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t j x) :
    handGamma s.branch.type t.branch.type<s.cost t x := by
  have hnum : handGamma s.branch.type t.branch.type=(8833/10000:ℝ) := by
    norm_num [hs,ht,Branch.type,handGamma,handGammaNumerator]
  rw [hnum]
  fin_cases j
  · exact source_secondary_low_high s t hs ht hgap hm
  · exact target_primary_low_high s t hs ht hgap hm
  · exact target_secondary_low_high s t hs ht hgap hm
  · exact source_primary_low_high s t hs ht hgap hm

theorem high_low_pair (s t : FramePair.State) (hs : s.branch=.high)
    (ht : t.branch=.low) (j : Fin 4) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t j x) :
    handGamma s.branch.type t.branch.type<s.cost t x := by
  have hnum : handGamma s.branch.type t.branch.type=(8833/10000:ℝ) := by
    norm_num [hs,ht,Branch.type,handGamma,handGammaNumerator]
  rw [hnum]
  fin_cases j
  · exact source_secondary_high_low s t hs ht hgap hm
  · exact target_primary_high_low s t hs ht hgap hm
  · exact target_secondary_high_low s t hs ht hgap hm
  · exact source_primary_high_low s t hs ht hgap hm

theorem low_high_cycle_pair (C : BoundaryCycle Q0) (i : Vertex)
    (hi : branchOf C i=.low) (hj : branchOf C (next i)=.high)
    (j : Fin 4) (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    handGamma (branchOf C i).type (branchOf C (next i)).type<
      (stateOf C i).cost (stateOf C (next i)) (pairAngle C i) := by
  exact low_high_pair (stateOf C i) (stateOf C (next i)) hi hj j
    (stateOf_gap_bounds C i).1.le (stateOf_feasible C i j haxis)

theorem high_low_cycle_pair (C : BoundaryCycle Q0) (i : Vertex)
    (hi : branchOf C i=.high) (hj : branchOf C (next i)=.low)
    (j : Fin 4) (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    handGamma (branchOf C i).type (branchOf C (next i)).type<
      (stateOf C i).cost (stateOf C (next i)) (pairAngle C i) := by
  exact high_low_pair (stateOf C i) (stateOf C (next i)) hi hj j
    (stateOf_gap_bounds C i).1.le (stateOf_feasible C i j haxis)

end SquaresInCircles.Eight.TableFree.FrameLowHighPair
