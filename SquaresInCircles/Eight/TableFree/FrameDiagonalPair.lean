module

public import SquaresInCircles.Eight.TableFree.FrameDiagonalOriginal

/-!
# Complete physical middle/high and high/high pair entries

All four original weak forward owners and both closed intrinsic cuts
are retained.  These adapters introduce no frame-window or quarter-word
hypothesis.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree.FrameDiagonalPair
open FramePair FrameDiagonalTransport FrameDiagonalOriginal

theorem middle_high_pair (s t : FramePair.State)
    (hs : s.branch=.middle) (ht : t.branch=.high) (j : Fin 4) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t j x) :
    handGamma s.branch.type t.branch.type<s.cost t x :=
  original_pair true false s t hs ht (Or.inr rfl) j hgap hm

theorem high_middle_pair (s t : FramePair.State)
    (hs : s.branch=.high) (ht : t.branch=.middle) (j : Fin 4) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t j x) :
    handGamma s.branch.type t.branch.type<s.cost t x :=
  original_pair false true s t hs ht (Or.inl rfl) j hgap hm

theorem high_high_pair (s t : FramePair.State)
    (hs : s.branch=.high) (ht : t.branch=.high) (j : Fin 4) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t j x) :
    handGamma s.branch.type t.branch.type<s.cost t x :=
  original_pair false false s t hs ht (Or.inl rfl) j hgap hm

theorem middle_high_cycle_pair (C : BoundaryCycle Q0) (i : Vertex)
    (hi : branchOf C i=.middle) (hj : branchOf C (next i)=.high)
    (j : Fin 4) (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    handGamma (branchOf C i).type (branchOf C (next i)).type<
      (stateOf C i).cost (stateOf C (next i)) (pairAngle C i) :=
  middle_high_pair (stateOf C i) (stateOf C (next i)) hi hj j
    (stateOf_gap_bounds C i).1.le (stateOf_feasible C i j haxis)

theorem high_middle_cycle_pair (C : BoundaryCycle Q0) (i : Vertex)
    (hi : branchOf C i=.high) (hj : branchOf C (next i)=.middle)
    (j : Fin 4) (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    handGamma (branchOf C i).type (branchOf C (next i)).type<
      (stateOf C i).cost (stateOf C (next i)) (pairAngle C i) :=
  high_middle_pair (stateOf C i) (stateOf C (next i)) hi hj j
    (stateOf_gap_bounds C i).1.le (stateOf_feasible C i j haxis)

theorem high_high_cycle_pair (C : BoundaryCycle Q0) (i : Vertex)
    (hi : branchOf C i=.high) (hj : branchOf C (next i)=.high)
    (j : Fin 4) (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    handGamma (branchOf C i).type (branchOf C (next i)).type<
      (stateOf C i).cost (stateOf C (next i)) (pairAngle C i) :=
  high_high_pair (stateOf C i) (stateOf C (next i)) hi hj j
    (stateOf_gap_bounds C i).1.le (stateOf_feasible C i j haxis)

end SquaresInCircles.Eight.TableFree.FrameDiagonalPair
