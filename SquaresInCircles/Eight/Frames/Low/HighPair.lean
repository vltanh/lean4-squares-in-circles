module

public import SquaresInCircles.Eight.Frames.High.LowPrimary
public import SquaresInCircles.Eight.Frames.High.LowSecondary
public import SquaresInCircles.Eight.Frames.Low.HighSecondaryOpposite
public import SquaresInCircles.Eight.Frames.Low.HighPositiveLate
public import SquaresInCircles.Eight.Frames.Low.MidPair

/-!
# Eight squares: the complete original low/high frame-pair entry

Both ordered type arcs, all original tangent signs, every original
weak separating owner, and both intrinsic endpoint ties are included.
The target axes use exact reflected reversal.  No concentrated frame,
preferred owner, or contact conclusion is assumed.
-/

section
/-!
## The axes of a low source in a low/high pair

The secondary axis of a low source against a high target gives a cost above `8833/10000` for all
four signs of the two ends (`secondary_all`), and so does each axis of the low square on a
low/high edge at a gap of at least `19/25` (`source_secondary_low_high`,
`source_primary_low_high`). Reversing the pair turns the two axes of a low target on a high/low
edge into these (`target_secondary_high_low`, `target_primary_high_low`). Ties of the separating
axes and the ends of the arcs are included.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameLowHighSourceAxes
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameHighArc FrameLowHighGeometry

theorem secondary_all (i k : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0) (hx : -(34/125:ℝ)≤x)
    (hm : 0≤ secondary i k b B x) : (8833/10000:ℝ)<lowHighCost i k b B x := by
  cases i <;> cases k
  · exact FrameLowHighCuts.negative_negative_secondary hb hB hx hm
  · exact FrameLowHighSecondaryOpposite.weak_separator hb hB hx hm
  · exact FrameLowHighNegativeAngles.positive_negative_secondary hb hB hx hm
  · exact FrameLowHighPositiveLate.positive_positive_secondary hb hB hx hm

theorem source_secondary_low_high (s t : FramePair.State)
    (hs : s.branch=.low) (ht : t.branch=.high) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t 0 x) :
    (8833/10000:ℝ)<s.cost t x := by
  have hb := (state_low_chart s hs).2
  have hB := (state_high_chart t ht).2
  have hmargin := (FrameLowMidGeometry.state_secondary s t
    (by simp [ht,Branch.type]) x).mp hm
  have hx := low_high_angle s t hs hgap
  rw [state_low_high_cost s t hs ht]
  exact secondary_all s.positive t.positive hb hB hx.le hmargin

theorem source_primary_low_high (s t : FramePair.State)
    (hs : s.branch=.low) (ht : t.branch=.high) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t 3 x) :
    (8833/10000:ℝ)<s.cost t x := by
  have hb := (state_low_chart s hs).2
  have hB := (state_high_chart t ht).2
  have hmargin := (FrameLowMidGeometry.state_primary s t
    (by simp [hs,Branch.type]) (by simp [ht,Branch.type]) x).mp hm
  have hx := low_high_angle s t hs hgap
  rw [state_low_high_cost s t hs ht]
  exact FrameLowHighPrimaryPositive.low_high_primary s.positive t.positive hb hB hx.le hmargin

theorem target_secondary_high_low (s t : FramePair.State)
    (hs : s.branch=.high) (ht : t.branch=.low) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t 2 x) :
    (8833/10000:ℝ)<s.cost t x := by
  have hh := source_secondary_low_high t.flip s.flip
    (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
    (by simpa using hgap) ((s.target_secondary_reverse t x).mp hm)
  simpa using hh

theorem target_primary_high_low (s t : FramePair.State)
    (hs : s.branch=.high) (ht : t.branch=.low) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t 1 x) :
    (8833/10000:ℝ)<s.cost t x := by
  have hh := source_primary_low_high t.flip s.flip
    (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
    (by simpa using hgap) ((s.target_primary_reverse t x).mp hm)
  simpa using hh

end SquaresInCircles.Eight.FrameLowHighSourceAxes
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameLowHighPair
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

end SquaresInCircles.Eight.FrameLowHighPair
end
end
end
