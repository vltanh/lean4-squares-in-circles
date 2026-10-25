module

public import SquaresInCircles.Eight.Frames.Core.HighPair
public import SquaresInCircles.Eight.Frames.Core.LowPair
public import SquaresInCircles.Eight.Frames.Core.MidPair
public import SquaresInCircles.Eight.Frames.Diagonal.Pair
public import SquaresInCircles.Eight.Frames.Low.HighPair
public import SquaresInCircles.Eight.Frames.Low.MidPair
public import SquaresInCircles.Eight.Frames.Mid.MidPair

/-!
# Eight squares: the four-type pair inequality on every edge

Each vertex of a boundary cycle at `Q0` has one type, the core or the low, middle or high range of
the outer circle, and one state, both read from its coordinates (`branchOf`, `stateOf`). On every
edge, each signed axis that separates the two squares, ties included, gives `γ(s, t) < cost`: the
bound `handGamma` of the two types is below the cost of the pair of states at the angle between
their frames (`forward_pair`, `original_axis_pair`, `all_pair`). The proof distinguishes the
types of the two ends, each case being a theorem on the whole domain of the pair. With the
markers of the states this is the charged bound `continuous_pair_bound`: `γ(τᵢ, τᵢ₊₁)` is below
the gap less `9/50` times the frame cost, plus the difference of the markers.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.FrameAllPairs
open FramePair

theorem forward_pair (C : BoundaryCycle Q0) (i : Vertex) (j : Fin 4)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    handGamma (branchOf C i).type (branchOf C (next i)).type<
      (stateOf C i).cost (stateOf C (next i)) (pairAngle C i) := by
  by_cases hci : (branchOf C i).type=0
  · by_cases hcj : (branchOf C (next i)).type=0
    · exact core_cycle_pair C i hci hcj
    · cases hj : branchOf C (next i) <;> simp [hj,Branch.type] at hcj
      · simpa only [hj] using FrameCoreLowPair.core_low_cycle_pair C i hci hj j haxis
      · simpa only [hj] using FrameCoreMidPair.core_mid_cycle_pair C i hci hj j haxis
      · simpa only [hj] using FrameCoreHighPair.core_high_cycle_pair C i hci hj j haxis
  · by_cases hcj : (branchOf C (next i)).type=0
    · cases hi : branchOf C i <;> simp [hi,Branch.type] at hci
      · simpa only [hi] using FrameCoreLowPair.low_core_cycle_pair C i hi hcj j haxis
      · simpa only [hi] using FrameCoreMidPair.mid_core_cycle_pair C i hi hcj j haxis
      · simpa only [hi] using FrameCoreHighPair.high_core_cycle_pair C i hi hcj j haxis
    · cases hi : branchOf C i <;> cases hj : branchOf C (next i) <;>
        simp [hi,hj,Branch.type] at hci hcj
      all_goals first
        | simpa only [hi,hj] using FrameLowPair.low_cycle_pair C i hi hj j haxis
        | simpa only [hi,hj] using FrameLowMidPair.low_mid_cycle_pair C i hi hj j haxis
        | simpa only [hi,hj] using FrameLowHighPair.low_high_cycle_pair C i hi hj j haxis
        | simpa only [hi,hj] using FrameLowMidPair.mid_low_cycle_pair C i hi hj j haxis
        | simpa only [hi,hj] using FrameMidMidPair.middle_cycle_pair C i hi hj j haxis
        | simpa only [hi,hj] using FrameDiagonalPair.middle_high_cycle_pair C i hi hj j haxis
        | simpa only [hi,hj] using FrameLowHighPair.high_low_cycle_pair C i hi hj j haxis
        | simpa only [hi,hj] using FrameDiagonalPair.high_middle_cycle_pair C i hi hj j haxis
        | simpa only [hi,hj] using FrameDiagonalPair.high_high_cycle_pair C i hi hj j haxis

/-- The pair inequality holds for every signed axis that separates the two squares, ties
included. -/
theorem original_axis_pair (C : BoundaryCycle Q0) (i : Vertex) (axis : SignedAxis)
    (haxis : axis.Feasible (C.square i) (C.square (next i))) :
    handGamma (branchOf C i).type (branchOf C (next i)).type<
      (stateOf C i).cost (stateOf C (next i)) (pairAngle C i) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i axis haxis
  apply forward_pair C i j
  simpa only [hj] using haxis

/-- The pair inequality on every edge, from the witness of the edge. -/
theorem all_pair (C : BoundaryCycle Q0) (i : Vertex) :
    handGamma (branchOf C i).type (branchOf C (next i)).type<
      (stateOf C i).cost (stateOf C (next i)) (pairAngle C i) :=
  original_axis_pair C i (C.selected i) (C.feasible i)

theorem continuous_pair_bound (C : BoundaryCycle Q0) :
    ∃ (τ : Vertex → Fin 4) (ψ : Vertex → ℝ), ∀ i,
      handGamma (τ i) (τ (next i))<
        angleGap C.beta i-(9/50:ℝ)*periodicFrameCost
          (C.canonicalAngle (next i)-C.canonicalAngle i)+ψ (next i)-ψ i := by
  refine ⟨fun i => (branchOf C i).type,fun i => C.alpha i-(stateOf C i).signedLabel,?_⟩
  intro i
  have h := all_pair C i
  rwa [stateOf_cost] at h

end SquaresInCircles.Eight.FrameAllPairs
