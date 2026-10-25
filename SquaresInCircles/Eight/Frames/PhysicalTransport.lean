module

public import SquaresInCircles.Eight.Boundary.SourcePrimaryRecovery
public import SquaresInCircles.Eight.Boundary.CycleActions
public import SquaresInCircles.Eight.Frames.Core.HighPair
public import SquaresInCircles.Eight.Frames.Core.LowPair
public import SquaresInCircles.Eight.Frames.Core.MidPair
public import SquaresInCircles.Eight.Frames.Diagonal.Pair
public import SquaresInCircles.Eight.Frames.Low.HighPair
public import SquaresInCircles.Eight.Frames.Low.MidPair
public import SquaresInCircles.Eight.Frames.Mid.HighQuarterStrip

/-!
# Eight squares: frame concentration at the original physical radius

The auxiliary circle is used only to prove the orientation-tour budget.
Its canonical angles agree exactly with those of the source cycle.  The
resulting lift and both signed variations therefore belong to the source
radius, source square records, and every original weak separating axis.
-/

section
/-!
## The four-type pair inequality on every edge

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
end
end
end

section
/-!
## Concentration of the frames

Each vertex of a boundary cycle at `Q0` keeps one marker. Adding the charged pair bounds of
`continuous_pair_bound` round the cycle, the markers telescope, and the bound of the closed walks
on the four types gives `3881/625 < 2π - (9/50) ∑ frame costs` (`charged_cycle_budget`); so the
frame costs of the steps add up to less than `10394/25425` (`charge_budget`). The frames then
have a quarter lift (`quarter_lift`), and both signed variations are bounded by the same budget.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.FrameConcentration
open Candidate

theorem charged_cycle_budget (C : BoundaryCycle Q0) :
    (3881/625:ℝ)<2*Real.pi-(9/50)*∑ i,
      periodicFrameCost (C.canonicalAngle (next i)-C.canonicalAngle i) := by
  obtain ⟨τ,ψ,hpair⟩ := FrameAllPairs.continuous_pair_bound C
  have h := four_type_cycle_budget τ (angleGap C.beta)
    (fun i => periodicFrameCost (C.canonicalAngle (next i)-C.canonicalAngle i)) ψ hpair
  rwa [angleGap_sum] at h

theorem charge_budget (C : BoundaryCycle Q0) :
    (∑ i,periodicFrameCost (C.canonicalAngle (next i)-C.canonicalAngle i))<10394/25425 := by
  have h := charged_cycle_budget C
  linarith [Arithmetic.two_pi_lt_710_over_113]

theorem quarter_lift (C : BoundaryCycle Q0) : Nonempty (QuarterLift C) :=
  quarterLift_of_cost C (charge_budget C)

end SquaresInCircles.Eight.FrameConcentration
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.FramePhysicalTransport
open Candidate

theorem canonical_eq {q r : ℝ} {C : BoundaryCycle q} {D : BoundaryCycle r}
    (hR : RadiusExpansion C D) (i : Vertex) : D.canonicalAngle i=C.canonicalAngle i := by
  simp only [BoundaryCycle.canonicalAngle,BoundaryCycle.alpha,hR.same_rays,hR.same_tangents]

theorem charge_eq {q r : ℝ} {C : BoundaryCycle q} {D : BoundaryCycle r}
    (hR : RadiusExpansion C D) :
    (∑ i,periodicFrameCost (D.canonicalAngle (next i)-D.canonicalAngle i))=
      ∑ i,periodicFrameCost (C.canonicalAngle (next i)-C.canonicalAngle i) := by
  simp only [canonical_eq hR]

theorem charge_budget_of_expansion {q : ℝ} {C : BoundaryCycle q}
    {D : BoundaryCycle Q0} (hR : RadiusExpansion C D) :
    (∑ i,periodicFrameCost (C.canonicalAngle (next i)-C.canonicalAngle i))<10394/25425 := by
  rw [← charge_eq hR]
  exact FrameConcentration.charge_budget D

def auxiliary {q : ℝ} (C : BoundaryCycle q) (hq : q∈Icc (5/2:ℝ) Q0) :
    BoundaryCycle Q0 :=
  C.expand ⟨hq.1,hq.2.trans (by norm_num [Q0])⟩ (by norm_num [Q0]) hq.2

theorem auxiliary_expansion {q : ℝ} (C : BoundaryCycle q) (hq : q∈Icc (5/2:ℝ) Q0) :
    RadiusExpansion C (auxiliary C hq) :=
  C.expand_spec ⟨hq.1,hq.2.trans (by norm_num [Q0])⟩ (by norm_num [Q0]) hq.2

@[simp] theorem auxiliary_selected {q : ℝ} (C : BoundaryCycle q)
    (hq : q∈Icc (5/2:ℝ) Q0) : (auxiliary C hq).selected=C.selected := rfl

theorem charge_budget {q : ℝ} (C : BoundaryCycle q) (hq : q∈Icc (5/2:ℝ) Q0) :
    (∑ i,periodicFrameCost (C.canonicalAngle (next i)-C.canonicalAngle i))<10394/25425 :=
  charge_budget_of_expansion (auxiliary_expansion C hq)

theorem quarter_lift {q : ℝ} (C : BoundaryCycle q) (hq : q∈Icc (5/2:ℝ) Q0) :
    Nonempty (QuarterLift C) := by
  obtain ⟨F⟩ := FrameConcentration.quarter_lift (auxiliary C hq)
  exact ⟨F.pullback (auxiliary_expansion C hq)⟩

def quarterPushforward {q r : ℝ} {C : BoundaryCycle q} {D : BoundaryCycle r}
    (F : QuarterLift C) (hR : RadiusExpansion C D) : QuarterLift D where
  theta := F.theta
  quarter := F.quarter
  left := F.left
  diameter := F.diameter
  small := F.small
  theta_range := F.theta_range
  represents i := by
    change D.canonicalAngle i=_
    rw [canonical_eq hR]
    exact F.represents i

theorem quarterPushforward_word {q r : ℝ} {C : BoundaryCycle q} {D : BoundaryCycle r}
    (F : QuarterLift C) (hR : RadiusExpansion C D)
    (hC : ∀ i,19/25<angleGap C.beta i) (hD : ∀ i,19/25<angleGap D.beta i) :
    (quarterPushforward F hR).word hD pi_lt_22_over_7=F.word hC pi_lt_22_over_7 := by
  funext i
  apply Fin.ext
  rfl

def candidatePushforward {q r : ℝ} {C : BoundaryCycle q} {D : BoundaryCycle r}
    (F : Candidate.Frame C) (hR : RadiusExpansion C D) (hr : r≤Q0) : Candidate.Frame D where
  theta := F.theta
  theta_A := F.theta_A
  canonical_eq i := by rw [canonical_eq hR]; exact F.canonical_eq i
  spread := F.spread
  gap_lower i := by simpa only [hR.same_rays] using F.gap_lower i
  gap_upper i := by simpa only [hR.same_rays] using F.gap_upper i
  forward_complete := boundary_forward_complete D hr

theorem candidate_variations {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0) :
    positiveVariation (SignedCycle.atFrame F).theta<frameCap ∧
      negativeVariation (SignedCycle.atFrame F).theta<frameCap :=
  atFrame_variations_of_actual_cost F (charge_budget C hq)

end SquaresInCircles.Eight.FramePhysicalTransport
end
end
end
