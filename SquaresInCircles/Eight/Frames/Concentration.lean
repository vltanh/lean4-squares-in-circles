module

public import SquaresInCircles.Eight.Boundary.CycleActions
public import SquaresInCircles.Eight.Frames.AllPairs

/-!
# Eight squares: concentration of the frames

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
