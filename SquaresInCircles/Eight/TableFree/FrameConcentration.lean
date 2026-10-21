module

public import SquaresInCircles.Eight.TableFree.FrameAllPairs
public import SquaresInCircles.Eight.TableFree.BoundaryBridge
public import SquaresInCircles.Eight.CycleActions

/-!
# Continuous frame concentration from the original seven-cycle

One intrinsic marker is retained at each original vertex.  The complete
continuous pair theorem is charged and telescoped before the shortest
orientation tour is lifted.  Both signed variation bounds then follow
from that same physical charge budget, without a candidate capture.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.FrameConcentration
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

theorem lift_spread {q : ℝ} {C : BoundaryCycle q} (F : QuarterLift C) (i j : Vertex) :
    |F.theta i-F.theta j|<frameCap := by
  have hi := F.theta_range i
  have hj := F.theta_range j
  have hsmall := F.small
  apply abs_lt.mpr
  dsimp [frameCap]
  constructor <;> linarith

theorem lift_step {q : ℝ} {C : BoundaryCycle q} (F : QuarterLift C) (i : Vertex) :
    |delta F.theta i|<frameCap := lift_spread F (next i) i

theorem lift_frameCost {q : ℝ} {C : BoundaryCycle q} (F : QuarterLift C) (i : Vertex) :
    frameCost |delta F.theta i|=
      periodicFrameCost (C.canonicalAngle (next i)-C.canonicalAngle i) := by
  have hs : |delta F.theta i|≤Real.pi/4 := by
    have hh := lift_step F i
    dsimp [frameCap] at hh
    linarith [Real.pi_gt_three]
  have hi : C.canonicalAngle i=F.theta i+(F.quarter i:ℝ)*(Real.pi/2) := F.represents i
  have hj : C.canonicalAngle (next i)=
      F.theta (next i)+(F.quarter (next i):ℝ)*(Real.pi/2) := F.represents (next i)
  have hid :
      (F.theta (next i)+(F.quarter (next i):ℝ)*(Real.pi/2))-
        (F.theta i+(F.quarter i:ℝ)*(Real.pi/2))=
      delta F.theta i+((F.quarter (next i)-F.quarter i:ℤ):ℝ)*(Real.pi/2) := by
    push_cast
    dsimp [delta]
    ring
  rw [hi,hj,hid,periodicFrameCost_int_quarter,periodicFrameCost_of_short hs]

theorem lift_variations_of_cost {q : ℝ} {C : BoundaryCycle q} (F : QuarterLift C)
    (hc : (∑ i,periodicFrameCost
      (C.canonicalAngle (next i)-C.canonicalAngle i))<10394/25425) :
    positiveVariation F.theta<frameCap ∧ negativeVariation F.theta<frameCap := by
  apply variations_lt_of_frameCost (fun i => (lift_step F i).le)
  simpa only [lift_frameCost F] using hc

theorem lift_variations (C : BoundaryCycle Q0) (F : QuarterLift C) :
    positiveVariation F.theta<frameCap ∧ negativeVariation F.theta<frameCap :=
  lift_variations_of_cost F (charge_budget C)

/-- The orientation representatives and their two actual variations are
obtained from the original cycle, before any word or owner classification. -/
theorem concentrated (C : BoundaryCycle Q0) :
    ∃ F : QuarterLift C,
      positiveVariation F.theta<frameCap ∧ negativeVariation F.theta<frameCap := by
  obtain ⟨F⟩ := quarter_lift C
  exact ⟨F,lift_variations C F⟩

end SquaresInCircles.Eight.TableFree.FrameConcentration
