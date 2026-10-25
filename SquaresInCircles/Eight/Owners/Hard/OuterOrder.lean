module

public import SquaresInCircles.Eight.Owners.Hard.OuterGeometry
public import SquaresInCircles.Eight.Words.Wrong.SignCapture

/-!
# Eight squares: intermediate order from the invariant actual endpoint budget

The original middle-order and one-tenth
arguments use E only through the already proved strict endpoint budget.
They therefore apply to local hard geometry and its physical reflection,
with no newly imposed sign or radial normalization at E.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.SignedCycle
open Candidate EndpointRotationPenalty EndpointBudgetScalars

theorem HardOuterGeometry.intermediate_order {q : ℝ}
    (I : HardOuterGeometry q) (hq : q≤qCap) : I.cycle.theta T<I.cycle.theta G := by
  by_contra! hGT
  obtain ⟨hHG,hTD⟩ := signed_outer_charges hq I.necessary I.anchors_normal
    I.witnesses I.zero_signs
  have hmiddle := middle_reverse_order_bound hq I.necessary I.anchors_normal
    I.witnesses I.GA_hard I.BT_hard hGT
  have hbudget := I.endpoint_bound hq
  dsimp [EndpointRotationPenalty.charge,epsilon] at hHG hTD hbudget
  linarith

theorem HardOuterGeometry.small_intermediate_signs {q : ℝ}
    (I : HardOuterGeometry q) (hq : q≤qCap) :
    (I.cycle.point G).y<(1/10 : ℝ) ∧ -(1/10 : ℝ)<(I.cycle.point T).y := by
  have horder := I.intermediate_order hq
  obtain ⟨hHG,hTD⟩ := signed_outer_charges hq I.necessary I.anchors_normal
    I.witnesses I.zero_signs
  have hend := I.endpoint_bound hq
  have hbudget : S0+epsilon< -(I.cycle.point G).y+(I.cycle.point T).y+
      EndpointRotationPenalty.charge*(I.cycle.theta G-I.cycle.theta T) := by
    dsimp [EndpointRotationPenalty.charge] at hHG hTD hend ⊢
    linarith
  have hfalse (hw : (1/10 : ℝ)≤(I.cycle.point G).y ∨
      (I.cycle.point T).y≤ -(1/10 : ℝ)) : False := by
    have hsmall := wrong_middle_bound hq I.necessary I.anchors_normal
      I.witnesses I.GA_hard I.BT_hard horder.le hw
    dsimp [epsilon] at hbudget
    linarith
  constructor
  · by_contra! h
    exact hfalse (Or.inl h)
  · by_contra! h
    exact hfalse (Or.inr h)

end SquaresInCircles.Eight.SignedCycle
