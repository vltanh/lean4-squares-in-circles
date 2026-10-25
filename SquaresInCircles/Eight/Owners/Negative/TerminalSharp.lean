module

public import SquaresInCircles.Eight.Owners.Both.NegativeSpan
public import SquaresInCircles.Eight.Owners.Nonpositive.OuterSharp

/-!
# Eight squares: the losses at H and D exclude the negative terminal cells

A negative-primary entry pays a strict loss at the anchor H or D. At a radius `q ≤ qStar` the
nonpositive hard terminal puts every anchor of the descendant on the sharp circle
(`HardInput.nonpositive_outer_all_anchors_on`), which contradicts the strict inequality against
the original contained point (`BothNegativeEntry.false`). In the two-negative cell the second
conversion keeps the loss at H, so both losses are available, and the cell is empty
(`both_negative_impossible`). Neither free intermediate serves as an obstruction to equality.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight
open Candidate Stationary GeometricModel

namespace SignedCycle

theorem HardInput.nonpositive_outer_all_anchors_on {q : ℝ}
    (I : HardInput q) (hqL : qLow≤q) (hqq : q≤qStar)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T) :
    AllAnchorsOn qStar I.cycle := by
  obtain ⟨_,_,_,_,_,_,_,_,hcircle,_⟩ :=
    I.nonpositive_outer_sharp hqL hqq hGH hDT
  exact hcircle

end SignedCycle

namespace AlignedNegative

/-- Each of the two anchor losses of a two-negative entry contradicts the sharp hard terminal at
`q ≤ qStar`; no circle equality is assumed for the point of H after the first move. -/
theorem BothNegativeEntry.false {q : ℝ} {C : SignedCycle} {w : C.Witnesses}
    (J : BothNegativeEntry q C w) (hqL : qLow≤q) (hqq : q≤qStar)
    (hH : (C.point H).Contained q) : False := by
  have hcircle := J.target.nonpositive_outer_all_anchors_on hqL hqq
    J.HG_aligned.symm.le J.TD_aligned.le
  exact circle_loss_impossible (hH.trans hqq) J.H_circle_loss
    (hcircle H (by simp [anchorVertices]))

/-- The cell with negative G and negative T primaries is empty at a radius `q ≤ qStar`: the entry
proves the span and the signs of the intermediates, and the contradiction is charged to the
anchor H. -/
theorem both_negative_impossible {q : ℝ}
    (I : SignedCycle.NormalizedBoundaryInput q)
    (hqL : qLow≤q) (hqq : q≤qStar)
    (hHG : I.cycle.theta G=I.cycle.theta H)
    (htG : I.cycle.theta A<I.cycle.theta H)
    (hGA : I.cycle.Feasible G 1) (hnotGA : ¬I.cycle.Feasible G 0)
    (hTD : I.cycle.theta T=I.cycle.theta D)
    (htT : I.cycle.theta D<I.cycle.theta B)
    (hBT : I.cycle.Feasible B 3) (hnotBT : ¬I.cycle.Feasible B 2) : False := by
  have hcap : q≤qCap := hqq.trans qStar_limits.2.2.le
  obtain ⟨J⟩ := both_negative_hard_entry I hqL hcap
    hHG htG hGA hnotGA hTD htT hBT hnotBT
  exact J.false hqL hqq (I.necessary.contained H)

end AlignedNegative

namespace DirectNegativeT

end DirectNegativeT
end SquaresInCircles.Eight
