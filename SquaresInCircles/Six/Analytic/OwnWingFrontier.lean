import SquaresInCircles.Six.Analytic.CoupledWingBudgetSharp
import SquaresInCircles.Six.Analytic.CardinalSouthTail.Geometry
import SquaresInCircles.Six.Analytic.LowDWestSource.Geometry
import SquaresInCircles.Six.Analytic.MixedCardinalWest.Geometry

/-!
# The angle between W and D in a missing west wing

In a missing west wing W and D are separated along the secondary axis of D, so
the angle of D from the west direction exceeds that of W by more than one
radian.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

/-- In a missing west wing the angle of D exceeds the angle of W by more than
one. -/
lemma MissingWestWing.diagonal_minus_west_gt_one {R : ℝ} {P : NormalizedPacking R}
    (h : MissingWestWing P) : 1 < P.diagonalAngle-P.helperAngle 2 := by
  have hg := DW_Dsecondary_gap_gt_one P h.from_diagonal
  have hc : cardinalCenter (matchingCardinal 2) = Real.pi := rfl
  rw [P.phase_from_deviation 2, hc] at hg
  dsimp [NormalizedPacking.diagonalAngle]
  linarith

end SquaresInCircles.Six.Analytic
