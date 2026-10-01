import SquaresInCircles.Six.Analytic.SouthOuterTail.Geometry
import SquaresInCircles.Six.Analytic.ReductionInterface

/-!
# Every normalized packing satisfies the reduction hypotheses

W and D are separated along the secondary axis of W, and D and S along the
secondary axis of S, as in the model, because neither wing is missing. If S is
separated from C along its own axis, its angle from the south direction is at
most `11/25` (`SouthOuterTail`). From these two facts `ReductionInterface`
derives the other reduction hypotheses: the angles of N, W and of E, S lie in
the domains of the pair estimate, and the angle of D is at least `1/2`.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.FixedPair
open Normalization

/-- If S is separated from C along its own axis, its angle from the south
direction is at most `11/25`. -/
theorem complete_south_outer_bound {R : ℝ} (P : NormalizedPacking R) : SouthOuterBound P := by
  intro hS
  exact (SouthOuterTail.normalized_own_south_upper_tail P hS).le

/-- Every normalized packing satisfies the reduction hypotheses. -/
theorem complete_reduction {R : ℝ} (P : NormalizedPacking R) : ReductionHypotheses P :=
  (reduction_iff_edges_and_south_tail P).mpr
    ⟨candidate_diagonal_separators P,complete_south_outer_bound P⟩

end SquaresInCircles.Six.Analytic.FixedPair
