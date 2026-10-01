import SquaresInCircles.Six.Analytic.SouthOuterTail.Geometry
import SquaresInCircles.Six.Analytic.ReductionInterface

/-!
# Unconditional analytical reduction

The two missing-wing exclusions supply the actual candidate D separators.
SouthOuterTail supplies the last independent tail bound. ReductionInterface
then derives the west outer tail, the south lower tail, and both pair domains.
No Classification.CommonDomain, fixed-row table, or finite-cover theorem is
used to construct this input. All problem predicates remain unchanged.

This completes the source-level analytical reduction. It is not a record of
Lean compilation, elaborated dependency inspection, or kernel acceptance.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.FixedPair
open Normalization

/-- The south tail is a derived geometric fact, not a caller-supplied premise. -/
theorem complete_south_outer_bound {R : ℝ} (P : NormalizedPacking R) : SouthOuterBound P := by
  intro hS
  exact (SouthOuterTail.normalized_own_south_upper_tail P hS).le

/-- All reduction data follow analytically from an arbitrary normalized packing. -/
theorem complete_reduction {R : ℝ} (P : NormalizedPacking R) : ReductionHypotheses P :=
  (reduction_iff_edges_and_south_tail P).mpr
    ⟨candidate_diagonal_separators P,complete_south_outer_bound P⟩

/-- The normalized radius endpoint now needs no classification or tail assumption. -/
theorem radius_of_normalized_packing {R : ℝ} (P : NormalizedPacking R)
    (hR : R^2 ≤ Six.qStar) : R=Six.radius :=
  radius_of_reduction P hR (complete_reduction P)

end SquaresInCircles.Six.Analytic.FixedPair
