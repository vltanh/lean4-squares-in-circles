module
public import SquaresInCircles.Six.Analytic.CompleteReduction

@[expose] public section

/-!
# Compatibility entry point for the completed analytical reduction

The historical Classification namespace is retained for clients. This module
no longer imports CommonDomain, CandidateGraph, fixed stress rows or ExactCover.
Its three declarations are direct adapters to the analytical missing-wing
exclusions and south-tail proof. The unrestricted radius and equality paths
can keep their existing signatures without using the old finite classifier.

Compilation and elaborated dependency/axiom validation remain unexecuted.
-/

noncomputable section
namespace SquaresInCircles.Six.Classification
open Normalization Analytic.FixedPair

/-- Both actual candidate D inequalities follow from analytical exclusions. -/
lemma reduction_edges {R : ℝ} (P : NormalizedPacking R) : CandidateDSeparators P :=
  Analytic.candidate_diagonal_separators P

/-- The upper south tail is the new unconditional analytical theorem. -/
lemma reduction_south_tail {R : ℝ} (P : NormalizedPacking R) : SouthOuterBound P :=
  complete_south_outer_bound P

/-- Compatibility name for the complete analytical reduction. -/
theorem reduction {R : ℝ} (P : NormalizedPacking R) : ReductionHypotheses P :=
  complete_reduction P

end SquaresInCircles.Six.Classification
