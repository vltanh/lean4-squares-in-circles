module
public import SquaresInCircles.Six.Classification.CommonDomain
public import SquaresInCircles.Six.Analytic.ReductionInterface

@[expose] public section

/-!
# The current unconditional reduction, with its remaining internal checks visible

The public proof can use the analytic pair bound and analytic reconstruction
without importing the legacy pair-envelope checker. This module supplies their
explicit input from the existing self-contained Lean classification.

IMPORTANT: CandidateGraph and CommonDomain still use the fixed-row/ExactCover
route. This is not a claim that the three outstanding analytic reductions have
been completed. It is the one integration boundary to replace when they are.
No external program result, file, success flag or new axiom is a premise.
-/

noncomputable section
namespace SquaresInCircles.Six.Classification
open Normalization Analytic.FixedPair

/-- Actual candidate D-edge inequalities, retaining the existing internal
classification rather than disguising it as an analytic case exclusion. -/
lemma reduction_edges {R : ℝ} (P : NormalizedPacking R) : CandidateDSeparators P := by
  have h := candidate_diagonal_edges P
  constructor
  · simpa only [DWSelected,Stress.pairNormal] using h.1
  · simpa only [DSSelected,Stress.pairNormal] using h.2.1

/-- The south upper tail currently comes from the internal Lean tail proof.
The west outer tail and south lower tail are supplied by ReductionInterface. -/
lemma reduction_south_tail {R : ℝ} (P : NormalizedPacking R) : SouthOuterBound P := by
  intro _
  exact (common_west_south_rectangle P).2.2

/-- An unconditional inhabitant of precisely the input consumed by the new
analytic radius and equality chain. The remaining table dependency is here. -/
theorem reduction {R : ℝ} (P : NormalizedPacking R) : ReductionHypotheses P :=
  (reduction_iff_edges_and_south_tail P).mpr ⟨reduction_edges P,reduction_south_tail P⟩

end SquaresInCircles.Six.Classification
