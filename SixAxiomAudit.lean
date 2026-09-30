module
public import SquaresInCircles
public import SquaresInCircles.Six.AnalyticReduction

@[expose] public section

/-!
# Deferred n=6 kernel/axiom audit

This imports the actual public theorem root and the analytical reduction.
The commands below are configuration for validation, NOT recorded execution.
The public source path no longer uses the finite Classification modules.
The compatibility adapter Classification.Reduction is deliberately not imported
here: the public endpoints use CompleteReduction directly.

A successful source review or a list of print commands does not establish
elaboration or kernel acceptance. The final output must be checked for only
propext, Classical.choice and Quot.sound, with no sorryAx or other added axiom.
-/

-- Candidate and normalization.
#print axioms SquaresInCircles.Six.attainment
#print axioms SquaresInCircles.Six.qStar_lt_Q0
#print axioms SquaresInCircles.Six.Normalization.strongCentralBox
#print axioms SquaresInCircles.Six.Normalization.normalize_of_candidate

-- Both actual candidate edges, with no finite classifier premise.
#print axioms SquaresInCircles.Six.Analytic.not_missing_south
#print axioms SquaresInCircles.Six.Analytic.not_missing_west
#print axioms SquaresInCircles.Six.Analytic.candidate_diagonal_separators
#print axioms SquaresInCircles.Six.Analytic.CandidateWestTail.normalized_own_west_tail_of_edges

-- The final tail: two cardinal sign rectangles and the repaired OWN argument.
#print axioms SquaresInCircles.Six.Analytic.SouthOuterTail.positive_cardinal
#print axioms SquaresInCircles.Six.Analytic.SouthOuterTail.narrow_support
#print axioms SquaresInCircles.Six.Analytic.SouthOuterTail.Own.force_cone
#print axioms SquaresInCircles.Six.Analytic.SouthOuterTail.Own.positive_raw
#print axioms SquaresInCircles.Six.Analytic.SouthOuterTail.own_impossible
#print axioms SquaresInCircles.Six.Analytic.SouthOuterTail.cardinal_impossible
#print axioms SquaresInCircles.Six.Analytic.SouthOuterTail.normalized_own_south_upper_tail
#print axioms SquaresInCircles.Six.Analytic.FixedPair.complete_south_outer_bound
#print axioms SquaresInCircles.Six.Analytic.FixedPair.complete_reduction
#print axioms SquaresInCircles.Six.Analytic.FixedPair.radius_of_normalized_packing

-- Analytic pair/diagonal bounds and the actual retained source witnesses.
#print axioms SquaresInCircles.Six.Analytic.FixedPair.lower_bound
#print axioms SquaresInCircles.Six.Analytic.FixedPair.remainder_nonnegative
#print axioms SquaresInCircles.Six.Analytic.FixedPair.remainder_zero
#print axioms SquaresInCircles.Six.Analytic.FixedPair.radius_of_reduction
#print axioms SquaresInCircles.Six.Analytic.FixedPair.northwest_work_of_selected
#print axioms SquaresInCircles.Six.Analytic.FixedPair.eastsouth_work_of_selected
#print axioms SquaresInCircles.Six.Analytic.FixedPair.candidate_data_with_selection

-- Equality without the legacy BalancedClosure or pair checker.
#print axioms SquaresInCircles.Six.Equality.ContactCoordinates.support_tight
#print axioms SquaresInCircles.Six.Equality.ContactCoordinates.coordinates_of_contacts
#print axioms SquaresInCircles.Six.Equality.ContactCoordinates.center_of_contacts
#print axioms SquaresInCircles.Six.Equality.AnalyticContacts.contacts_of_selected
#print axioms SquaresInCircles.Six.Equality.AnalyticContacts.coordinates_of_reduction
#print axioms SquaresInCircles.Six.Equality.AnalyticReconstruction.normalized_congruent_of_reduction
#print axioms SquaresInCircles.Six.Equality.absorb_normalization_reflection

-- Actual advertised endpoints, with their unchanged problem statements.
#print axioms SquaresInCircles.Six.lower_bound
#print axioms SquaresInCircles.Six.uniqueness
#print axioms SquaresInCircles.Six.optimum
#print axioms SquaresInCircles.optimal_radius
#print axioms SquaresInCircles.optimal_packings
