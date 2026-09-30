module
public import SquaresInCircles
public import SquaresInCircles.Six.AnalyticReduction

@[expose] public section

/-!
# Deferred n=6 kernel/axiom audit

This imports the actual public theorem root, not just a development checkpoint.
The commands are configuration for later validation, NOT recorded execution.
Compilation and the kernel/axiom audit remain deferred by the user.

The pair/equality chain is analytic. Classification.Reduction still uses the
internal fixed-row classification; its separate entry below makes that boundary
visible. No conclusion about kernel acceptance follows from this source file.
-/

-- Candidate and normalization.
#print axioms SquaresInCircles.Six.attainment
#print axioms SquaresInCircles.Six.qStar_lt_Q0
#print axioms SquaresInCircles.Six.Normalization.strongCentralBox
#print axioms SquaresInCircles.Six.Normalization.normalize_of_candidate

-- The remaining internal classification boundary.
#print axioms SquaresInCircles.Six.Classification.reduction

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
