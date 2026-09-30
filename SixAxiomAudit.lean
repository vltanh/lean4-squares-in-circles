import SquaresInCircles.Six
import SquaresInCircles.Six.AnalyticReduction

/-!
# Deferred n=6 kernel/axiom audit

This is the single audit entry point for the n=6 development. These commands are
configuration for a later compiler/kernel audit; they are NOT recorded output.
Compilation remains deferred.

The final unrestricted endpoints still require the open missing-wing and
OWN-tail reductions described in research/six/lean/STATUS.md. Printing an
endpoint here does not certify that its current dependency path satisfies the
human-analytic acceptance standard.
-/

-- Candidate and construction
#print axioms SquaresInCircles.Six.attainment
#print axioms SquaresInCircles.Six.qStar_lt_Q0

-- Analytic normalization
#print axioms SquaresInCircles.Six.Normalization.strongCentralBox
#print axioms SquaresInCircles.Six.Analytic.five_pin_cover
#print axioms SquaresInCircles.Six.Analytic.labelled_window
#print axioms SquaresInCircles.Six.Normalization.pinPacking_of_ceiling
#print axioms SquaresInCircles.Six.Normalization.PinPacking.west_before_diagonal
#print axioms SquaresInCircles.Six.Normalization.PinPacking.moving_pins
#print axioms SquaresInCircles.Six.Normalization.PinPacking.D_own
#print axioms SquaresInCircles.Six.Normalization.normalize_of_candidate
#print axioms SquaresInCircles.Six.Normalization.NormalizedPacking.east_cardinal_angle_203
#print axioms SquaresInCircles.Six.Normalization.NormalizedPacking.north_cardinal_angle_203

-- Analytic pair/diagonal closure
#print axioms SquaresInCircles.Six.Analytic.FixedPair.lower_bound
#print axioms SquaresInCircles.Six.Analytic.FixedPair.remainder_nonnegative
#print axioms SquaresInCircles.Six.Analytic.FixedPair.remainder_zero
#print axioms SquaresInCircles.Six.Analytic.FixedPair.radius_of_reduction

-- Analytic D-edge reduction frontier
#print axioms SquaresInCircles.Six.Analytic.normalized_diagonal_gt_half
#print axioms SquaresInCircles.Six.Analytic.DW_Dsecondary_gap_gt_quarter
#print axioms SquaresInCircles.Six.Analytic.DS_Dsecondary_gap_gt_quarter
#print axioms SquaresInCircles.Six.Analytic.candidate_or_missing_wing
#print axioms SquaresInCircles.Six.Analytic.candidate_edges_iff_no_missing_wing
#print axioms SquaresInCircles.Six.Analytic.FixedPair.reduction_iff_remaining_obligations
#print axioms SquaresInCircles.Six.Analytic.FixedPair.radius_of_edges_and_own_tails

-- Public endpoints; meaningful only after the analytic dependency path is closed.
#print axioms SquaresInCircles.Six.lower_bound
#print axioms SquaresInCircles.Six.uniqueness
