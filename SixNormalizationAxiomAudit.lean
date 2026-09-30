import SquaresInCircles.Six.AnalyticNormalization

/-!
# Deferred normalization kernel audit

These commands are an audit entry point, NOT recorded execution output.
Compilation remains deferred. The source-level import review and explicit
endpoint arithmetic do not establish that these commands have run or that
Lean has accepted their proof terms.

This file deliberately does not import the unfinished analytic conversion of
D-edge classification, pair envelopes, or the unrestricted n=6 endpoints.
-/

#print axioms SquaresInCircles.Six.normalize_frame_of_ceiling
#print axioms SquaresInCircles.Six.Normalization.strict_marker_separation
#print axioms SquaresInCircles.Six.Normalization.no_empty_long_arc
#print axioms SquaresInCircles.Six.Normalization.strongCentralBox
#print axioms SquaresInCircles.Six.Analytic.sixty_pin_cover
#print axioms SquaresInCircles.Six.Analytic.own_east_fixed_pin
#print axioms SquaresInCircles.Six.Analytic.own_west_fixed_pins
#print axioms SquaresInCircles.Six.Analytic.five_pin_cover
#print axioms SquaresInCircles.Six.Analytic.labelled_window
#print axioms SquaresInCircles.Six.Analytic.allowed_axis_of_pin
#print axioms SquaresInCircles.Six.Normalization.pinPacking_of_ceiling
#print axioms SquaresInCircles.Six.Normalization.PinPacking.west_before_diagonal
#print axioms SquaresInCircles.Six.Normalization.PinPacking.moving_pins
#print axioms SquaresInCircles.Six.Normalization.PinPacking.one_helper_per_side
#print axioms SquaresInCircles.Six.Analytic.westStressW_positive
#print axioms SquaresInCircles.Six.Analytic.westStressD_positive
#print axioms SquaresInCircles.Six.Analytic.west_cardinal_impossible
#print axioms SquaresInCircles.Six.Normalization.PinPacking.D_own
#print axioms SquaresInCircles.Six.Normalization.normalize_of_ceiling
#print axioms SquaresInCircles.Six.Normalization.normalize_of_candidate
#print axioms SquaresInCircles.Six.Normalization.NormalizedPacking.east_cardinal_angle_203
#print axioms SquaresInCircles.Six.Normalization.NormalizedPacking.north_cardinal_angle_203
#print axioms SquaresInCircles.Six.Stress.PinPacking.sharp_central_box
#print axioms SquaresInCircles.Six.Stress.PinPacking.east_west_budget_candidate
#print axioms SquaresInCircles.Six.Stress.PinPacking.north_south_budget_candidate
