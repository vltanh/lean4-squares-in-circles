import SquaresInCircles.Six.Analytic

/-!
# Deferred kernel audit of the analytic replacements

These commands are an audit entry point, not a record of executed checks.
No output is claimed here. The complete n=6 endpoints are deliberately absent
because their non-analytic dependencies have not all been replaced.
-/

#print axioms SquaresInCircles.Six.Analytic.stress_angle_sign
#print axioms SquaresInCircles.Six.Analytic.primary_cap_angle
#print axioms SquaresInCircles.Six.Analytic.trig_lower_of_endpoints
#print axioms SquaresInCircles.Six.Analytic.quartic_positive_of_chord
#print axioms SquaresInCircles.Six.Analytic.vertexMinorant_positive
#print axioms SquaresInCircles.Six.Analytic.diagonal_vertex_expression_positive
#print axioms SquaresInCircles.Six.Analytic.diagonal_constant_bounds
#print axioms SquaresInCircles.Six.Stress.scalarSupport_max_min
#print axioms SquaresInCircles.Six.Stress.diagonal_value_formula
#print axioms SquaresInCircles.Six.Stress.diagonal_cap_remainder_lower
#print axioms SquaresInCircles.Six.Stress.diagonal_vertex_remainder_positive
#print axioms SquaresInCircles.Six.Stress.diagonal_remainder_nonnegative
#print axioms SquaresInCircles.Six.Stress.diagonal_remainder_zero
