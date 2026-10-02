module

import SquaresInCircles

/-!
Dependency audit. Every line below must report exactly
`[propext, Classical.choice, Quot.sound]`, the three standard axioms: an
unproved lemma would add `sorryAx`, and a proof by `native_decide`, which
trusts the compiler, would add `Lean.ofReduceBool`.
-/

-- All seven cases in one statement, which depends on every case.
#print axioms SquaresInCircles.optimal_radius
#print axioms SquaresInCircles.optimal_packings
#print axioms SquaresInCircles.optimal_packings_rigid

-- The shared tools: separation of disjoint squares, arcs and their budget, the
-- radial sweep, directions on the circle, contacts, and the optimum.
#print axioms SquaresInCircles.support_separator
#print axioms SquaresInCircles.SAT.separating_axes
#print axioms SquaresInCircles.oriented_separating_axes
#print axioms SquaresInCircles.open_arc_budget
#print axioms SquaresInCircles.OpenArc.third_distance_bounds
#print axioms SquaresInCircles.safe_openRay_of_disjoint
#print axioms SquaresInCircles.ray_budget_impossible
#print axioms SquaresInCircles.directions_budget
#print axioms SquaresInCircles.regular_polygon
#print axioms SquaresInCircles.centers_distance_sq_ge_one
#print axioms SquaresInCircles.unit_contact
#print axioms SquaresInCircles.axis_packing
#print axioms SquaresInCircles.Congruent.packing
#print axioms SquaresInCircles.Optimum.optimality
#print axioms SquaresInCircles.Optimum.isLeast
#print axioms SquaresInCircles.Optimum.packing_iff

-- Each case: its construction, what an exterior square holds, what becomes of
-- the square that contains the disk centre, the steps between, and uniqueness.
#print axioms SquaresInCircles.One.model_packing
#print axioms SquaresInCircles.One.uniqueness

#print axioms SquaresInCircles.Two.model_packing
#print axioms SquaresInCircles.Two.centers_at_half
#print axioms SquaresInCircles.Two.uniqueness

#print axioms SquaresInCircles.Three.model_packing
#print axioms SquaresInCircles.Three.exterior_cap
#print axioms SquaresInCircles.Three.no_containing
#print axioms SquaresInCircles.Three.uniqueness

#print axioms SquaresInCircles.Four.model_packing
#print axioms SquaresInCircles.Four.exterior_arc
#print axioms SquaresInCircles.Four.quarter_arc
#print axioms SquaresInCircles.Four.uniqueness

-- For five squares the closed 12-gon alone is rigid, without the disk.
#print axioms SquaresInCircles.Five.model_packing
#print axioms SquaresInCircles.Five.exterior_arc
#print axioms SquaresInCircles.Five.containing_arc
#print axioms SquaresInCircles.Five.centered_square
#print axioms SquaresInCircles.Five.polygon_uniqueness
#print axioms SquaresInCircles.Five.uniqueness

-- Six squares: the central square and the box of its centre, the
-- normalization, the separators of the turned square, the stress bound at the
-- optimal radius, and the eight contacts.
#print axioms SquaresInCircles.Six.model_packing
#print axioms SquaresInCircles.Six.exterior_arc
#print axioms SquaresInCircles.Six.exists_containing
#print axioms SquaresInCircles.Six.Normalization.central_box
#print axioms SquaresInCircles.Six.Normalization.normalize
#print axioms SquaresInCircles.Six.wing_separators
#print axioms SquaresInCircles.Six.Stress.stress_bound
#print axioms SquaresInCircles.Six.Equality.model_of_contacts
#print axioms SquaresInCircles.Six.uniqueness

-- Seven squares: the marker arc, the critical gap pi/3 (nonnegative, zero only
-- at contacts), all smaller gaps, the pair theorem, the containing square in
-- the middle column, the ring, and the classification.
#print axioms SquaresInCircles.Seven.column_packing
#print axioms SquaresInCircles.Seven.marker_arc
#print axioms SquaresInCircles.Seven.fixed_gap_nonneg
#print axioms SquaresInCircles.Seven.fixed_gap_zero
#print axioms SquaresInCircles.Seven.all_gap_pos_below
#print axioms SquaresInCircles.Seven.marker_separation_closed
#print axioms SquaresInCircles.Seven.ordered_chart_contact
#print axioms SquaresInCircles.Seven.exists_containing
#print axioms SquaresInCircles.Seven.central_square_represents
#print axioms SquaresInCircles.Seven.six_exterior_ring
#print axioms SquaresInCircles.Seven.uniqueness
#print axioms SquaresInCircles.Seven.classification_by_slots

-- The statements being proved, for inspection.
#print SquaresInCircles.Packing
#print SquaresInCircles.Congruent
#print SquaresInCircles.axisSquare
#print SquaresInCircles.optimalRadius
#print SquaresInCircles.optimalPackings
#print SquaresInCircles.Optimum
#check @SquaresInCircles.optimal_radius
#check @SquaresInCircles.optimal_packings
#check @SquaresInCircles.optimal_packings_rigid
#check @SquaresInCircles.Five.polygon_uniqueness
#check @SquaresInCircles.Seven.column_packing
#print SquaresInCircles.Six.model
#print SquaresInCircles.Six.diagonalSquare
#print SquaresInCircles.Seven.Column
#print SquaresInCircles.Seven.columnCenters
#print SquaresInCircles.Seven.columnModel
