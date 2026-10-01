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

-- The contact-polygon argument of five squares, which uses no disk.
#print axioms SquaresInCircles.Five.polygon_uniqueness

-- The shared framework.
#print axioms SquaresInCircles.support_separator
#print axioms SquaresInCircles.safe_openRay_of_disjoint
#print axioms SquaresInCircles.open_arc_budget
#print axioms SquaresInCircles.ray_budget_impossible
#print axioms SquaresInCircles.Optimum.optimality
#print axioms SquaresInCircles.Optimum.isLeast
#print axioms SquaresInCircles.OpenArc.third_distance_bounds
#print axioms SquaresInCircles.centers_distance_sq_ge_one
#print axioms SquaresInCircles.unit_contact
#print axioms SquaresInCircles.regular_polygon
#print axioms SquaresInCircles.axis_packing
#print axioms SquaresInCircles.Congruent.packing
#print axioms SquaresInCircles.Optimum.packing_iff

-- Three squares: the containing square.
#print axioms SquaresInCircles.Three.no_containing
#print axioms SquaresInCircles.Three.compensation
#print axioms SquaresInCircles.Three.axial_pair_impossible

-- Six squares: the model, the central square and the normalization, the
-- analytical reduction, the radius bound, and uniqueness.
#print axioms SquaresInCircles.Six.model_packing
#print axioms SquaresInCircles.Six.exists_containing
#print axioms SquaresInCircles.Six.Normalization.strict_marker_separation
#print axioms SquaresInCircles.Six.Normalization.normalize_of_candidate
#print axioms SquaresInCircles.Six.Analytic.FixedPair.complete_reduction
#print axioms SquaresInCircles.Six.uniqueness

-- Seven squares: the marker arc, the gap of pi/3 (nonnegative, zero only at
-- contacts), all smaller gaps, the pair theorem, the regular hexagon of
-- markers, and the column packings.
#print axioms SquaresInCircles.Seven.marker_arc
#print axioms SquaresInCircles.Seven.fixed_gap_nonneg
#print axioms SquaresInCircles.Seven.fixed_gap_zero
#print axioms SquaresInCircles.Seven.all_gap_pos_below
#print axioms SquaresInCircles.Seven.SAT.separating_axes
#print axioms SquaresInCircles.Seven.marker_separation_closed
#print axioms SquaresInCircles.Seven.ordered_chart_contact
#print axioms SquaresInCircles.Seven.six_directions_hexagon
#print axioms SquaresInCircles.Seven.column_packing

-- Seven squares at the optimal radius: a square contains the centre, the ring,
-- the square in the middle, and the classification.
#print axioms SquaresInCircles.Seven.exists_containing
#print axioms SquaresInCircles.Seven.six_exterior_ring
#print axioms SquaresInCircles.Seven.central_square_represents
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
