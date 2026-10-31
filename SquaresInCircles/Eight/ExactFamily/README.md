# Eight squares: the stationary configuration, the terminal inequality and the family

The modules of this directory define the optimal configuration of eight unit squares, prove the
terminal inequality, a lower bound for the squared radius near that configuration, and describe
the optimal packings as a five-parameter family. Bare file names are those of this directory;
other paths start at the root of the repository.

## The stationary configuration

- `Coordinates.lean`: the chain of the squares `A, B, D, E, H` with five corners on the circle
  (`Coordinates`, `IsChain`), its radical constructor and direct local coordinate bounds
  (`radicalCoordinates`, `radical_coordinate_bounds`), its defect, and the stationary system
  `IsStationary`; the five parameters of the family (`EqualityParameters`), their domain `Admissible`, the box `InBox` and
  the model `EqualityParameters.model`. At the extreme corners of the pose rectangle, circle
  bounds compare the two terms of the position derivative and give opposite signs
  (`Coordinates.lower_corner_position`, `Coordinates.upper_corner_position`). The circle bounds
  at the two extreme positions are shared with the midpoint cut estimates
  (`Coordinates.left_circle_bounds`, `Coordinates.right_circle_bounds`).
- `Weights.lean`: the five circle weights `mu` and the seven contact weights `lam` of a chain,
  positive on `WeightDomain`, and the balance of forces (`force_balance`, `slider_forces_zero`).
  At a position-stationary chain, ED dominates every raw contact weight. The circle-weight mass
  is at least `6/5` times ED, so the normalized contacts are at most `5/6`
  (`WeightDomain.delta_force_balance`, `WeightDomain.contact_weight_bound`), using coordinate
  bounds and the existing `h₂` bracket. `WeightBounds` collects these coordinate assumptions;
  `WeightDomain.contact_bounds` also gives `epsilon ≥ 2/3` and contact proportions used by the
  owner estimates (`ContactBounds`).
- `Expression.lean`: formulas in several variables (`Formula`) and their symbolic partial
  derivatives (`Formula.diff`), which are the partial derivatives of their values wherever the
  radicands are positive and the inverted values nonzero (`Formula.hasDerivAt_partial`).
  Regularity is preserved by symbolic differentiation (`Formula.RegularAt.diff`).
- `StationaryExpressions.lean`: the four radicals, half-angle frame, fifth corner and defect
  as named formulas; their partial derivatives follow from `Formula.diff` with kernel-checked
  identities. `FormulaData.lean` supports caching these expressions as data.
- `FixedEval.lean`: fixed-point interval evaluation of formulas on rational boxes, whose success
  gives numerical bounds on the whole box (`bounded_sound`).
- `Analysis.lean`: for every squared radius in `[qMinus, Q0]` the defect is strongly convex in the
  position and the tilt on the rectangle `poseBox`; its minimum vanishes at exactly one squared
  radius `qStar`, at the point `sharpPose` (`unique_minimum_zero`, `sharpPose_stationary`).
  The trial pose `(-0.92066, 0.0619)` suffices for existence and interiority. Comparing the
  position derivatives bounds the motion of their roots between `2/3` and `13/6` per unit
  of tilt (`root_position_lower`, `root_position_motion`); the height increases along them
  (`root_height_slope`).
- `Convexity.lean`, `CriticalHessian.lean`, `Envelope.lean`: the stationary system has at most one
  solution (`FiveCornerGeometry.stationary_chain_unique`). The defect is strictly convex in the
  position on the whole radical domain, the determinant of its Hessian is positive at every
  critical point of the strip, and the minimum over the position, as a function of the tilt, has
  at most one critical point. The position curvature on the local rectangle is bounded
  directly by the circle curvatures (`local_positionSecond_bounds`, `familyYY_bounds`).
  Endpoint frame projections and a shear by `3/5` also prove the shifted Hessian determinant
  positive throughout the rectangle (`local_hessian_bounds`, `local_halfAngle_hessian_pos`),
  without a grid. The half-angle chain rule identifies these geometric derivatives with
  the symbolic ones (`familyYZ_geometric`, `familyZZ_geometric`).
  Differentiating the circle equations in the squared radius also gives
  `-4 ≤ F_q ≤ -3` (`radical_radius_derivatives`, `local_radiusSlope_bounds`, `family_q_bound`).
- `Stationary.lean`: the stationary configuration `sharpData`, which solves the stationary system
  (`sharpData_stationary`) and is its only solution (`stationary_unique`,
  `exact_stationary_existsUnique`), with rational brackets for `qStar` and the coordinates
  (`qStar_bracket`, `qStar_limits`, `sharp_coordinates`, `sharp_y`). The shared coarse pose
  bounds `sharpPose_bounds` also locate the adaptive endpoint roots by root motion. Its refined trial pose
  is used for these numerical bounds. The coordinate estimates follow by squaring short
  decimal endpoints in the circle equations and bounding products in the half-angle frame,
  with no separate coordinate certificates.

## The terminal inequality

- `Cuts.lean`: the owner reserves `ownerReserve` and their geometric estimates. Force balance
  removes the quotient in `cutJ` from its neighbouring cuts (`Coordinates.cutJ_force_balance`,
  `Coordinates.cut_expansions`); coarse contact proportions then bound five reserves below by
  `1/80` (`Coordinates.geometric_owner_bounds`). Circle derivatives bound the HE margin's
  position slope below by `0.91` and tilt slope below by `-0.6`, so it increases along the
  position roots (`root_margin_slope`). The last two reserves share an unnormalized cut that
  decreases with position. Its tilt curvature has absolute value at most `32`, and two midpoint
  tangent parabolas bound it on the entire pose rectangle
  (`familyRawCut_bounds_of_midpoint`, `Coordinates.cut_owner_bounds`). Circle equations at the
  middle tilt supply both cut values and slopes (`Coordinates.left_midpoint_cut`,
  `Coordinates.right_midpoint_cut`), with no generated certificates. The endpoint heights
  follow from the circle equations (`Coordinates.lower_tilt_height`,
  `Coordinates.upper_tilt_height`), and the reserve margin is at least `1/40` on the entire
  lower-tilt face (`familyMargin_lower_tilt`).
- `Adaptive.lean`: at every tilt of `tiltBox` the adaptive chain `adaptiveData`, at the squared
  radius `qStar` and at the position where the position derivative of the defect vanishes; its
  defect is at least `(z - z*)²/8` (`adaptive_curvature`). Circle-coordinate comparisons at
  the two extreme corners and decrease in tilt enclose this zero
  (`extreme_corner_signs`, `adaptive_endpoint_signs`, `adaptive_position_exists`). Comparing
  with the known stationary root bounds the endpoint positions
  (`adaptive_position_from_sharp`), without generated root brackets.
  The height gains at least `1.8` from tilt and loses at most `0.7 * 13/6` from position motion,
  so it increases along the family (`adaptive_height_monotone`). The HE reserve margin also
  increases: its position gain `0.91 * 2/3` exceeds its tilt loss `0.6`
  (`adaptive_margin_monotone`).
- `AdaptiveBounds.lean`: along the adaptive chain all nine owner reserves are positive, the
  contact weights are at most `4209/5000` and `h₂` lies in `[-29/20, -7/5]`
  (`adaptive_owner_bounds`, `adaptive_edge_weight_bound`, `adaptive_hTwo_bound`). Force balance
  gives the stronger contact bound `5/6`. Monotonicity extends the geometric endpoint height
  bounds and lower-face margin bound to the entire family. Midpoint circle estimates give
  `0.412 ≤ N₀ ≤ 0.44` throughout the pose rectangle (`raw_cut_bound`); normalization then bounds
  the last two reserves by `3/250`. The other seven reserves are at least `1/80`.
- `CenterCompletion.lean`: completing the square at the centres (`complete_center_square`), the
  constants of the terminal inequality (`terminal_constants`), and the stationary identity at
  arbitrary centres, which fixes the five squares with a corner on the circle and the lines of the
  two sliders (`OriginalDual.original_centers_rigid`, `OriginalDual.slider_coordinates`).
- `PerturbationModel.lean`: the terminal dual at arbitrary centres, frame errors and owners; it is
  at most the squared radius when the anchored corners lie in the disk and the gaps are
  nonnegative (`dual_le`), and it is a sum of completed squares and a reduced part
  (`exact_completion`).
- `PerturbationEstimates.lean`: lower bounds for the reduced part: its value at zero frame errors
  plus first-order terms, less quadratic and cubic remainders.
- `PerturbationBounds.lean`: bounds on the remainder coefficients from the coordinate and
  contact-weight bounds, using the endpoints of the tilt interval
  (`remainder_bounds_of_coordinates`, `adaptive_remainder_bounds`).
- `Perturbation.lean`: the quantitative terminal inequality (`Perturbation.quantitative`), which
  `SquaresInCircles/Eight/Rigidity/Terminal.lean` applies to a boundary cycle with the estimates of
  `SquaresInCircles/Eight/Rigidity/Estimates.lean`.

## The family

- `EqualityGeometry.lean`: every admissible model is a packing in the disk of squared radius
  `qStar` (`model_sqPacking`). The exterior support bounds follow from the stationary
  coordinate bounds by signs and elementary products, with no additional interval certificates.
- `EqualityBox.lean`: the whole box `InBox` is admissible (`admissible_of_inBox`), by
  half-angle formulas, Cauchy–Schwarz, separating projections and squared coordinate bounds.
  It uses the stationary coordinate bounds directly, with no further interval certificates.
- `CentralParameters.lean`: every unit square is the central square of parameters whose frame
  parameter lies in the half-open interval of `Admissible` (`central_parameters_exist`).
- `BoxRigidity.lean`: distinct points of `InBox` give non-congruent models
  (`BoxRigidity.box_rigid_parameters`, `BoxRigidity.box_rigidlyCongruent_iff`).
- The public geometric statement is connected to this chart by
  `SquaresInCircles/Eight/Corners/GeometricStationaryExistence.lean`,
  `SquaresInCircles/Eight/Equality/Angles.lean`,
  `SquaresInCircles/Eight/Equality/Equivalence.lean` and
  `SquaresInCircles/Eight/Construction.lean`: the five-corner minimum has the
  stationary radius, and the geometric and stationary admissible families agree.

`SquaresInCircles/Eight/ExactFamily/Models.lean` assembles the stationary family;
`SquaresInCircles/Eight/Rigidity/Classification.lean` classifies packings in the stationary chart.
`SquaresInCircles/Eight/Construction.lean` proves the packing and circle-contact facts
for the public family, and `SquaresInCircles/Eight/Uniqueness.lean` proves its
classification and assembles the single `Eight.optimum`, as in the other cases.

## Generated modules

The modules of `Generated/` are written by scripts in `scripts/eight/`, run from the root of the
repository, for example `python3 -I scripts/eight/generate_stationary.py`. Each script evaluates
every bound with exact arithmetic before it writes it, and the kernel decides the bound again with
`decide +kernel`; running a script again reproduces its files byte for byte.

- `generate_stationary.py` writes `Generated/StationaryFormula.lean`, with aliases for the named
  expressions, the local box and the numerical bracket, and `Generated/LocalStationaryBounds.lean`,
  with fixed-point trial and refined-bracket bounds. Positivity of the radicands
  and closure of regularity under differentiation are proved directly in `Analysis.lean`.
  The short trial pose is used for the
  existence bounds; the refined pose is used for the numerical radius and coordinate bounds.
The adaptive-chain estimates are proved directly in `Coordinates.lean`, `Cuts.lean` and
`AdaptiveBounds.lean`; their former generator and generated formula/checker files are retired.
