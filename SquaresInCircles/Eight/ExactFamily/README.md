# Eight squares: the stationary configuration, the terminal inequality and the family

The modules of this directory define the optimal configuration of eight unit squares, prove the
terminal inequality, a lower bound for the squared radius near that configuration, and describe
the optimal packings as a five-parameter family. Bare file names are those of this directory;
other paths start at the root of the repository.

## The stationary configuration

- `Coordinates.lean`: the chain of the squares `A, B, D, E, H` with five corners on the circle
  (`Coordinates`, `IsChain`), its defect, and the stationary system `IsStationary`; the five
  parameters of the family (`EqualityParameters`), their domain `Admissible`, the box `InBox` and
  the model `EqualityParameters.model`.
- `Weights.lean`: the five circle weights `mu` and the seven contact weights `lam` of a chain,
  positive on `WeightDomain`, and the balance of forces (`force_balance`, `slider_forces_zero`).
- `Expression.lean`: formulas in several variables (`Formula`) and their symbolic partial
  derivatives (`Formula.diff`), which are the partial derivatives of their values wherever the
  radicands are positive and the inverted values nonzero (`Formula.hasDerivAt_partial`).
- `FixedEval.lean`: fixed-point interval evaluation of formulas on rational boxes, whose success
  gives bounds and regularity on the whole box (`bounded_sound`, `regular_sound`).
- `Analysis.lean`: for every squared radius in `[qMinus, Q0]` the defect is strongly convex in the
  position and the tilt on the rectangle `poseBox`; its minimum vanishes at exactly one squared
  radius `qStar`, at the point `sharpPose` (`unique_minimum_zero`, `sharpPose_stationary`).
- `Convexity.lean`, `CriticalHessian.lean`, `Envelope.lean`: the stationary system has at most one
  solution (`FiveCornerGeometry.stationary_chain_unique`). The defect is strictly convex in the
  position on the whole radical domain, the determinant of its Hessian is positive at every
  critical point of the strip, and the minimum over the position, as a function of the tilt, has
  at most one critical point.
- `Stationary.lean`: the stationary configuration `sharpData`, which solves the stationary system
  (`sharpData_stationary`) and is its only solution (`stationary_unique`,
  `exact_stationary_existsUnique`), with rational brackets for `qStar` and the coordinates
  (`qStar_bracket`, `qStar_limits`, `sharp_coordinates`, `sharp_y`).

## The terminal inequality

- `Adaptive.lean`: at every tilt of `tiltBox` the adaptive chain `adaptiveData`, at the squared
  radius `qStar` and at the position where the position derivative of the defect vanishes; its
  defect is at least `(z - z*)²/8` (`adaptive_curvature`). The module also defines the owner
  reserves `ownerReserve`.
- `AdaptiveBounds.lean`: along the adaptive chain the owner reserves are positive, the contact
  weights are at most `4209/5000` and `h₂` lies in `[-29/20, -7/5]` (`adaptive_owner_bounds`,
  `adaptive_edge_weight_bound`, `adaptive_hTwo_bound`).
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
- `PerturbationBounds.lean`: bounds on the remainder coefficients along the adaptive chain
  (`adaptive_remainder_bounds`).
- `Perturbation.lean`: the quantitative terminal inequality (`Perturbation.quantitative`), which
  `SquaresInCircles/Eight/Terminal.lean` applies to a boundary cycle with the estimates of
  `SquaresInCircles/Eight/TerminalEstimates.lean`.

## The family

- `EqualityGeometry.lean`: every admissible model is a packing in the disk of squared radius
  `qStar` (`model_sqPacking`).
- `EqualityBox.lean`: rational bounds on eighteen quantities of the model on the box `InBox`
  (`box_data_bounds`).
- `CentralParameters.lean`: every unit square is the central square of parameters whose frame
  parameter lies in the half-open interval of `Admissible` (`central_parameters_exist`).
- `BoxRigidity.lean`: distinct points of `InBox` give non-congruent models
  (`BoxRigidity.box_rigid_parameters`, `BoxRigidity.box_rigidlyCongruent_iff`).
- `StatementLink.lean`: the radius and the models of the statement in
  `SquaresInCircles/Geometry.lean` (namespace `EightStatement`) are those of the proof
  (`radius_statement`, `models_statement`).

`SquaresInCircles/Eight/Equality.lean` and `SquaresInCircles/Eight/Uniqueness.lean` assemble the
family and the uniqueness theorem from these modules.

## Generated modules

The modules of `Generated/` are written by scripts in `scripts/eight/`, run from the root of the
repository, for example `python3 -I scripts/eight/generate_stationary.py`. Each script evaluates
every bound with exact arithmetic before it writes it, and the kernel decides the bound again with
`decide +kernel`; running a script again reproduces its files byte for byte.

- `generate_stationary.py` writes `Generated/StationaryFormula.lean`, the defect, its derivatives
  and the coordinates of the chain as formulas, with the derivative identities, and
  `Generated/LocalStationaryBounds.lean`, their bounds near the stationary point by the
  fixed-point evaluation of `FixedEval.lean`.
- `generate_adaptive.py` writes `Generated/AdaptiveFormula.lean`, the contact weights, the owner
  reserves, `h₂` and the remainder coefficients as formulas, with the 256 graph boxes of the
  adaptive chain, and `Generated/AdaptiveBounds.lean`, the signs of the position derivative on the
  faces of the graph boxes and the bounds on their hulls, again by `FixedEval.lean`.
- `generate_equality.py` writes `Generated/EqualityBox.lean`, interval expressions (`ScalarExpr`)
  for the eighteen quantities of `EqualityBox.lean` on the box of parameters.

`generate_adaptive.py` and `generate_equality.py` build on the formulas and the interval
arithmetic of `generate_stationary.py`.
