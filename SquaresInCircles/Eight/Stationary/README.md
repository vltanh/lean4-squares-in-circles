# Eight squares: the stationary configuration and the family

The modules of this directory define the optimal configuration of eight unit squares, prove that
it is the only solution of the stationary system, give the stationary identity at arbitrary
centres, and describe the optimal packings as a five-parameter family. Bare file names are those
of this directory; other paths start at the root of the repository.

## The stationary configuration

- `Coordinates.lean`: the chain of the squares `A, B, D, E, H` with five corners on the circle
  (`Coordinates`, `IsChain`), its defect, and the stationary system `IsStationary`; the seven
  contacts of the chain (`HG_contact`, `GA_contact`, `HE_contact`, `standard_contacts`); the five
  parameters of the family (`EqualityParameters`), their domain `Admissible`, the box `InBox` and
  the model `EqualityParameters.model`.
- `Weights.lean`: the five circle weights `mu` and the seven contact weights `lam` of a chain,
  positive on `WeightDomain`, which holds on the stationary system (`IsStationary.weightDomain`),
  and the balance of forces (`force_balance`, `slider_forces_zero`); the vertical balance at `E`
  follows from the position equation (`last_force_residual`).
- `Expression.lean`: formulas in several variables (`Formula`) and their symbolic partial
  derivatives (`Formula.diff`), which are the partial derivatives of their values wherever the
  radicands are positive and the inverted values nonzero (`Formula.hasDerivAt_partial`).
- `FixedEval.lean`: fixed-point interval evaluation of formulas on rational boxes, whose success
  gives bounds and regularity on the whole box (`bounded_sound`, `regular_sound`).
- `Analysis.lean`: for every squared radius in `[qMinus, Q0]` the defect is strongly convex in the
  position and the tilt on the rectangle `poseBox` (`family_strong_convex`); its minimum vanishes
  at exactly one squared radius `qStar`, at the point `sharpPose` (`unique_minimum_zero`,
  `sharpPose_stationary`).
- `Convexity.lean`, `CriticalHessian.lean`, `Envelope.lean`: the stationary system has at most one
  solution (`FiveCornerGeometry.stationary_chain_unique`). The defect is strictly convex in the
  position on the whole radical domain (`strictConvexOn_defect`) and decreases faster than the
  squared radius grows (`defect_radius_decrease`), the determinant of its Hessian is positive at
  every critical point of the strip (`StripCritical.hessian_reserve`), and the minimum over the
  position, as a function of the tilt, has at most one critical point, which is its minimum
  (`positionEnvelope_critical_unique`, `positionEnvelope_critical_global_minimum`).
- `System.lean`: the stationary configuration `sharpData`, the chain of square roots
  (`radicalCoordinates`) at `(qStar, sharpPose)`, which solves the stationary system
  (`sharpData_stationary`) and is its only solution (`stationary_unique`,
  `exact_stationary_existsUnique`), with rational brackets for `qStar` and the coordinates
  (`qStar_bracket`, `qStar_limits`, `sharp_coordinates`, `sharp_y`).

## The stationary identity

- `CenterCompletion.lean`: completing the square at a centre (`center_square_difference`), and the
  stationary identity at arbitrary centres (`OriginalDual.exact_identity`): the weighted corner
  constraints less the weighted gaps along the normals of the model are `q` plus the weighted
  squared distances of the five anchored centres from those of the model. It fixes the five
  squares with a corner on the circle and puts the two sliders on their lines
  (`OriginalDual.original_centers_rigid`, `OriginalDual.slider_coordinates`).

## The family

- `EqualityGeometry.lean`: every admissible model is a packing in the disk of squared radius
  `qStar` (`model_sqPacking`); each pair of exterior squares is separated along the normal
  `exteriorNormal` (`exterior_separator`).
- `EqualityBox.lean`: rational bounds on eighteen quantities of the model on the box `InBox`
  (`box_data_bounds`).
- `Family.lean`: every point of `InBox` is admissible (`box_admissible`); the admissible models
  and their mirror images in the diagonal (`stationaryModels`) are packings in the disk of radius
  `√qStar` that reach the circle (`model_packing`, `model_reaches`); and the admissibility
  conditions are necessary for a packing at that radius whose exterior squares are those of a
  model (`admissible_of_original_geometry`).
- `CentralParameters.lean`: every unit square is the central square of parameters whose frame
  parameter lies in the half-open interval of `Admissible` (`central_parameters_exist`).

`SquaresInCircles/Eight/Equality/` and `SquaresInCircles/Eight/Uniqueness.lean` assemble the
family and the uniqueness theorem from these modules.

## Generated modules

The modules of `Generated/` are written by scripts in `scripts/eight/`, run from the root of the
repository, for example `python3 -I scripts/eight/generate_stationary.py`. Each script checks
every bound with its own interval arithmetic before it writes it, and the kernel decides the bound
again with `decide +kernel`; running a script again reproduces its files byte for byte.

- `generate_stationary.py` writes `Generated/StationaryFormula.lean`, the defect, its derivatives
  and the coordinates of the chain as formulas, with the derivative identities, and
  `Generated/LocalStationaryBounds.lean`, their bounds near the stationary point by the
  fixed-point evaluation of `FixedEval.lean`.
- `generate_equality.py` writes `Generated/EqualityBox.lean`, interval expressions (`ScalarExpr`)
  for the eighteen quantities of `EqualityBox.lean` on the box of parameters.

`generate_equality.py` builds on the formulas and the interval arithmetic of
`generate_stationary.py`.
