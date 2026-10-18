# Exact family, sharp terminal, and equality source

This directory is an **uncompiled Lean source draft**. No Lean build, Lean
elaboration, CI run, or audit was performed when preparing this handoff.
The theorem bodies and rational certificate proofs are supplied for the
subsequent compilation and audit pass.

## Exact stationary selection (F2)

`Coordinates.lean` defines the nested-radical chain through four circle
vertices, the fifth contact vertex, the two stationarity equations, and the
five equality parameters. `Weights.lean` derives the seven contact weights
and five positive circle weights from those coordinates. Its last vertical
force balance follows from position stationarity.

`Expression.lean` connects the rational interval expression language to a
differentiable real expression language. It retains nonzero denominator and
positive radicand obligations. `RootCover.lean` provides simultaneous-zero
exclusion and complete weak closed splitting. The generated stationary
cover includes both sides of every cut and retains boundary ties.

`Analysis.lean` proves existence of an interior minimizer for every radius
in the local rectangle, uniform strict convexity in the two pose variables,
strict monotonicity and continuity of the minimized value as the radius
varies, and existence and uniqueness of its zero. The selected `qStar` is
obtained from that existence theorem. `Stationary.lean` identifies its
actual nested-radical coordinates, localizes every solution of the broad
stationary system by the generated closed cover, and proves uniqueness.
No external stationary witness is an assumption of these results.

The principal exports are:

- `qStar`, `sharpData`, and `sharpData_stationary`;
- `qStar_bracket` and `qStar_limits`;
- `stationary_unique` and `exact_stationary_existsUnique`;
- `sharp_coordinates` and `sharp_y`.

Hand sources: `EXACT_CONFIGURATION_AND_FREEDOM.md`,
`ANALYTIC_EXACT_CONSTRUCTION.md`, `HUMAN_FIVE_CORNER.md`, and
`UNRESTRICTED_EIGHT_SQUARE_HAND_PROOF.md`, Section 1. The closed stationary
cover and the sharp bracket arithmetic also follow the expressions in
`verify_hand_sharp_ceiling_bracket.py`.

## Adaptive and terminal comparison (F9)

`Adaptive.lean` proves existence and uniqueness of the position-stationary
value at each tilt in the terminal interval. `AdaptiveBounds.lean` supplies
the original-owner first-order reserves from exact rational expression
certificates. `PerturbationBounds.lean` supplies bounds on the quadratic and
cubic remainder coefficients.

`PerturbationModel.lean` defines the seven actual signed gaps, original
centers, center forces, and completed center squares.
`PerturbationEstimates.lean` proves the trigonometric remainder estimates
and the enlarged slider coefficient bounds. `Perturbation.lean` assembles
the positive-error comparison. It uses the positive curvature already
proved for the reduced function in the half-angle variable; the exact
coefficient need only be positive to force the unique equality tilt.

`CenterCompletion.lean` contains the separate stationary identity on
arbitrary original centers. Its slider forces are exactly zero. In
particular, its `OriginalDual.original_centers_rigid` theorem assumes no
distance from the displaced centers and no original slider rectangle.

`../Terminal.lean` contains the physical boundary adapters and exports
`Terminal.boundary_quantitative`, `Terminal.boundary_rigid`, and
`Terminal.original_pullback`.

Hand sources: `HUMAN_ADAPTIVE_DUAL_SEVEN_SQUARE_SHARPNESS.md`,
`HAND_EXACT_CENTER_SQUARE_COMPLETION.md`,
`HAND_TERMINAL_WITH_AUTOMATIC_SLIDERS.md`,
`HUMAN_BROAD_TERMINAL_ARITHMETIC.md`, and
`EQUALITY_PULLBACK_TO_ORIGINAL_SQUARES.md`.

## Full equality domain and noncongruence (F11)

`EqualityGeometry.lean` proves sufficiency for the entire weak parameter
domain, including all exterior pairs and all seven central SAT conditions.
`EqualityBox.lean` interprets the exact interval certificates for the full
displayed five-parameter box. `../Equality.lean` proves necessity from the
actual original geometry and exports the family, its attaining packing,
and circle contact witnesses.

`CentralParameters.lean` chooses a physical quarter-turn representative for
the central square and recovers its half-angle parameter in the specified
half-open interval. `BoxRigidity.lean` proves distinct box parameters are
noncongruent under every distance-preserving plane equivalence, with any
square permutation. Its argument recovers the unique containing center
from the stationary contact-vertex barycenter, fixes the independent A and
E centers using disjoint rational center-radius bands, and recovers the
remaining parameters from the slider centers and central support widths.

Hand source: `COMPLETE_EQUALITY_PARAMETER_DOMAIN.md`, together with
`UNRESTRICTED_EIGHT_SQUARE_HAND_PROOF.md`, Sections 11–12.

## Unrestricted public assembly (F10/F12)

`../Theorem.lean` consumes the geometric `GlobalNormalization` record.
Candidate capture is applied to the Q1 expansion and pulled back to the
recovered cycle at `max q qMinus`. Boundary rigidity fixes the radius,
tilt, and five frame errors. The original stationary identity then fixes
the untouched original anchors and identifies the two slider lines.
Only after these anchors are fixed is original cyclic order used to
identify the two slider sectors. The central parameter representative and
the full admissible domain produce the reflected or unreflected model.

Public exports include `Eight.optimum`, `Eight.lower_bound`,
`Eight.packing_iff`, `Eight.equality_iff_parameters`, `Eight.isLeast`, and
`Eight.full_dimensional_equality_box`.

## Generated data

The generators write Lean expressions and rational arithmetic proof
objects. The theorem statements interpret those expressions over the
reals. A successful Python run is not used as a Lean premise.

- `generate_stationary.py`: stationary closed cover, derivatives, Hessian
  bounds, root brackets, and coordinate brackets;
- `generate_adaptive.py`: adaptive position brackets, all nine owner
  reserves, edge weight bounds, and perturbation remainder bounds;
- `generate_equality.py`: the explicit equality box and its strict
  containment, core, and central separation reserves.

The large generated files are split into source modules so their full
rational arithmetic data remain available to the later Lean pass.
