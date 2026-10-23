# Exact family, sharp terminal, and equality source

This directory is an **uncompiled Lean source draft**. The geometric
replacement pass includes source review, pinned-Mathlib API checks, small
exact rational identities, and static dependency counts. No Lean build,
elaboration, CI run, or large certificate replay has been performed. The
proof bodies remain subject to subsequent compilation and kernel checking.

## Exact stationary selection (F2)

`Coordinates.lean` defines the nested-radical chain through four circle
vertices, the fifth contact vertex, the two stationarity equations, and the
five equality parameters. `Weights.lean` derives the seven contact weights
and five positive circle weights from those coordinates. Its last vertical
force balance follows from position stationarity.

`Expression.lean` connects rational interval syntax to differentiable real
expressions, retaining nonzero denominator and positive radicand obligations.
The 49 local existence and numerical bracket formula certificates remain.
`Analysis.lean` constructs an interior minimizer in the local rectangle,
proves strict monotonicity and continuity of its minimized value in radius,
and selects `qStar` at its unique zero.

Global uniqueness now follows from geometry on the original broad domain.
`CircleConvexity` proves strict position convexity on the complete closed
radical domain. `EnvelopePosition` locates its unique minimum in the fixed
window `[87/100,11/10]`. `EnvelopeDifferentiation` derives the actual smooth
minimizer and both envelope derivatives using the implicit-function theorem.
At every critical tilt, whole-interval circle comparisons and the six
`CriticalHessian` estimates make the envelope second derivative positive,
including when the defect is positive. An intervening-maximum argument gives
critical-point uniqueness and global minimality on the closed tilt interval.
Finite radius inclusion then identifies the radius of any stationary zero.

`GeometricStationary.stationary_chain_unique` identifies all original chain
coordinates. `Stationary.stationary_unique` applies it to the constructed
witness, and `stationary_local` follows from that equality. The generated
global root-cover decision is deleted; neither `CompactRootCover` nor
`RootCover` is in the active theorem's import closure. No external stationary
witness, local-box membership, Hessian sign, or global-minimum property is
assumed. See `research/eight/formalization/STATIONARY_GEOMETRY.md` for the
full proof chain and its uncompiled-source status.

The principal exports are:

- `qStar`, `sharpData`, and `sharpData_stationary`;
- `qStar_bracket` and `qStar_limits`;
- `stationary_unique` and `exact_stationary_existsUnique`;
- `sharp_coordinates` and `sharp_y`.

Hand sources: `EXACT_CONFIGURATION_AND_FREEDOM.md`,
`ANALYTIC_EXACT_CONSTRUCTION.md`, `HUMAN_FIVE_CORNER.md`,
`HUMAN_FAMILY_CLOSURE.md`, and `UNRESTRICTED_EIGHT_SQUARE_HAND_PROOF.md`,
Section 1. The retained sharp bracket arithmetic follows the expressions
in `verify_hand_sharp_ceiling_bracket.py`.

## Adaptive and terminal comparison (F9)

`Adaptive.lean` proves existence and uniqueness of the position-stationary
value at each tilt in the terminal interval. `AdaptiveBounds.lean` supplies
the original-owner first-order reserves from exact rational expression
certificates. `PerturbationBounds.lean` supplies bounds on the quadratic and
cubic remainder coefficients. The current adaptive bounds retain 256 indices
and 21 scalar checks per index, totaling 5,376. Their fixed-box interval
utility is now in `IntervalEnclosure.lean`, separate from the retired root
search. This extraction does not replace those quantitative estimates.

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

## Pure statement mirror

`../../StatementEight.lean` defines the explicit stationary predicate and
selects its root by ordinary `Classical.epsilon`. It imports primitive
geometry and Mathlib, without importing the eight-square proofs. It also
contains the complete five-parameter domain and both model orientations.
`StatementLink.lean` proves the predicate has a unique actual solution,
identifies its selected coordinates with `sharpData`, and proves the pure
radius and model set equal those used by the analytic proof.

The public `Optimal.lean` registry uses these pure definitions; the n=8
branch of the root `optimum_spec` uses `Eight.radius_statement` and
`Eight.models_statement`. `scripts/sync-challenge.py --write` materializes
the Geometry, StatementEight, and Optimal definitions in dependency order
inside the Mathlib-only Challenge source. This source copier performs no
Lean compilation or comparator execution. The Challenge retains its two
intentional theorem statement stubs, now with the same range through eight
as the implemented public theorem statements.

## Generated data

The generators write Lean expressions and rational arithmetic proof
objects. The theorem statements interpret those expressions over the
reals. A successful Python run is not used as a Lean premise.

- `generate_stationary.py`: local derivatives, Hessian bounds, root brackets,
  and coordinate brackets. The default no longer reconstructs a root cover;
  `--legacy-root-cover` explicitly enables that historical archive;
- `generate_adaptive.py`: adaptive position brackets, all nine owner
  reserves, edge weight bounds, and perturbation remainder bounds;
- `generate_equality.py`: the explicit equality box and its strict
  containment, core, and central separation reserves.

The remaining generated arithmetic data are available to the later Lean
pass. Historical root-search utilities remain outside the active proof
dependency graph; their former decision module has been deleted.
