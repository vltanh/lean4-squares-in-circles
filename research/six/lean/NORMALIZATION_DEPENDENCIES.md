# Analytic normalization dependency review

## Endpoint and review scope

The isolated entry point is `SquaresInCircles/Six/AnalyticNormalization.lean`.
It imports `Normalization.StrongCardinal` and `Stress.CandidateCardinal`, which
lead to `Normalization.Complete` and the pure candidate-radius support chain.

The endpoint `Normalization.normalize_of_candidate` takes the original Packing
predicate and the candidate squared-radius bound. It returns a normalized
packing and the explicit `CongruentOrDiagonal` relation. Its constructor does
not accept a small-core, pin, window, A2, numerical-certificate or stress-table
hypothesis from the caller.

The mathematical source checkpoint is `4ec2d54aa24d8a2e0e1bb6649b96a2ef5310dd81`.
The isolated entry point and deferred audit were added through
`44f9727fb8826016dde7f0dd2946c740ea339e8a`.

The review consisted of reading the Six-module import headers and the changed
constructor/call sites, then traversing the manually recorded Six-only graph.
That graph has 82 reached Six modules and 124 Six-to-Six edges, with no cycle
and no reached forbidden module listed below. This is NOT an elaborated Lean
declaration-dependency audit or a fresh audit of every line in those modules.
The pre-existing Common, Seven, Geometry and Mathlib libraries are explicit
review boundaries; no new independent audit of those libraries is claimed.

## Mathematical paths

### Strong core

`Complete -> PinPacking -> StrongCore -> Input + Analytic.ForbiddenArcs`.
The forbidden-arc path uses the analytic small/large-center quadrant arguments,
genuine marker bounds and the finite five-marker empty-arc contradiction.
There is no import of `Normalization.Certificates.CentralGrid` or its checker.

### Fixed pins, broad windows and allowed central axes

`PinPacking -> Analytic.PinWindows -> PinLocations -> CapFixedPins /
PinCoordinates / FixedPinInclusions -> PinArc + OwnAxisWindows`.

The sixty-degree covering proof is a completed-square obstruction. The western
flank uses a second completed square. OWN windows use trigonometric concavity
and explicit endpoint fractions. The five-pin bijection supplies uniqueness;
uniqueness eliminates the wrong primary quadrants and gives all five windows.
Forbidden cardinal axes follow from the pin coordinates, while the two SEC
axes fail by the strong-core transverse bound.

The constructor calls `Analytic.five_pin_cover`, `Analytic.labelled_window`
and `Analytic.allowed_axis_of_pin`. It no longer calls `pin_cover_from_upper`
or `window_from_upper`. The reflected constructor likewise uses the actual-pin
coordinate lemma instead of a window certificate.

### Moving pins, order and cardinal geometry

`MovingPins -> Analytic.OwnMovingPin -> MovingPinPolynomial + CentralSAT`.
The polynomial proof is whole-interval algebra. Cardinal moving pins use actual
cap piercing.

`PairOrder -> Analytic.WestDiagonalOrder -> PairProjectionBounds +
PinProjections -> PinDirectedAxes -> PairCoordinates`.
All four actual pair axes are retained; broad windows are now supplied by the
analytic pin constructor.

`CardinalWindows -> Analytic.CardinalFrame -> CapSupport` supplies the six
cardinal-facing cases. `CardinalGeometry` transports the local cap results,
including one helper per side and both opposite-cardinal budgets. The two
cardinal hypotheses are not dropped.

### Appendix A and D-own

`Complete -> WestCardinalStress -> Analytic.WestStressGeometry`.
The historical eight-check implementation of WestCardinalStress has been
replaced, not merely renamed. The wrapper calls `west_cardinal_impossible`
with both proved core-exclusion inputs.

`WestSecondaryAxes` excludes the primary and reversed secondary directions on
the whole angle domain. The remaining two sources use one multiplier triple.
`WestStressMinorant` and `WestStressBounds` handle W-secondary by an affine
radical bound. `RadicalTrigConcavity`, `WestStressDConcavity`,
`WestStressDEndpoints` and `WestStressDPositive` handle D-secondary by displayed
second derivatives and the seven geometric endpoint values.

The D-secondary norm uses the positive mixed term
`53/200 + (9/40)*sin(u-t)`. A mistaken intermediate negative-sign/dominance
argument was removed during this continuation; the final theorem does not use
it. The actual force, norm and projection identities are in WestStressGeometry.

### Candidate-radius refinements

`Stress.CandidateCardinal -> CandidateRadius -> Complete +
CandidateRadiusConstants -> Candidate + ExactSupport`.
The exact candidate central box and opposite-cardinal budget are derived from
actual containment. They do not identify cStar with c0 or import the later
D-edge classification.

## Explicitly excluded mathematical modules

No module in the reviewed normalization path imports:

- `Six.ProofTools.Certificate`, Expression, RationalInterval, TrigInterval or
  the smooth-expression checker;
- `Six.Normalization.Certificates.Checks`, CentralGrid, ConeSemantics,
  Semantics or Model;
- `Six.Stress.FixedData.*`, ExactCover, RowTactics or the fixed D-edge
  classification;
- PairCertificateChecks, the common-pair numerical cover, or the unrestricted
  LowerBound/Uniqueness chain.

The namespace `Normalization.Certificates` persists in `PinData.lean` for the
ordinary real pin constants, phase centers and allowed-axis lists. It is a
historical namespace, not an executable certificate dependency. Small finite
index equalities and logical case choices are not numerical inequality checks.

## What actually ran

No Lean compilation, kernel checking, numerical search, interval subdivision,
certificate replay, generated-table verification, GitHub runner or remote
computation was used in this normalization conversion.

Local exact algebra reviewed 34 explicitly displayed identity/rational checks:
the completed squares, radical curvature numerator, rational constant bounds,
root endpoint comparisons, and the fourteen boundary lower values forced by
the concavity proof. No search chose these vertices; they are the vertices of
the order/sign domain. Those local arithmetic calculations are development
checks, not imported mathematical premises. The Lean source has its own
ordinary analytic and rational proof bodies.

`SixNormalizationAxiomAudit.lean` is now configured for the normalization and
refinement endpoints. Its commands have NOT executed. Actual elaboration,
proof-term/kernel acceptance and the transitive axiom output remain a separate
deferred validation gate. Static reachability cannot establish those results.

## Remaining work outside normalization

The analytic reduction to the later candidate D-edge graph and tighter common
helper domain still needs replacements for fixed-row/tail certificates. The
common pair envelope also still has outer and derivative-cover dependencies.
Those are excluded from AnalyticNormalization. Existing unrestricted endpoint
source cannot be accepted as the final human-analytic n=6 proof until those
separate dependencies are replaced and the final chain is validated.
