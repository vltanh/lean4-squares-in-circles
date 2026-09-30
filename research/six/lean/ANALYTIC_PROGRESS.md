# Human-analytic conversion ledger

Acceptance criterion: `HUMAN_ANALYTIC_STANDARD.md`.
PR #7, branch `feat/six-lean-proof`.

A checked item means its analytic argument, Lean proof body and source call
sites have been written and connected. It does NOT mean compilation or kernel
acceptance; those remain deferred. No numerical search, interval certificate,
generated stress-table verification or external success flag proves an item.

**The analytic normalization source is now assembled through
`Normalization.normalize_of_candidate`.** The complete unrestricted
human-analytic n=6 proof is still open at the separate downstream blocks below.

## Earlier completed replacements

- [x] A22 west/east weight signs from the shifted-sine identity.
- [x] Pure candidate-radius constants separated from packing normalization.
- [x] Diagonal coefficient bounds from exact candidate algebra.
- [x] Concavity endpoint reduction and explicit quartic chord identities.
- [x] Diagonal vertex inequality on its stated diamond domain, with the two geometric boundary quartics.
- [x] Actual vertex support premise implies that analytic minorant's angle domain.
- [x] Diagonal cap/vertex remainder, nonnegativity and unique zero; no diagonal checker.
- [x] Real support and balanced-pair formulas separated from computational reification.
- [x] Six cardinal-facing refinements from the short-transverse-axis cap obstruction.
- [x] Human-readable diagonal argument in `ANALYTIC_DIAGONAL_PROOF.md`.

## Strong core — analytic and connected

- [x] Genuine signed-marker bounds, closed marker point and west-cap lift exclusions.
- [x] All small-cy north cases with budget 3/8; all south cases with budget 2/3.
- [x] Small-cy east quadrant impossible for all actual central SAT alternatives.
- [x] All large-cy E/N/S cases, retaining the genuine marker branches.
- [x] Geometric quadrant assembly and modular marker lifting, with no central-coordinate grid.
- [x] Both forbidden arcs have length greater than 2pi/3.
- [x] Strict five-marker gap contradiction.
- [x] Unconditional `strong_central_box`, `strongCentralBox`, then N16, before pins/sectors/A2.

## Fixed pins and broad windows — now analytic and connected

- [x] Universal sixty-degree two-pin lemma from a single completed-square far-corner obstruction — `Analytic/PinArc.lean`.
- [x] OWN east window by trigonometric concavity and explicit endpoints — `OwnAxisWindows.lean`.
- [x] OWN west lower window and the W-pin upper window by analytic profiles.
- [x] Fixed E pin by contraction of the analytic moving-pin point.
- [x] Western flank pin by a second displayed completed square; middle arc by the sixty-degree lemma — `FixedPinInclusions.lean`.
- [x] Pure point-set symmetries and real-phase bookkeeping, independent of PinPacking — `PinCoordinates.lean`.
- [x] Cardinal cap-facing primary directions from four geometric quadrant cases.
- [x] Fixed pins in E/W caps, with N/S transported by local point-set identities — `CapFixedPins.lean`.
- [x] Complete five-pin covering with primary-location information retained — `PinLocations.lean`.
- [x] Finite five-square/five-pin bijection and uniqueness of the assigned pin.
- [x] All five broad labelled windows from unique-pin location, not a separate numerical window check — `PinWindows.lean`.
- [x] Forbidden cardinal axes from pin coordinates; SEC axes from the strong core.
- [x] `PinPacking` constructor calls the analytic covering/window/axis lemmas.
- [x] Reflected PinPacking uses the analytic pin-coordinate lemma; its last window-certificate call is removed.

## Remaining normalization outputs — analytic and connected

- [x] Actual side-nearest foot and chart bounds from the strong core.
- [x] The complete OWN moving-pin polynomial chain, plus cardinal piercing cases.
- [x] W/D order from all four actual pair axes and the now-analytic broad windows.
- [x] The remaining cyclic primary order links.
- [x] One global D-normalizing diagonal reflection, explicitly recorded.
- [x] Cardinal-preferred two-choice rule and exclusion of D-south.
- [x] Cap-frame transport, one cardinal helper per side and both moving pins.
- [x] Opposite-cardinal budgets retaining BOTH hypotheses.
- [x] N25+ for cardinal E/N and exact candidate-radius box/budget refinements.

## Appendix A — eight finite checks replaced

- [x] Whole-domain projection estimates exclude both primary and reversed secondary axes — `WestSecondaryAxes.lean`.
- [x] Both surviving secondary sources use one triple (3/10,9/20,1/4).
- [x] Correct actual force and norm identities, including the PLUS mixed term in the D-secondary W-force norm — `WestStressGeometry.lean`.
- [x] W-secondary positivity from one affine radical majorant, separate concavity and seven geometric vertices — `WestStressMinorant.lean`, `WestStressBounds.lean`.
- [x] Explicit radical second-derivative identity and whole-domain concavity criterion — `RadicalTrigConcavity.lean`.
- [x] D-secondary coordinate/diagonal concavity, rational root endpoint bounds and the same seven vertices — `WestStressDConcavity.lean`, `WestStressDEndpoints.lean`, `WestStressDPositive.lean`.
- [x] Actual separating inequalities and universal vertex support imply a nonpositive defect, contradicting either analytic positive bound.
- [x] Replace `Normalization/WestCardinalStress.lean` with the analytic wrapper; remove its finite checker implementation.
- [x] Supply both already proved core-exclusion inputs explicitly at the D-west call site.
- [x] D is canonically OWN, including exclusion of cardinal ties.

## Normalization assembly and review

- [x] `normalize_of_ceiling` and `normalize_of_candidate` use the analytic constructor and analytic Appendix A.
- [x] Isolated `Six/AnalyticNormalization.lean`; included in `Six/Analytic.lean`.
- [x] Deferred `SixNormalizationAxiomAudit.lean` for the actual normalization/refinement endpoints; NOT executed.
- [x] Human-readable companion `ANALYTIC_NORMALIZATION_PROOF.md` with completed squares, profiles, force formulas, curvature identity and endpoint reserves.
- [x] Manual Six-import-header/call-site review; the recorded 82-node Six-only graph has no cycle or reached listed computational module.
- [x] Explicit review boundary: existing Common/Seven/Geometry/Mathlib libraries, Lean elaboration and kernel dependencies are not newly validated by that static graph.
- [x] Local exact review of 34 displayed identity/rational comparisons at the mathematically forced endpoints; no search or subdivision, and no result imported as a proof premise.

The legacy `Normalization.Certificates` namespace in `PinData.lean` contains
ordinary real pin data. It is not an import of the executable certificate
modules. See `NORMALIZATION_DEPENDENCIES.md` for the precise review scope.

## Still open — D-edge classification and candidate domain

- [ ] Replace default/Appendix-C fixed-row classification by conceptual whole-domain analytic stress arguments.
- [ ] Replace the 53 hard-cell table without numerical partition verification.
- [ ] Replace candidate tail and bridge stress certificates.
- [ ] Derive the candidate D-edge graph and tighter common helper domain analytically.

## Still open — pair envelope and unrestricted endpoints

- [ ] Analytic common pair envelope for every source and central-bit choice.
- [ ] Replace the outer pair cover and local derivative certificates, including support/sign walls.
- [ ] Final balanced closure from only analytic scalar bounds and analytic domain reduction.
- [ ] Reconnect equality reconstruction and candidate reflection symmetry through that chain.
- [ ] Review all transitive mathematical dependencies of lower bound, uniqueness and public Optimum 6.
- [ ] Complete the independent human-readable proof for those remaining downstream blocks.
- [ ] Compiler/kernel/axiom validation, separate from source completion and the analytic criterion.

Existing unrestricted endpoint source still depends on those computational
blocks and is not accepted as the final human-analytic proof. Completing
normalization does not mark those separate items complete.

## Principal normalization-conversion checkpoints

- `5cf282c`: earlier strong-core analytic arc connection.
- `6d73d4a`: sixty-degree two-pin covering.
- `0b237bc`: actual PinPacking constructed with analytic pin/windows/axes.
- `c690e9e`: analytic Appendix A connected to D-own and the normalization endpoint.
- `4ec2d54`: final radical-curvature identity orientation correction.
- `9502244`: isolated analytic normalization entry point.
- `39afd23`: include normalization in the analytic development root.
- `44f9727`: configure the deferred normalization axiom audit.
- `d0902b8`: human-readable normalization companion.
- `1964e03`: record static dependency review and its limits.

The intermediate erroneous D-secondary norm-sign/dominance argument was removed
and replaced by the separate correct curvature proof before the endpoint was
connected. It is not a premise of the completed normalization source.
