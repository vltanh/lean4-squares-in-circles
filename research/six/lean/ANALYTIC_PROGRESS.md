# Human-analytic conversion ledger

Acceptance criterion: `HUMAN_ANALYTIC_STANDARD.md`.
Starting point: `fa1e1cd7c7a523fe7f3570927adce609a330fc28`, PR #7.

A checked item means an explicit analytic argument and its Lean proof body have
been written and connected. It does NOT mean compilation or kernel acceptance;
compilation remains deferred. No numerical search, interval-cover replay or
generated stress-table verification proves an item on this ledger.

The old computer-assisted lower-bound and uniqueness source remains in the
branch. It is not the accepted human-analytic proof while the dependencies
listed as open below remain on its mathematical path.

## Completed replacements

- [x] A22 west/east weight signs from the shifted-sine identity.
- [x] Pure candidate-radius constants separated from packing normalization.
- [x] Diagonal coefficient bounds from exact candidate algebra.
- [x] Concavity endpoint reduction and explicit quartic chord identity.
- [x] Diagonal vertex inequality by the diamond X+Y<=11/25 and its two geometric boundary quartics.
- [x] Actual vertex support premise implies the analytic minorant's angle domain.
- [x] Diagonal cap/vertex remainder, nonnegativity and unique zero; no diagonal checker.
- [x] Real support and balanced-pair formulas separated from computational reification.
- [x] Six cardinal-facing angle refinements from the short-transverse-axis cap obstruction.
- [x] Human-readable diagonal proof in `ANALYTIC_DIAGONAL_PROOF.md`.

## Strong core: completed analytic chain

- [x] Genuine signed-marker bounds, closed marker-point membership and west-cap lift exclusions.
- [x] Every small-cy north quadrant case with the single budget 3/8.
- [x] Every small-cy south quadrant case with the single budget 2/3.
- [x] Small-cy east quadrant impossible for all seven actual SAT alternatives.
- [x] Large-cy east quadrant: both secondary signs and both south-cap transverse signs.
- [x] Large-cy north OWN transverse bound and all other north alternatives.
- [x] Large-cy south OWN weighted-disk bound and south-cap quartic bound.
- [x] Geometric E/N/S/W quadrant assembly, with no central-coordinate grid.
- [x] Small arc (-pi/2+2/3,pi/2-3/8) and large arc (-27/50,pi/2), both longer than 2pi/3.
- [x] Modular marker-lift exclusion, including the possible 2pi shifts.
- [x] `Normalization.strong_central_box`, `strongCentralBox` and N16 now call these analytic arcs, not `Certificates.CentralGrid`.

The strong-core endpoint is established before pins, sectors and A2. The only
symmetry used in that argument proves the symmetric bound on the original
packing; it does not impose or reuse the later D-normalizing reflection.
The scalar ingredients are affine Taylor bounds, explicit completed squares,
weighted disk support, and one displayed quartic chord argument.

## Remaining normalization conversion

- [ ] Geometric five-pin covering without the reified certificate.
- [ ] Broad labelled angular windows and forbidden source-axis estimates.
- [ ] Confirm and connect the whole analytic OWN moving-pin dependency chain.
- [ ] Confirm and connect analytic W/D order with its broad-window inputs.
- [ ] Appendix A three-square exclusions without the eight finite stress checks.
- [ ] Reassemble normalization without any mathematical certificate dependency.

## D-edge classification and candidate domain

- [ ] Replace default/Appendix-C fixed-row classification by conceptual whole-domain analytic stress arguments.
- [ ] Replace the 53 hard-cell table without numerical partition verification.
- [ ] Replace tail and bridge stress certificates.
- [ ] Derive the candidate D-edge graph and common helper domain analytically.

## Pair envelope and unrestricted endpoints

- [ ] Analytic common pair envelope for every source and central-bit choice.
- [ ] Replace the outer pair cover and local derivative certificates, including all support/sign walls.
- [ ] Derive final balanced closure from only analytic pair/diagonal bounds and analytic domain reduction.
- [ ] Reconnect equality reconstruction and candidate reflection symmetry through that chain.
- [ ] Audit all transitive dependencies of lower bound, uniqueness and public Optimum 6.
- [ ] Complete the independent human-readable manuscript.
- [ ] Compiler/kernel/axiom validation, separately from the analytic criterion.

## Important scope boundaries

The diagonal remainder theorem still assumes its explicit DiagonalDomain.
Its inequality is analytic; the current proof that every packing reaches that
domain still uses fixed rows and tails. The cardinal-angle refinements still
use broad-window and pin inputs whose construction is being converted.

The strong-core certificate dependency is now removed. The remaining
pin/window, fixed-row and pair-envelope computations are not made acceptable
by that change. A compatibility alias calling an analytic theorem is harmless;
an actual finite-cover computation remains a disallowed mathematical premise.

## Commit journal

Earlier analytic checkpoints:
`2840595`, `8350473` (signs); `ed6407c` (endpoints); `2822b40`, `6a786bb`
(vertex minorant); `1f4eabf`, `dee0dc0` (constants); `84a667a`, `8ee42ad`,
`2c582bd` (vertex connection); `3e8f994`, `b872f0a`, `023f68f`, `4660362`,
`7db410e`, `ed45175`, `5210e66` (import separation); `3d9a98d`, `5d6e194`
(remainder); `a188138`, `3ef32ea` (cardinal frames); `b20d7ac`, `fba1ecb`
(analytic entry points); `b8b6f23` (diagonal companion).

Current strong-core conversion:
- `54bee5b`: real marker lifts, west-cap exclusions and signed marker bounds.
- `01c86bc`: complete small-center north quadrant.
- `ee73c0d`: small-center south quadrant and east impossibility.
- `207b587`: all large-center east cases.
- `1e2603f`: large-center north/south cases.
- `c2733a2`: complete arcs, their lengths and modular lift handling.
- `5cf282c`: replace the strong-core certificate chain in the actual normalization endpoint.
