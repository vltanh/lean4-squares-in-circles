# n=8 formalization: source draft status

**Deliverable: an uncompiled Lean source draft of the unrestricted eight-square
argument, including the exact optimum and the five-parameter equality family.**
The F0–F11 source stages, pure statement integration, and public assembly are
written. The independent statement mirror through n=8 has been materialized as
source. This status records the implementation pass requested on 2026-10-18 UTC;
it does not report a checked formalization.

The user explicitly requested completion of the source before compilation or
audit. Accordingly, **no Lean compilation, build, CI run, certificate evaluation,
or audit was performed in this pass**. A theorem written with a proof body is
recorded below as a *source draft*, not as a theorem whose elaboration or kernel
checking has succeeded. Every F12 verification gate remains deferred.

## Provenance and delivery

The implementation transfers the roadmap and mathematical corpus from
[PR #9](https://github.com/vltanh/lean4-squares-in-circles/pull/9), at source commit
`a21c91f54039e805a637e983bc612bd130f39ee7`, into
[PR #10](https://github.com/vltanh/lean4-squares-in-circles/pull/10), stacked on
`research/eight-proof`. The inherited main baseline is
`089a1cb83aeb40eea802375c1f35d3301fda06a3`.

The transferred [ROADMAP.md](ROADMAP.md) remains the detailed mathematical and
implementation specification. [SOURCE.json](SOURCE.json) records the source
commit, source tree, baseline, pinned toolchain, and the instruction to deliver
without running Lean, CI, or an audit. The older mathematical development is
preserved in [PRE_SQUASH_COMMITS.json](../PRE_SQUASH_COMMITS.json) and
[PROGRESS_HISTORY.md](../PROGRESS_HISTORY.md).

## Stage ledger

Paths in this table are relative to `SquaresInCircles/Eight/` unless otherwise
specified. “Source draft complete” means that the intended definitions,
statements, proof bodies, and source data have been written. It makes no claim
about successful elaboration, proof checking, runtime, memory use, dependencies,
or axioms.

| Stage | Source draft and main exports | Source status |
|---|---|---|
| **F0 — model and interfaces** | `Model.lean`, `SeparatingAxis.lean`: squared-radius packing adapters, actual signed square axes, radial boundary states, original-cycle and radius-expansion transport records. | Source draft complete. |
| **F1 — real and rational certificate kernels** | `Arithmetic/`: rational intervals, Bernstein expansions, radical and trigonometric bounds, closed covers, real-expression box semantics, and the continuous interpretation of affine rows. `Generated/` holds the emitted data and claim bindings. | Source draft complete; evaluation deferred. |
| **F2 — exact stationary configuration** | `ExactFamily/Coordinates.lean`, `Expression.lean`, `RootCover.lean`, `Stationary.lean`, `Weights.lean`, and `Generated/`: exact radicals, stationary equations, uniqueness cover, exact weights, and radius brackets. Exports include `qStar_bracket`, `qStar_limits`, `sharpData_stationary`, and `exact_stationary_existsUnique`. | Source draft complete. |
| **F3 — central square and strict core** | `CentralCore.lean`, `CentralForbidden.lean`, `Arithmetic/CentralBandPolynomials.lean`: circle-arc measure argument, a unique central square, actual common-point inequalities, and the forbidden-ray budget. Exports include `central_core_and_exteriors` and `central_core_unique`. | Source draft complete. |
| **F4 — boundary reduction and radius transfer** | `BoundaryReduction.lean`, `RadiusTransfer.lean`: finite successive first-contact moves, explicit frame and signed-axis transport, original cyclic order, and fixed-ray radius expansion preserving every initially feasible signed axis. Exports include `boundary_reduction_exists`, `radius_expand_boundary_cycle`, `BoundaryCycle.expand`, and `boundary_normalization_exists`. | Source draft complete. |
| **F5 — frame range** | `Frames.lean`, `Arithmetic/FourTypePairs.lean`: four-type pair semantics on actual boundary cycles, finite cycle costs, shortest quarter-turn lifts, and the frame-diameter bound. Exports include `four_type_pair_bound`, `physical_cycle_width_bound`, and `physical_frame_lift_of_cost`. | Source draft complete; finite real-box decisions are unevaluated. |
| **F6 — quarter words and candidate normalization** | `QuarterWords.lean`, `BoundaryGeometry.lean`, `CycleActions.lean`, `Arithmetic/WordProblems.lean`, `Generated/WordCertificates.lean`, and `WordGeometry.lean`: actual gap and forward-axis reductions, finite word classification, all six wrong-word exclusions, dihedral transport, and the surviving word `0101011`. Exports include `boundary_gap_lower`, `boundary_forward_complete`, and `quarter_word_candidate`. | Source draft complete, including the final actual-cycle adapter. Finite real-box decisions are unevaluated. |
| **F7 — candidate cuts and mismatch bounds** | `Candidate/Model.lean`, `Geometry.lean`, `Nominal.lean`, `Mismatch.lean`, and `Generated/AffineBudgets.lean`: closed-domain cuts and successive mismatch budgets, attached to actual cycle geometry. `Candidate.Tables` exports `g_cut`, `t_cut`, `hd_cut`, `coarse_bound`, `enhanced_bound`, `middle_bound`, and `intermediate_bound`. | Source draft complete. |
| **F8 — final capture, owners, and tilt** | `Candidate/Capture.lean`, `Projection.lean`, `Dual.lean`, `DualApplication.lean`, `Generated/OwnerCompleteness.lean`, and `Generated/AffineBudgets.lean`: final mismatch budget, selected owners, projections, and tilt. Exports include `Candidate.capture`, `Candidate.Frame.pullback`, and `Candidate.Captured.pullback`. | Source draft complete. |
| **F9 — quantitative terminal dual** | `Terminal.lean` and the exact-family dual and perturbation modules: boundary error control, rigidity, and the stationary dual applied to the untouched original centers. Exports include `Terminal.boundary_quantitative`, `Terminal.boundary_rigid`, and `Terminal.original_pullback`. | Source draft complete. |
| **F10 — unrestricted lower bound** | `GlobalNormalization.lean`, `Theorem.lean`: actual packing to canonical candidate frame, optional reflection, boundary and radius transport, and original-center pullback. Exports include `global_normalization_exists`, `squared_radius_lower_bound`, and `lower_bound`. | Source draft complete. |
| **F11 — all equality cases and five freedoms** | `Equality.lean`, `ExactFamily/EqualityGeometry.lean`, `EqualityBox.lean`, `CentralParameters.lean`, `BoxRigidity.lean`, and `Theorem.lean`: necessary and sufficient weak parameter inequalities, reflected models, a full five-dimensional box, and noncongruence inside that box under arbitrary rigid isometries. Exports include `equality_iff_parameters` and `full_dimensional_equality_box`. | Source draft complete. |
| **F12 — public assembly and verification** | The n=8 assembly is written in `Theorem.lean`. `SquaresInCircles/StatementEight.lean` supplies the pure statement definitions, `ExactFamily/StatementLink.lean` connects them to F2/F11, and `SquaresInCircles/Optimal.lean` supplies the pure registry through 8. The root public theorems and independent `Challenge.lean` definition mirror are extended through 8. Compilation, generated decision evaluation, dependency and axiom inspection, comparator checking, and CI are postponed. | Public and independent-statement source integration complete; mirror materialized with Python only. **Verification deferred in full by the user.** |

## Main public statements written in source

The following names are in `SquaresInCircles.Eight` and are assembled in
[`SquaresInCircles/Eight/Theorem.lean`](../../../SquaresInCircles/Eight/Theorem.lean):

| Export | Intended mathematical content |
|---|---|
| `squared_radius_lower_bound` | Every packing of eight unit squares in an origin-centered disk with squared radius `q` satisfies `qStar ≤ q`. |
| `lower_bound` | The corresponding radius lower bound for a disk with arbitrary center. |
| `origin_equality_classification` | Every origin-centered equality packing belongs, up to the repository's congruence relation, to the explicit model family. |
| `uniqueness` | Equality classification at an arbitrary disk center. The historical interface name denotes classification by a family; it does not assert an isolated unique pose. |
| `optimum : Optimum 8` | The n=8 instance of the repository's optimum interface, including attainment and equality classification. |
| `isLeast` | `radius` is the least radius admitting a packing of eight unit squares. |
| `packing_iff` | A packing at `radius` is equivalent to congruence with a member of `models`. |
| `equality_iff_parameters` | A packing at `radius` is equivalent to an admissible five-parameter model, with an explicit optional reflection. |
| `full_dimensional_equality_box` | Every parameter point in the exhibited box gives an equality packing, and two points of that box give rigidly congruent packings exactly when the parameter points are equal. |

[`SquaresInCircles/StatementEight.lean`](../../../SquaresInCircles/StatementEight.lean)
supplies the n=8 definitions independently of the n=8 proof modules. It imports
the primitive geometry and Mathlib, defines a seven-real-coordinate `Root` and
its explicit broad-strip circle and derivative predicate `Root.IsStationary`,
and sets `selected := Classical.epsilon Root.IsStationary`. Its radius is
`sqrt selected.q`; it also defines the five `Parameters`, their 15-field weak
admissible domain, and both reflection branches of the model family.

[`SquaresInCircles/Optimal.lean`](../../../SquaresInCircles/Optimal.lean) imports
only this statement module and defines `optimalRadius` and `optimalPackings`
through n=8 using its pure definitions. The proof-side
[`ExactFamily/StatementLink.lean`](../../../SquaresInCircles/Eight/ExactFamily/StatementLink.lean)
contains `statement_stationary_existsUnique`, `selected_stationary`,
`selected_coordinates`, `qStar_eq`, and the domain and model correspondences.
These connect the pure squared radius `EightStatement.selected.q` to the
existing exact stationary coordinates. Its public bridges are
`Eight.radius_statement : Eight.radius = EightStatement.radius` and
`Eight.models_statement : Eight.models = EightStatement.models`.

[`SquaresInCircles.lean`](../../../SquaresInCircles.lean) imports the registry
and proof assembly, extends the public results through n=8, and uses these two
bridges in the n=8 branch of `optimum_spec`. This factors the statement
definitions away from the proof of stationary existence without changing the
F2 stationary construction. The independent `Challenge.lean` definitions have
also been materialized through n=8, as described below.

The exact radius is `sqrt qStar`. The source includes the strict rational bounds
`7831/2000 < qStar < 1957767069/500000000 < 9789/2500`. Radius bounds use the
repository's Euclidean squared quantity `normSq`; they do not substitute the
product-space norm on `ℝ × ℝ`.

## Generated source and unevaluated finite proofs

The affine certificate corpus contains **660,370 generated rows** in the
repository. The source includes their interval domains, polynomial data, closed
cover structure, semantic bindings to actual candidate quantities, and budget
wrappers. The full exact stationary-root cover data are also present as source
under `ExactFamily/Generated/`; their generation scripts remain alongside the
exact-family modules. The draft does not replace either corpus with a numerical
summary or a sampled success report.

F5 and F6 also use the real-expression interval compiler in
`Arithmetic/RealBox.lean`. Their source contains ordinary `by decide` proof
scripts for expressions of the form **`RealBox.certify 96 … = true`**. These
scripts have **not been evaluated**. Whether each finite decision returns
`true`, whether the semantic adapter elaborates, and what time or memory the
kernel reduction requires are all questions for the later verification pass.
The number `96` is a parameter of the written decision procedure; it is not an
observed successful proof run or a measured resource bound.

The finite quarter-word enumeration, polynomial identities, cover bookkeeping,
and rational arithmetic scripts are likewise unevaluated. The source is
organized to expose the actual real inequalities, all signed separating axes,
and closed endpoint coverage. That organization is part of the implementation;
it is not an audit result.

## Geometric and equality choices carried through the draft

The central core is the **closed** disk of radius `1/12`, contained in the
**open** central square. Closed square boundaries may touch. The central-core
conclusion supplies strict avoidance for the seven other squares.

Boundary reduction retains the actual original squares, cyclic order, fixed
physical frames, and selected separating-axis witnesses while moving one
center at a time to its first admissible boundary contact. It does not assume
that arbitrary outward motion preserves nonoverlap. The subsequent radius
expansion retains rays, tangents, frames, and all initially feasible signed
axes. The two transports are separate records because their invariants differ.

`GlobalNormalization` keeps both the untouched original centers and the boundary
cycles. Capture is obtained after expansion to `Q1`; capture data are pulled
back to the recovered cycle at `sourceLevel q = max q qMinus`. The final
stationary dual acts on the original centers. Original slider sectors are
derived from original cyclic order and the strict core, rather than assumed
from the directions of moved centers.

The candidate roles are `H, G, A, B, T, D, E`; the quarter word is `0101011`.
Reflection and cyclic reindexing are represented explicitly. The equality
family has five parameters `(x, y, w, z, eta)`, retains contact through weak
inequalities, and uses a half-open central-frame interval to choose a square
representative. The repository's `Congruent` relation uses rotation and
relabeling, so reflected equality models are included explicitly. The separate
box statement treats arbitrary rigid isometries and does not identify distinct
parameter points by an unrecorded reflection.

## Deferred F12 and comparator handoff

**No pass/fail conclusion is recorded for any verification gate.** Later work,
after the user authorizes it, should elaborate the source against the pinned
Lean `v4.35.0-rc3` and mathlib revision
`c55e6e786f49471c72fbddbec5415808896aec1e`, evaluate the written finite proofs,
resolve any source or resource failures, and inspect the resulting theorem
dependencies and axioms. The intended ordinary logical axioms are not an
observed axiom report. This pass did not run `#print axioms` or establish the
absence of unexpected dependencies.

**The pure statement and independent mirror source integration is complete.**
`StatementEight.lean` separates the explicit stationary predicate, selected
root, radius, and five-parameter models from the proof chain. The new
`StatementLink.lean` supplies proof bodies identifying those definitions with
the exact stationary configuration and equality family used in the theorem.
The stationary existence and uniqueness result is used in this bridge, rather
than imported by the pure registry. These source identities remain uncompiled.

[`scripts/sync-challenge.py`](../../../scripts/sync-challenge.py) extracts the
definition bodies from `Geometry.lean`, `StatementEight.lean`, and
`Optimal.lean`, in that order, and places them under one shared noncomputable
section and namespace in `Challenge.lean`. The command
`python3 scripts/sync-challenge.py --write` was run solely to materialize that
source. The resulting mirror has the registry and theorem bounds through n=8,
describes the reflected five-parameter family, and retains the two intentional
pre-existing Challenge theorem stubs. Its imports are Mathlib's angle module
and `Mathlib.Tactic`; it does not import the n=8 proof modules.

`scripts/verify-comparator.sh` was edited to invoke the extracted helper before
its existing comparator work, but **the comparator workflow was not run**.
The helper's source-writing mode does not elaborate Lean, evaluate the finite
proofs, or establish comparator agreement. Its default textual-drift mode was
not run as an audit in this pass either.

The later F12 owner should check the pure statement layer and its proof-side
identity bridge against the pinned toolchain, then run the independently
authorized comparator and theorem checks. The source architecture and mirror
are now supplied; comparator success, import independence after elaboration,
and the public theorem dependencies remain verification questions. Do not
hand-maintain a competing n=8 statement in `Challenge.lean`. See
[README.md](README.md) for the module map and handoff order.
