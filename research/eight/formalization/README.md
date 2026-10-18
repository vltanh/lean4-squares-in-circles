# Eight squares: Lean source draft

This directory carries the transferred formalization roadmap and the completion
record for the uncompiled n=8 Lean draft. The implementation follows the
unrestricted hand proof through the exact optimal radius and the complete
five-parameter equality family. The F0–F11 source stages, pure statement
integration, and public theorem assembly are written; the independent statement
mirror through n=8 has been materialized as source. The n=8 entry point is
[`SquaresInCircles/Eight/Theorem.lean`](../../../SquaresInCircles/Eight/Theorem.lean).

**This is source delivery before verification.** The user asked to finish the
draft without compiling Lean, running CI, or auditing it. None of those actions
was performed. Written proof bodies and generated certificate data remain
subject to elaboration, kernel checking, finite decision evaluation, and the
later F12 handoff. [STATUS.md](STATUS.md) records the stage-by-stage state, the
completed statement integration, and every deferred verification gate.

## Start here

| Document or source | Purpose |
|---|---|
| [ROADMAP.md](ROADMAP.md) | The transferred F0–F12 specification, proof dependencies, finite domains, and acceptance criteria. |
| [STATUS.md](STATUS.md) | What has been written, the public exports, and exactly which verification claims remain deferred. |
| [SOURCE.json](SOURCE.json) | Machine-readable source provenance, toolchain pins, and the instruction to deliver uncompiled source. |
| [UNRESTRICTED_EIGHT_SQUARE_HAND_PROOF.md](../UNRESTRICTED_EIGHT_SQUARE_HAND_PROOF.md) | The consolidated mathematical argument being transcribed. |
| [UNRESTRICTED_EIGHT_SQUARE_HAND_MANIFEST.json](../UNRESTRICTED_EIGHT_SQUARE_HAND_MANIFEST.json) | The inherited mathematical source and certificate manifest. |
| [PROGRESS_HISTORY.md](../PROGRESS_HISTORY.md) and [PRE_SQUASH_COMMITS.json](../PRE_SQUASH_COMMITS.json) | The preserved pre-squash development history. |

The source is inherited from
[PR #9](https://github.com/vltanh/lean4-squares-in-circles/pull/9), commit
`a21c91f54039e805a637e983bc612bd130f39ee7`. The source draft is delivered in
[PR #10](https://github.com/vltanh/lean4-squares-in-circles/pull/10), stacked on
the `research/eight-proof` branch. The pinned main baseline is
`089a1cb83aeb40eea802375c1f35d3301fda06a3`; the recorded toolchain is Lean
`v4.35.0-rc3` with mathlib
`c55e6e786f49471c72fbddbec5415808896aec1e`. These pins are provenance for future
checking, not evidence of a build in this pass.

## Mathematical target and public entry points

The argument uses squared radii internally. `qStar` is the exact stationary
squared radius, and `radius = sqrt qStar`. The source gives exact stationary
coordinates and weights and places the constant between the rational levels

```text
qMinus = 7831 / 2000
Q1     = 1957767069 / 500000000
Q0     = 9789 / 2500

qMinus < qStar < Q1 < Q0.
```

The public source statements in namespace `SquaresInCircles.Eight` include:

```lean
squared_radius_lower_bound
lower_bound
origin_equality_classification
uniqueness
optimum : Optimum 8
isLeast
packing_iff
equality_iff_parameters
full_dimensional_equality_box
```

`lower_bound` applies to eight unit squares in a disk with arbitrary center.
`optimum` assembles the repository's optimum interface, while `isLeast` states
the least admissible radius directly. `packing_iff` classifies radius-equality
packings by the model family. The historical name `uniqueness` is the equality
classification field; it does not assert a single isolated optimal pose.

`equality_iff_parameters` exposes the actual five parameters and their
admissibility conditions, including optional reflection. Its intended shape is:

```lean
Packing S o radius ↔
  ∃ reflected : Bool, ∃ p : EqualityParameters,
    p.Admissible sharpData ∧
    Congruent S o (reflectedModel reflected p)
```

`full_dimensional_equality_box` supplies a concrete box of admissible parameter
points and states that two packings from this box are congruent under arbitrary
rigid isometries precisely when the parameter points agree. The equality result
therefore includes five independent freedoms as well as its necessity and
converse directions.

The pure statement module
[`SquaresInCircles/StatementEight.lean`](../../../SquaresInCircles/StatementEight.lean)
defines a seven-real-coordinate `Root`, its explicit broad-strip circle and
derivative predicate `Root.IsStationary`, and
`selected := Classical.epsilon Root.IsStationary`. It defines the statement
radius as `sqrt selected.q`, the five `Parameters`, their 15-field weak
admissible domain, and both reflected and unreflected models. It imports the
primitive geometry and Mathlib, independently of the n=8 proof modules.

[`SquaresInCircles/Optimal.lean`](../../../SquaresInCircles/Optimal.lean) imports
only this statement layer and supplies the pure `optimalRadius` and
`optimalPackings` registry through n=8. The proof-side
[`ExactFamily/StatementLink.lean`](../../../SquaresInCircles/Eight/ExactFamily/StatementLink.lean)
identifies the selected root, radius, parameter domain, and models with the
existing exact-family construction. Its public exports
`Eight.radius_statement` and `Eight.models_statement` connect the two radius
and model definitions.

The root [`SquaresInCircles.lean`](../../../SquaresInCircles.lean) imports the
registry and proof assembly, extends the public results through n=8, and uses
those two bridges in the n=8 branch of `optimum_spec`. The independent
`Challenge.lean` definition mirror and its theorem bounds have also been
materialized through n=8 with a Python-only source-writing command. All these
source changes remain uncompiled, and comparator checking remains deferred.

## Source map

All module paths in this section are relative to
[`SquaresInCircles/Eight/`](../../../SquaresInCircles/Eight/).

### Packing geometry, boundary motion, and original configurations

| Modules | Role and useful names |
|---|---|
| `Model.lean`, `SeparatingAxis.lean` | Actual Euclidean squared containment, all signed square-frame separating axes, boundary states, `NeighborCycle`, `BoundaryCycle`, and `RadiusExpansion`. |
| `CentralCore.lean`, `CentralForbidden.lean` | Measured circle arcs, central-square existence and uniqueness, the strict radius-`1/12` core, real common-point inequalities, and finite forbidden-ray data. Main entry points: `central_core_and_exteriors`, `central_core_unique`. |
| `BoundaryReduction.lean` | Successive motion to first boundary contact with fixed physical frames, selected-axis witnesses, and cyclic order. Main entry point: `boundary_reduction_exists`. |
| `RadiusTransfer.lean` | Fixed-ray expansion to a larger radius preserving every initially feasible signed axis; extraction and retention of original exterior squares. Main entry points: `BoundaryCycle.expand`, `radius_expand_boundary_cycle`, `boundary_normalization_exists`. |
| `BoundaryGeometry.lean` | Actual pair gap `> 19/25`, its original-cycle version, the complementary upper gap bound, and complete reduction from all signed SAT axes to the four forward axes. Main entry points: `polar_order_gap_lower`, `boundary_gap_lower`, `boundary_forward_complete`. |
| `CycleActions.lean` | Exact rotation, reflection, cyclic reindexing, angle unwrapping, physical-frame transport, and signed-axis transport. The same action is applied to original and moved configurations. |
| `GlobalNormalization.lean` | `GlobalNormalization`, `boundary_candidate_normalization`, and `global_normalization_exists`: the unrestricted packing-to-candidate route, original source retention, explicit reflection, and original slider-sector recovery. |

The central core is closed and lies in the open central square. This strict
containment is distinct from closed-square packing, where boundary contacts are
allowed. All distances use the repository's squared Euclidean metric `normSq`;
the product norm on `ℝ × ℝ` is not substituted for Euclidean distance.

Two distinct deformation steps appear in the source. Boundary reduction moves
one center at a time to a first admissible contact and preserves original
cyclic order and selected witnesses. Radius expansion preserves rays, tangents,
frames, and all feasible signed axes. Their records retain the different
invariants explicitly. In particular, the proof draft does not infer
nonoverlap from arbitrary outward displacement.

`GlobalNormalization` retains untouched original centers, a recovered boundary
cycle at `sourceLevel q = max q qMinus`, and its expansion to `Q1`. This is what
allows the terminal argument to use both the captured boundary geometry and
the original packing. Original slider sectors are derived using the original
cyclic order and the strict core.

### Whole-domain reductions and candidate capture

| Modules | Role and useful names |
|---|---|
| `Frames.lean`, `Arithmetic/FourTypePairs.lean` | Actual four-type pair inequalities, finite cycle costs, periodic frame cost, zero-winding lifts, and frame diameter `< 7/10`. Main entry points: `four_type_pair_bound`, `physical_cycle_width_bound`, `physical_frame_lift_of_cost`. |
| `QuarterWords.lean` | The quarter increment sum, finite word classification, dihedral equivalence, and the candidate word `0101011`. |
| `Arithmetic/WordProblems.lean`, `Generated/WordCertificates.lean`, `WordGeometry.lean` | Whole-domain wrong-word problems and actual geometric adapters for all six exclusions. Main entry point: `quarter_word_candidate`. |
| `Candidate/Model.lean`, `Geometry.lean`, `Nominal.lean`, `Mismatch.lean` | Canonical roles `H, G, A, B, T, D, E`, candidate coordinates, closed cuts, and the mismatch chain. |
| `Generated/AffineBudgets.lean` | `Candidate.Tables.g_cut`, `t_cut`, `hd_cut`, `coarse_bound`, `enhanced_bound`, `middle_bound`, `intermediate_bound`, and `final_bound`. |
| `Candidate/Projection.lean`, `Dual.lean`, `DualApplication.lean`, `Capture.lean` | Owner completeness, projections, tilt, and capture assembly. Main entry points: `Candidate.capture`, `Candidate.Frame.pullback`, `Candidate.Captured.pullback`. |

The four-type and quarter-word reductions run on an auxiliary expansion to
`Q0`; the same frame lifts and quarter increments transfer back to `Q1`.
Dihedral normalization then supplies the candidate frame and the required
half-tangent sign, with reflection represented by an actual action on the
squares and axes. Candidate capture at `Q1` can be pulled back along
`RadiusExpansion` before applying the stationary dual to original centers.

### Exact stationary data, terminal rigidity, and equality

| Modules | Role and useful names |
|---|---|
| `ExactFamily/Coordinates.lean`, `Expression.lean`, `Analysis.lean`, `RootCover.lean`, `Stationary.lean`, `Weights.lean` | Exact radical coordinates and positive stationary weights, a closed stationary-root cover, and the exact constant. Main entry points: `qStar_bracket`, `qStar_limits`, `sharpData_stationary`, `exact_stationary_existsUnique`. |
| `ExactFamily/StatementLink.lean` | Identification of the pure statement root, radius, admissible domain, and models with the F2/F11 construction. Source exports include `statement_stationary_existsUnique`, `selected_stationary`, `selected_coordinates`, `qStar_eq`, `Eight.radius_statement`, and `Eight.models_statement`. |
| `ExactFamily/Adaptive.lean`, `AdaptiveBounds.lean`, `Perturbation.lean`, `PerturbationBounds.lean`, `PerturbationEstimates.lean`, `PerturbationModel.lean` | Explicit quantitative error bounds and perturbation estimates used by the terminal inequality. |
| `Terminal.lean` | Boundary quantitative control, rigidity, and the original-center stationary pullback. Main entry points: `Terminal.boundary_quantitative`, `Terminal.boundary_rigid`, `Terminal.original_pullback`. |
| `ExactFamily/CenterCompletion.lean`, `CentralParameters.lean`, `EqualityGeometry.lean`, `EqualityBox.lean`, `BoxRigidity.lean` | Central-square representatives, necessary and sufficient admissibility constraints, an explicit five-dimensional box, and parameter rigidity under arbitrary isometries. |
| `Equality.lean` | Model-family definitions, attainment, every admissible model packing, and recovery of admissibility from original geometry. Main entry points: `models`, `model_packing`, `model_reaches`, `admissible_of_original_geometry`, `five_parameter_box`. |
| `Theorem.lean` | Unrestricted lower bound and equality assembly, then the public `Optimum 8` instance and classification statements. |

The equality parameters `(x, y, w, z, eta)` retain weak inequalities where
contact is admissible. The central frame uses a half-open representative
interval. Since the repository's `Congruent` relation contains rotations and
relabelings, reflected models are explicit members of the family; the stronger
box rigidity statement independently allows arbitrary rigid isometries.

## Certificate source and its verification boundary

`Arithmetic/` contains the draft soundness layer: rational intervals,
Bernstein positivity, exact polynomial identities, radical bounds,
arctangent/trigonometric estimates, closed-cover composition, and continuous
semantics for affine rows and real-expression boxes. The source bindings are
intended to connect each finite inequality to actual square geometry, with all
radial branches, signs, and originally feasible axes represented.

The repository includes **660,370 generated affine rows**, their domain and
coverage data, and the direct budget wrappers in `Generated/`. The full
stationary-cover data are present in `ExactFamily/Generated/`, with the
generation scripts `generate_stationary.py`, `generate_adaptive.py`, and
`generate_equality.py` beside the exact-family modules. Polynomial-generation
metadata are recorded in `Generated/polynomial_generation_index.json`.

The F5/F6 real-box bridge uses ordinary source scripts of the form
`by decide` to prove equations of the form `RealBox.certify 96 … = true`.
**Those scripts have not been run.** The draft includes the decision procedure
and its semantic proof, but this source-delivery pass does not establish that
every requested decision succeeds, that every adapter elaborates, or that the
chosen computation fits practical time and memory limits. All such questions
belong to the later audit. The same restriction applies to finite enumeration,
rational arithmetic, and generated polynomial proof scripts elsewhere in the
tree.

Generated source volume is not a verification result. The complete data are
included so that the later pass can inspect and check the actual obligations
without reconstructing omitted tables or accepting an external success log.

## Independent statement source

The statement-layer factoring is complete in source. `StatementEight.lean`
contains the exact predicate and model definitions; `Optimal.lean` uses them
without importing the stationary existence proof. `StatementLink.lean` uses the
F2 existence and uniqueness result to connect the pure selected root to the
proof-side constant and equality family. This preserves the existing F2
construction while giving the comparator an independent definition boundary.

[`scripts/sync-challenge.py`](../../../scripts/sync-challenge.py) combines the
definition bodies from `Geometry.lean`, `StatementEight.lean`, and
`Optimal.lean`, in dependency order, beneath a shared noncomputable section and
namespace in `Challenge.lean`. Its `--write` mode preserves the header and
existing theorem region; the header and bounds were updated for n≤8 while the
two intentional pre-existing theorem stubs were retained. The mirror imports
only Mathlib's angle module and `Mathlib.Tactic`.

The command `python3 scripts/sync-challenge.py --write` was run to materialize
these definitions. **That was source generation only.** No Lean elaboration,
comparator verification, finite-proof evaluation, CI, or audit was performed.
The helper's default mode reports textual drift; that checking mode was not
run in this pass. `scripts/verify-comparator.sh` was edited to call the helper
before its existing comparator work, but the comparator workflow itself was
not executed.

## Deferred F12: a concrete handoff

The current delivery stops at written source. It leaves all build and audit
gates unrun. A future verification owner should work through the following
dependencies after the user authorizes that work:

1. **Use the recorded toolchain and dependency pins.** Begin with the inherited
   lock state; avoid changing the mathematical or library target while first
   determining the draft's elaboration state.
2. **Elaborate the arithmetic and geometric dependency layers.** Resolve actual
   source errors, then evaluate finite decisions and record any failed domain,
   identity, endpoint, or resource obligation. A written `by decide` block is
   still an unevaluated obligation until this step succeeds.
3. **Complete the original-packing assembly checks.** Check the full route
   through central-core extraction, deformation, all-axis radius expansion,
   candidate capture, stationary-original pullback, and equality necessity and
   converse. The public lower bound must retain its unrestricted packing
   hypothesis.
4. **Check the pure statement bridge and independent comparator.** The source
   factoring and through-8 mirror are now supplied. Elaborate `StatementEight`,
   `StatementLink`, and the pure registry, including the selected-root identity
   and the radius/model bridges used by `optimum_spec`. Then run the authorized
   comparator workflow against the independent `Challenge.lean` definitions.
   Python source materialization does not establish comparator agreement or
   successful Lean elaboration. Do not maintain a separate hand-written
   competing statement.
5. **Record the actual dependency and axiom results.** Inspect the elaborated
   public exports, their trust dependencies, and the resource behavior of the
   generated computations. The intended ordinary logical axioms are not an
   observed report. Run CI only when that work is authorized.

The public assembly, pure registry, identity bridge, and independent statement
mirror through n=8 are present as source. The source-writing helper was run;
the comparator, Lean, CI, and audit were not. **F12 verification is not complete
or checked**.

For stage details, use [STATUS.md](STATUS.md). For the mathematical acceptance
criteria that the later pass must assess, use [ROADMAP.md](ROADMAP.md).
