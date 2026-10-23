# n=9 — current roadmap: six exhaustive tree cases, two closed

**Checkpoint:** 2026-10-23. **The unrestricted n=9 theorem remains OPEN.**
The full common-coordinate-separable class has a hand proof. The unrestricted stress program now has a **finite exhaustive tree-component classification**, and two of its six complete nine-square completion cases have been excluded. Four tree cases and the cyclic branch remain open. The new results are hand manuscripts pending independent mathematical audit; no Lean compilation or CI is claimed.

## Canonical reading and progress history

- [DEEP_GATED_ROADMAP.md](DEEP_GATED_ROADMAP.md): complete G0–G8 contracts, subgates and dependencies.
- [FINITE_TREE_CASE_LEDGER.md](FINITE_TREE_CASE_LEDGER.md): exact six-case inventory with checked/unchecked rows and UTC proof commits.
- [G2_SUBGATES.md](G2_SUBGATES.md): live mathematical G2 status.
- [PROGRESS_LEDGER.md](PROGRESS_LEDGER.md): append-only progress, exact scope and source provenance.
- [TREE_FINITE_VALIDATION.md](TREE_FINITE_VALIDATION.md): reproducible execution, physical stress witnesses and rejected shortcuts.
- [README.md](README.md): source index and handoff.

## Target

For all nine independently oriented unit squares satisfying the original Packing predicate inside a disk, prove

    R^2 >= Q = 1105/256,  hence R9 = sqrt(1105)/16,

then classify every equality packing. The exact construction attains Q. Unrestricted lower-bound and global equality necessity have not been proved.

## New finite reduction: all positive trees

Use the physical torque-balanced stress with the permitted nonradial normal choice at off-origin point-only vertex/vertex contacts. In the explicit window

    79/40 <= R <= sqrt(Q),

[TREE_BODY_LOCALIZATION.md](TREE_BODY_LOCALIZATION.md) proves:

1. Every unloaded tree body is central and circle-clear; at most four occur.
2. Every loaded tree body has radial S/D geometry, even when not a graph leaf.
3. Every unloaded body avoiding zero is a one-step side-normal transmitter to a single S terminal, with incoming origin-containing neighbors.

[TREE_RADIUS_QUANTIZATION.md](TREE_RADIUS_QUANTIZATION.md) then excludes origin-interior tree roots and proves:

> **Every positive tree component in the window has R^2=17/4.**
> All its unloaded squares contain zero on a side or at a vertex; all loaded squares are radial side-normal terminals.

If s counts the side-interior incidences and v the vertex incidences among the unloaded component bodies, disjoint tangent cones and the previous star exclusion give

    2s+v <= 4,   s+v >= 2.

These yield **exactly six cases**, retaining their continuous positions, angles, loads and all other physical packing squares. This is not an enumeration of sample poses.

**Window caveat:** the lower window is an explicit theorem premise. The existing n=8 lower bound can supply it by deleting a square, with its existing proof dependencies. An independent table-free proof must separately establish this coarse lower bound.

## Six-case live tree ledger

| Case | (s,v) | Complete geometric family | Status |
|---|---|---|---|
| TREE.20 | (2,0) | Two opposed side-origin bodies; staggered two-slider four-square path | OPEN; flat row alone excluded |
| TREE.11 | (1,1) | Side-origin + vertex-origin body; includes genuine nonaligned trees | OPEN |
| **TREE.12** | **(1,2)** | **One side body and two vertex bodies fill the full origin angle** | **CLOSED hand: <=8 total squares** |
| TREE.02 | (0,2) | Two vertex-origin bodies with all compatible cone angles | OPEN |
| TREE.03 | (0,3) | Three vertex-origin bodies with all compatible angular gaps | OPEN |
| **TREE.04** | **(0,4)** | **Four vertex bodies form the central 2x2 block** | **CLOSED hand: <=8 total squares** |

**Proofs of the two full cases:** [TREE_FINITE_COMPLETIONS.md](TREE_FINITE_COMPLETIONS.md).

- **TREE.12:** force balance requires all four cardinal loaded squares centered at (+/-3/2,0),(0,+/-3/2). The new **cardinal-cage theorem** confines every additional center to [-1/2,1/2]^2, using the actual square geometry to exclude diagonal pockets. At most four additional squares fit, even with arbitrary orientations and oblique separators.
- **TREE.04:** the unloaded bodies fill [-1,1]^2. The new **central-block capacity theorem** allows only the four cardinal outer centers, with forced alignment. Total capacity is eight.

Slider endpoints |tau|=1/2 are counted in vertex-incidence cases, not dropped. A selected core may use fewer than nine squares; both completion theorems retain all unstressed and other-component bodies.

## Global status ledger

| Gate | Status |
|---|---|
| G0 exact model, upper construction and negative controls | CLOSED hand at stated scope |
| G1 signed/grid/cap/row terminals | CLOSED hand under explicit hypotheses |
| G2.C whole common-coordinate-separable class | CLOSED hand |
| G2.O3.0–O3.1 minimizer, actual stress, physical torque, radial bridges | CLOSED hand necessary reductions |
| TREE.F1–F2 localization, all-tree radius quantization and six-case coverage | **NEW CLOSED hand reduction** |
| TREE.12 and TREE.04 full physical completions | **NEW CLOSED hand cases** |
| TREE.20, TREE.11, TREE.02, TREE.03 | OPEN |
| CYCLIC selected positive components | OPEN sharp finite cover/capacity theorem |
| G2.X / G4 unrestricted sharp radius | BLOCKED on complete coverage and sharpness |
| G5 unrestricted equality necessity/converse | OPEN/BLOCKED |
| G6 independent full mathematical audit | NOT COMPLETED |
| G7–G8 standard-kernel Lean and integration | NOT STARTED |

The <=19-term planar translational support, <=27-atom physical force/torque incidence stress and positive body-pair graph remain distinct. A tree proof cannot make a cycle's nonbridge forces radial.

## Exact execution and essential counterexamples

[check_finite_tree_cases.py](check_finite_tree_cases.py), source commit 8a6eea1, was matched by Git blob and SHA-256 and run at **2026-10-23 13:20:52 UTC** under Python 3.13.5, exit 0. [FINITE_TREE_EXACT_CHECK.json](FINITE_TREE_EXACT_CHECK.json) records **909 rational checks**, the six integer profiles, **seven exact physical force/torque tree examples**, cardinal-cage attainment and negative controls.

Important controls prevent false shortcuts:

- A nonaligned five-body TREE.11 really exists at 17/4. The missing obligation is its completion to nine, not core impossibility.
- A seven-body TREE.12 exists even though its completion to nine is impossible.
- Three squares can fit above a staggered row at 17/4; independent two-per-side capacities would be false.
- A positive star exists below the radius window, so that lower premise is essential.

These finite checks are not the universal proofs, an independent audit or a Lean certificate. The analytic manuscripts prove the stated classes; they still require independent review.

## Next exact obligations

1. **Finish the four unchecked tree rows:** each needs one full continuous-family capacity inequality, with the other physical squares retained. Do not introduce an endless sequence of small-angle/offset tests.
2. **Handle CYCLIC:** either prove a human-sized exhaustive geometric inventory with a sharp inequality per class, or a global cap/strip/stress invariant covering all cyclic completions.
3. **Assemble the unrestricted theorem:** include the explicit lower-window dependency, then complete equality necessity and sufficiency, independent audit, Lean proof and public integration.

**Progress metric:** two of six exhaustive tree cases closed is precise. It is not a claim that one third of the unrestricted proof is complete. PR #11 remains draft until the advertised full result and verification are delivered.
