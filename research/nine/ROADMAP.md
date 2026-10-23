# n=9 — current proof roadmap and gate status

**Current status:** the entire common-coordinate-separable radius theorem
has a hand proof. The unrestricted oblique branch now has a proved
minimizer-to-stress reduction, a planar sparse contact-core reduction,
and a separate exact angular-stationarity reduction. **The unrestricted
sharp radius and complete global equality classification remain OPEN.**
No n=9 Lean compilation, CI or independent full manuscript audit is claimed.

## Canonical reading

- [DEEP_GATED_ROADMAP.md](DEEP_GATED_ROADMAP.md): theorem-level gates,
  subgates, dependencies and exact closure criteria.
- [G2_SUBGATES.md](G2_SUBGATES.md): live mathematical branch ledger.
- [README.md](README.md): proof-source index and handoff.

The target, using the repository's original Packing predicate, is

\[
 R^2\ge Q:=1105/256,\qquad R_9=\sqrt{1105}/16.
\]

An exact construction proves the upper bound. The global lower bound
must still cover independent orientations and genuine oblique-only
separators; a common orthogonal separating frame is false at equality.

## Live gate ledger

| Gate | Contract | Status |
|---|---|---|
| G0 | Exact construction, corner/SAT geometry, negative controls | CLOSED hand / exact counterexamples |
| G1 | Long/short, signed 4+3 and grid stresses; fixed-owner weak dual | CLOSED hand, with explicit terminal hypotheses |
| G2.C | Entire common-coordinate-separable n=9 sharp radius theorem | **CLOSED hand** |
| G2.O0–O2 | Oblique witness, exact SAT-owner language, fixed-owner center dual | CLOSED negative/framework |
| **G2.O3.0.2a–d** | Compact minimizer, strict noncontact axis selection, normalized active stress, exact dual attainment | **CLOSED hand** |
| **G2.O3.1a–d** | Four-junction stress uncrossing, planar outer-loaded core, <=19 terms, bounded degree-two paths | **CLOSED hand** |
| **G2.O3.1e** | Separate full angular-stationarity certificate, <=27 atoms | **CLOSED hand** |
| **G2.O3.2–O3.3** | Human-sized exhaustive sharp terminal classes for the cores **and the unstressed squares** | **OPEN** |
| **G2.O4–O5** | Uniform orientation bounds >=Q and full oblique closure | **OPEN / BLOCKED** |
| G2.X / G4 | Lower bound from unrestricted Packing alone | BLOCKED on the sharp oblique theorem |
| G5.0 | Stratified and signed matched-chain conditional equality models | CLOSED hand within those named classes |
| G5.U | Every unrestricted equality packing, both directions | OPEN / BLOCKED |
| G6 | Independent full hand-proof audit | Not completed |
| G7–G8 | Standard-kernel Lean proof, public integration and replay | NOT STARTED |

A CLOSED reduction need not be a lower-bound theorem. In particular,
none of the three new general stress theorems proves `q0 >= Q`.

## New unrestricted-branch results

### 1. Compactness and exact sparse stress

[SPARSE_MINIMIZER_STRESS.md](SPARSE_MINIMIZER_STRESS.md) proves:
if any unrestricted packing fits at `q<Q`, a global minimizer at
`q0<Q` exists. Selecting strict own-axis separators for all physically
noncontacting pairs gives a finite, regular constrained problem.
The elementary active-gradient alternative yields normalized
nonnegative multipliers on actual circle-contact vertices and actual
touching square pairs. At most **19 positive scalar terms** suffice
for the nine-square translational certificate. The existing
center-eliminating dual is **attained exactly** at `q0`.

Each positive-stress component has at least two circle-loaded squares;
an unloaded leaf or a circle-free positive self-stress is impossible.
One connected component can be retained and renormalized.

### 2. Planar core, with the circle-loaded vertices on the outer face

[PLANAR_STRESS_CORE.md](PLANAR_STRESS_CORE.md) proves that every
four-square point junction is an aligned 2x2 block. Select parallel
normals for its two opposite pairs and reroute the smaller crossing
stress onto the corresponding side contacts. This preserves all
translational balances and exact dual value while removing the
crossing. The resulting support graph has a planar embedding, and
all circle-loaded square nodes are incident to its exterior face.

Sparsification within this planar support restores the **19-term**
bound. After suppressing unloaded degree-two transmitting squares,
each remaining unloaded junction has degree at least three. Each
contracted path has **0, 1 or 2** internal squares and the exact gap

\[
 d\cdot(c_B-c_A)=h_A(d)+h_B(d)+2\sum_{i\text{ internal}}h_i(d).
\]

This is a proved geometric reduction for arbitrary orientations, not
an assertion that the full physical contact graph is planar.

### 3. All-angle stationarity without absolute-value differentiation

[ROTATION_STATIONARY_STRESS.md](ROTATION_STATIONARY_STRESS.md)
replaces every selected support maximum by four smooth vertex
inequalities. It proves exact stationarity in all translations and
independent square angles, including the derivative of the owner's
separating normal. Global rotation symmetry reduces the conic support
bound to **27 positive scalar atoms** for nine squares.

**Do not combine unproved properties:** the planar 19-term
translational stress and the angular 27-atom stress can be different.
No simultaneous planar-and-torque-balanced certificate is asserted.

## Exact executed regression checks

`check_sparse_stress.py` was executed using Fraction arithmetic, and
its local bytes were matched to the committed Git blob. The record
[SPARSE_STRESS_EXACT_CHECK.json](SPARSE_STRESS_EXACT_CHECK.json)
pins the source commit, Git blob, SHA-256, Python version and exit code.
It checks 36 physical SAT pairs, 36 corners, all node force balances,
all angular balances, the uncrossing identity, and exact dual value
`1105/256` on the known oblique upper-pair construction.

The example has 11 fixed-frame positive terms and a separate 18-atom
angular certificate. **These are regression checks of one witness,
not universal optimality or a substitute for the hand arguments.**

## The completed coordinate branch stays closed

[COORDINATE_SEPARABLE_NINE_COMPLETE.md](COORDINATE_SEPARABLE_NINE_COMPLETE.md)
proves the sharp lower bound for every packing separable along one
common orthogonal frame, even with independent square orientations.
It includes both two-stack cases: the (4,1) case is ruled out by
[FOUR_PLUS_FOUR_PLUS_ONE_EXCLUSION.md](FOUR_PLUS_FOUR_PLUS_ONE_EXCLUSION.md),
and a five-element matching completes (3,2) by a perpendicular
signed 4+3-chain stress. Do not reopen those cases for small
angle/height improvements.

The exact two-stack record witness must be kept at equality; global
stratification and global coordinate separability are false
normalizations. See TWO_STACK_SHARP_EQUALITY_WITNESS.md,
NONSTRATIFIED_PARALLEL_NINE.md and NO_GLOBAL_ORTHOGONAL_FRAME.md.

## Exact next mathematical obligation

Prove that **every physically realizable nine-square minimizing
configuration** whose contact core has the structure above satisfies
`q0>=Q`. The classification must retain the remaining unstressed
squares and their packing capacity: a stressed core of fewer than
nine squares need not itself require radius `sqrt(Q)`.

This requires a short exhaustive terminal classification and
orientation-uniform sharp inequalities, or a new global inequality
covering all such cores at once. The bounds 19 and 27 and the finite
path labels do not by themselves supply that theorem. A list of
all raw SAT assignments is not a human-readable closure.

After that comes unrestricted equality necessity, the independent
manuscript audit, Lean kernel formalization, and public integration.
PR #11 remains draft until those claimed deliverables are actually
proved and verified.
