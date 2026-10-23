# Nine unit squares in a circle — current research handoff

**Branch:** `research/nine-tablefree-hand` · **PR:** #11, draft.
**Target:** prove the unrestricted sharp squared radius `Q=1105/256`
and classify all attaining packings. An exact construction attains Q;
**the unrestricted lower bound and global equality necessity are OPEN**.

**Completed at the hand-proof level:** the whole common-coordinate-
separable theorem; unrestricted minimizer-to-exact-stress reduction;
a sparse planar translational core; angular stationarity; and the
new **physical force/torque contact-incidence reduction**. These are
not Lean-verified or independently audited end-to-end.

## Start here

[ROADMAP.md](ROADMAP.md) is the short master status.
[DEEP_GATED_ROADMAP.md](DEEP_GATED_ROADMAP.md) and
[G2_SUBGATES.md](G2_SUBGATES.md) contain the gate contracts and ledger.
The latest physical-contact extension is
[PHYSICAL_STRESS_GATE_UPDATE.md](PHYSICAL_STRESS_GATE_UPDATE.md),
which closes O3.1f.1–6 without changing the remaining sharp target.

## New unrestricted-branch hand theorems

### 1. Every hypothetical better packing has an exact sparse minimizing stress

[SPARSE_MINIMIZER_STRESS.md](SPARSE_MINIMIZER_STRESS.md) proves
compact attainment using finite closed SAT conditions and compact
center/frame sublevel sets. Any q<Q packing therefore yields an
unrestricted global minimizer q0<Q.

Select a strict true separator for every physically noncontacting pair.
An elementary active-gradient cone argument, with an explicit strict
center-expansion direction, produces normalized nonnegative stress on
actual circle-contact vertices and actual touching square pairs.
At most **19 positive scalar terms** suffice for fixed orientations,
and the earlier center-eliminating weak dual is **attained exactly**.
Each positive component has at least two circle-loaded square nodes;
one connected component can be retained. Unsupported internal
self-stresses and unloaded leaves are impossible.

**Boundary:** this certifies the unknown value q0, not the desired
inequality q0>=Q.

### 2. A planar, outer-loaded translational core

[PLANAR_STRESS_CORE.md](PLANAR_STRESS_CORE.md) proves that a four-way
square contact is an aligned 2x2 block. Choose parallel normal axes
for its two diagonally opposite pairs, then reroute the smaller
crossing stress onto side contacts. No square moves, and all center
forces and the exact dual value are preserved.

The support embeds planarly with all circle-loaded body nodes on the
outer face. Re-sparsification within that support gives <=19 terms.
Unloaded degree-two paths contain at most two internal squares at
q0<=Q. This is not planarity of the full physical contact graph and
does not preserve a separately chosen torque certificate.

### 3. Exact angular balance, with no absolute-value derivative shortcut

[ROTATION_STATIONARY_STRESS.md](ROTATION_STATIONARY_STRESS.md)
uses four smooth nonowner-vertex inequalities per selected own-axis
separator. It includes the owner's rotating-normal derivative and
proves all angle balances at every unrestricted minimizer. Global
rotation removes one gradient dimension, giving **<=27 atoms**.

This selected-owner certificate can differ from the 19-term planar
translational certificate. Its individual support-vertex atoms are
not automatically located in the actual pair intersection.

### 4. Physical force points, joint incidence planarity, discrete transmission

[PHYSICAL_CONTACT_STRESS.md](PHYSICAL_CONTACT_STRESS.md) resolves
the physical-lever issue by a complete local contact-type argument.
A vertex/edge contact has one smooth row, a point-only vertex/vertex
contact uses a strictly exposing common normal, and a partial side
contact uses its **two actual overlap endpoints**. For either sign
of relative rotation, at least one endpoint row is the full SAT
condition; requiring both is a valid smooth local feasible branch.

The resulting **<=27-atom physical certificate** has force and
angular balance at genuine shared points. After aggregating collinear
side forces, retain contact points as explicit junction nodes and
join them to square centers. This is a **straight-line planar
incidence network**, with junction degree 2–4 and all circle-loaded
bodies on the outer face. Angular balance is retained because the
physical application points are not discarded.

An unloaded square with exactly two positive body-pair forces must
transmit across opposite sides or opposite vertices. Its projected
width along the force is therefore exactly **1 or sqrt(2)**, not
an arbitrary angle-dependent width. At q0<=Q, a square-ended path
of these transmitters has internal reserve only

\[
                         0,\quad1,\quad\sqrt2,\quad2.
\]

The reserve 2 uses two side-normal squares; two internal squares with
even one diagonal transmitter exceed the center-diameter budget.

**Do not conflate the graphs:** this is a planar *incidence* network
with contact-point vertices. The simple body-pair graph need not be
planar, and the old 19-term planar body certificate is not thereby
proved torque-balanced. Square-ended path bounds are not bounds for
arbitrary paths ending at contact-junction points.

## Exact executed regressions

Both scripts use Python standard-library `Fraction` arithmetic.
Their local bytes and dependencies were compared with the committed
Git blob hashes before execution. Reports include source commits,
SHA-256, Python version, UTC execution time and exit code zero.

- [check_sparse_stress.py](check_sparse_stress.py), with
  [SPARSE_STRESS_EXACT_CHECK.json](SPARSE_STRESS_EXACT_CHECK.json):
  all 36 physical SAT pairs, all 36 corners, every node's center and
  angular balance, the exact dual Q and the four-junction uncrossing
  identity. The test packing uses the known obliquely separated
  upper pair; its fixed-frame stress has 11 terms and its angular
  witness has 18 atoms.
- [check_physical_contact_stress.py](check_physical_contact_stress.py),
  with [PHYSICAL_STRESS_EXACT_CHECK.json](PHYSICAL_STRESS_EXACT_CHECK.json):
  all seven force application points are in actual shared segments
  and correct support faces; all nine physical force and angular
  residuals vanish. Exact rational rotations check the two-endpoint
  support identities and endpoint gradient formulas.

These are **concrete-witness and local algebra regression checks**,
not a proof of universal optimality or an independent mathematical
review of the general manuscripts. No Lean or CI was run.

## The coordinate-separable class is fully closed by hand

[COORDINATE_SEPARABLE_NINE_COMPLETE.md](COORDINATE_SEPARABLE_NINE_COMPLETE.md)
proves q>=Q for every nine-square packing for which one common
perpendicular frame separates every pair in at least one projection.
All individual square orientations remain arbitrary.

Its proof combines the rank-grid extraction, signed 4+3 stress,
[FOUR_PLUS_FOUR_PLUS_ONE_EXCLUSION.md](FOUR_PLUS_FOUR_PLUS_ONE_EXCLUSION.md)
for the (4,1) complement, and an elementary five-element matching for
(3,2). A predecessor/successor overlap lemma and a three-case singleton
split turn the latter into perpendicular 4+3 chains. No remaining
coherent-side, two-column or zigzag case should be described as open
**inside this common-frame class**.

At equality that class has a signed matched-chain skeleton.
[SIGNED_MATCHED_EQUALITY_FAMILY.md](SIGNED_MATCHED_EQUALITY_FAMILY.md)
gives the full conditional parameter domain: four pinned endpoints,
three slider heights and two independent squares checked by actual
SAT conditions. The earlier stratified domain in
[STRATIFIED_EQUALITY_FAMILY.md](STRATIFIED_EQUALITY_FAMILY.md) is a
smaller conditional family, not globally exhaustive.

## Existing short analytic and structural tools

The sharp support arguments remain in
[ORIENTATION_STABLE_SEVEN_ANCHOR.md](ORIENTATION_STABLE_SEVEN_ANCHOR.md),
[FOUR_ANCHOR_STRESS.md](FOUR_ANCHOR_STRESS.md),
[PAIRED_FOUR_ANCHOR_STRESS.md](PAIRED_FOUR_ANCHOR_STRESS.md),
[SIGNED_MATCHED_CHAIN_STRESS.md](SIGNED_MATCHED_CHAIN_STRESS.md), and
[GRID_FOUR_CORNER_STRESS.md](GRID_FOUR_CORNER_STRESS.md).
The exact center-eliminating formula is
[SEPARATOR_GRAPH_CONVEX_DUAL.md](SEPARATOR_GRAPH_CONVEX_DUAL.md).

Structural predecessors are
[ORTHOGONAL_RANK_DICHOTOMY.md](ORTHOGONAL_RANK_DICHOTOMY.md),
[FOUR_CHAIN_SHADOW_BARRIER.md](FOUR_CHAIN_SHADOW_BARRIER.md),
[INNER_PAIR_SHADOW_DOMINATION.md](INNER_PAIR_SHADOW_DOMINATION.md),
[ZIGZAG_BRANCH_CLOSED.md](ZIGZAG_BRANCH_CLOSED.md),
[TWO_COLUMN_COMPLEMENT_REDUCTION.md](TWO_COLUMN_COMPLEMENT_REDUCTION.md),
[THREE_BAND_GRID_OBSTRUCTION.md](THREE_BAND_GRID_OBSTRUCTION.md), and
[GLOBAL_TRIPLE_TRANSVERSAL.md](GLOBAL_TRIPLE_TRANSVERSAL.md).
The older FOUR_CHAIN_ZIGZAG_NORMAL_FORM.md and
NO_CROSSED_FOUR_CHAINS_IN_ZIGZAG.md are intermediate lemmas, not
currently open zigzag obligations.

## Exact counterexamples that every global normalization must preserve

[NO_GLOBAL_ORTHOGONAL_FRAME.md](NO_GLOBAL_ORTHOGONAL_FRAME.md):
a record-radius packing has no orthogonal frame separating all pairs;
the free upper pair requires an oblique axis. This is why the full
coordinate theorem does not settle the unrestricted problem.

[TWO_STACK_SHARP_EQUALITY_WITNESS.md](TWO_STACK_SHARP_EQUALITY_WITNESS.md):
a physical q=Q packing lies in the residual two-column class and is
explained by perpendicular signed 4+3 chains. Excluding that whole
class including equality was a false shortcut.

[NONSTRATIFIED_PARALLEL_NINE.md](NONSTRATIFIED_PARALLEL_NINE.md):
even nine axis-aligned record-radius squares can lack stratification
in every frame. A global row normal form is not legitimate.

[CROSSED_FOUR_CHAINS_EIGHT_WITNESS.md](CROSSED_FOUR_CHAINS_EIGHT_WITNESS.md)
and [CENTER_RELAXATION_COUNTEREXAMPLE.md](CENTER_RELAXATION_COUNTEREXAMPLE.md)
show why the ninth physical square and actual support widths matter.
The construction in [HAND_PROOF.md](HAND_PROOF.md), the tilted witness
in [NONRIGID_WITNESS.md](NONRIGID_WITNESS.md), and the original controls
in [STRUCTURAL_NEGATIVE_TESTS.md](STRUCTURAL_NEGATIVE_TESTS.md) remain
valid within their exact stated scopes.

## The actual unresolved theorem

A hypothetical q<Q packing is now known to have an unrestricted
minimizer with the physical planar incidence network above. **What
is missing is a sharp inequality q0>=Q for every such physically
realizable nine-square network, including its unstressed-square
completion.** Neither stationarity, planarity, sparsity nor four
possible transmission labels implies that inequality by itself.

The next work must classify the remaining loaded/branching networks
and their completion capacities into a small exhaustive collection
of sharp terminal families, or derive a global invariant covering
all of them. Do not simply enumerate all labelled SAT assignments,
return to solved common-frame cases, or discard unstressed squares.

Then follow unrestricted equality necessity/converse, independent
hand audit, standard-kernel Lean formalization, and public registry
integration. The older UNRESTRICTED_BLOCKER_AUDIT.md is a historical
checkpoint: its old coordinate-branch blockers are superseded by the
current whole-class theorem and this handoff.

**Completion boundary:** the new arguments prove general necessary
structure for arbitrary minimizers. They do not yet prove T9.
