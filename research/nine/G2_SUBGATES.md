# n=9 — live G2 mathematical subgate ledger

**Current target:** prove the unrestricted sharp bound `q >= Q = 1105/256`
for nine independently rotatable unit squares, with complete equality
classification afterwards. **The bound is not yet proved globally.**

The entire common-coordinate-separable branch is CLOSED by hand.
The unrestricted branch now has a proved global-minimizer reduction,
a sparse planar actual-contact stress core, and a separate exact
angular-stationarity certificate. The remaining task is the sharp
core/completion inequality, not existence of multipliers or another
small-angle estimate.

See [DEEP_GATED_ROADMAP.md](DEEP_GATED_ROADMAP.md) for complete contracts
and [ROADMAP.md](ROADMAP.md) for the short master status. CLOSED here
means a written hand proof with its stated hypotheses, not Lean or an
independent full audit. Earlier revisions remain in Git history.

## 1. Dependency summary

```text
G2.T1-T4 conditional geometric stresses / fixed-owner weak dual CLOSED
  |
  +-- G2.C entire common-coordinate-separable class             CLOSED
  |     C1 rank-product/four-chain extraction                   CLOSED
  |     C2 shadow / inner-pair incidence                        CLOSED
  |     C3 whole large-zigzag exclusion                         CLOSED
  |     C4.3a signed 4+3 chain terminal                         CLOSED
  |     C4.3b three-band grid terminal                         CLOSED
  |     C4.3c(4,1) crossed four-chain + ninth exclusion          CLOSED
  |     C4.3c(3,2) matching + perpendicular 4+3                CLOSED
  |     C4.4 sharp whole common-frame theorem                  CLOSED
  |
  +-- G2.O unrestricted oblique branch                         PARTIAL
        O0/O1 negative controls and exact SAT language         CLOSED
        O2 fixed-owner center-eliminating weak dual            CLOSED
        O3.0.2 unrestricted minimizer / sparse exact stress    CLOSED
        O3.1a-d planar outer-loaded <=19-term contact core     CLOSED
        O3.1e separate full-angle <=27-atom certificate        CLOSED
        O3.2 sharp core + unstressed completion alternatives   OPEN
        O3.3 human-sized exhaustive terminal classification   OPEN
        O4 sharp uniform inequalities >=Q                    OPEN
        O5 unrestricted assembly                             BLOCKED
               |
               +-- G2.X / G4 unrestricted sharp radius        BLOCKED
               +-- G5.U complete equality                     OPEN/BLOCKED
```

Legacy G2.O2/O3 referred broadly to the open oblique program; the
new O3.0.2/O3.1 subdivisions identify the parts now actually proved.
The origin-interior/boundary/exterior trichotomy is still a valid
optional partition, but its three sharp branch theorems were never
proved and are not prerequisites if the contact-core route succeeds.

## 2. Completed conditional terminal tools

**G2.T1 — long/short four-anchor stress: CLOSED hand.**
The four chosen endpoints have horizontal reserves 2 and 1 and the
required vertical support gaps. They force `q>=Q`, with pinned equality
anchors, even at arbitrary individual orientations. The signed version
permits independent vertical directions for the two matching endpoint
pairs. Sources: FOUR_ANCHOR_STRESS.md, PAIRED_FOUR_ANCHOR_STRESS.md,
SIGNED_MATCHED_CHAIN_STRESS.md.

**G2.T2 — rotated cap rows / 4+3: CLOSED hand.**
ORIENTATION_STABLE_SEVEN_ANCHOR.md proves the all-angle square penalty,
cap-row bound and sharp seven-anchor theorem. ROTATED_STRATIFIED_NINE.md
covers the complete explicitly stratified class, not all packings.

**G2.T3 — four-corner grid: CLOSED hand.**
GRID_FOUR_CORNER_STRESS.md gives `q>=9/2>Q` from the four span reserves,
without an alignment assumption on the four square frames.

**G2.T4 — fixed-owner weak dual: CLOSED hand.**
SEPARATOR_GRAPH_CONVEX_DUAL.md gives an explicit lower bound for supplied
nonnegative separator stresses and circle weights. It eliminates center
coordinates while leaving the orientation variables and owner choices.
The new minimizer theorem below additionally proves exact attainment
for suitable stresses at an unrestricted minimizer.

## 3. Common-coordinate-separable branch: completely CLOSED hand

**Definition.** There is one orthonormal frame such that every pair of
squares is separated along at least one of its coordinate projections.
The nine individual orientations can still differ. This global-frame
hypothesis is false for some unrestricted record-radius packings.

**C1 rank extraction:** ORTHOGONAL_RANK_DICHOTOMY.md injects squares
into pairs of x/y longest-chain ranks. No five-chain fits; a complete
3x3 rank grid would force `q>=9/2`. Thus a four-chain exists.

**C2 incidence:** FOUR_CHAIN_SHADOW_BARRIER.md shows every extra square
meets one to three consecutive chain projections. The oblique-safe
INNER_PAIR_SHADOW_DOMINATION.md rules out exclusive outermost overlap,
so every extra square meets one of the middle two projections.

**C3 zigzag:** ZIGZAG_BRANCH_CLOSED.md excludes the entire large-zigzag
branch by capacities 2+1+2 and a contradiction when all are saturated.
The old intermediate 4x3 rank case is not an unresolved obligation.

**C4.3a:** a disjoint x-projection triple outside the four-chain gives
SIGNED_MATCHED_CHAIN_STRESS.md, covering all vertical endpoint signs.

**C4.3b:** THREE_BAND_GRID_OBSTRUCTION.md handles its full three-band
3+3+3 terminal class by corresponding endpoint overlap and grid stress.

**C4.3c.1–2 two-column normal form:** TWO_COLUMN_COMPLEMENT_REDUCTION.md
partitions five extras with x-chain height <=2 into two vertical stacks,
necessarily (4,1) or (3,2), and forces a middle-chain displacement.
This is a proved reduction, not a sharp exclusion on its own.

**C4.3c(4,1) CLOSED:** FOUR_PLUS_FOUR_PLUS_ONE_EXCLUSION.md excludes
disjoint perpendicular four-chains plus a ninth square. Four middle
centers occupy tiny quadrant boxes whose coordinate-exclusion regions
cover every possible ninth center. The eight-square crossed-chain
example remains valid; the ninth square is essential.

**C4.3c(3,2) CLOSED:** COORDINATE_SEPARABLE_NINE_COMPLETE.md proves:
no four-antichain is possible in the height-two five-element x-poset;
two disjoint comparable pairs plus a singleton exist. A predecessor/
successor overlap lemma attaches each antichain class to a different
middle four-chain anchor. The singleton's three cases complete two
disjoint **perpendicular 4+3 chains**, so the signed stress applies.

**C4.4 whole-class result CLOSED:** every common-coordinate-separable
nine-square packing satisfies `q>=Q`. At equality some frame direction
has a signed matched 4+3 skeleton, parametrized by
SIGNED_MATCHED_EQUALITY_FAMILY.md with the original physical constraints
on the two free squares retained. This is not global necessity for
arbitrary oblique-only pairs.

## 4. Unrestricted minimizer / actual-contact stress: CLOSED reduction

**Source:** [SPARSE_MINIMIZER_STRESS.md](SPARSE_MINIMIZER_STRESS.md).

### O3.0.2a Compactness [CLOSED]
Centers lie in a bounded disk, frames in compact unit circles, and
nonoverlap is a finite union of closed SAT conditions. Every subcritical
packing leads to a global minimizer at `q0<Q`. No row deformation occurs.

### O3.0.2b Physical-contact selection [CLOSED]
Choose a strict true own-axis separator for every pair whose closed
squares do not touch. Then every active chosen separator joins actual
physical contacts. At touching pairs retain any compatible true axis,
including the junction choices used in the planarization below.

### O3.0.2c Regularity / normalized stress [CLOSED]
The velocity `dot c_i=c_i`, `dot q=K` with sufficiently large `K`
strictly decreases every active constraint. A finite conic separation
argument supplies nonnegative circle-vertex and edge multipliers:

\[
 \sum_{i,k}\lambda_{i,k}=1,\qquad
 2\sum_k\lambda_{i,k}p_{i,k}+F_i=0.
\]

The circle vertices and separator pairs are genuinely active.
No abnormal objective multiplier or numerical optimizer is assumed.

### O3.0.2d Sparse exact dual [CLOSED]
In 19 center/radius variables, conic thinning gives **at most 19
positive scalar terms**, counting circle-vertex and edge terms together.
The existing center-eliminating weak dual attains `q0` exactly.
This is not an assertion that its unknown attained value is `Q`.

### O3.0.2e Connected loaded core [CLOSED]
Every positive-stress component has positive circle weight on at least
two distinct squares. A component without circle weight or an unloaded
leaf is impossible. One connected component can be retained and its
weights normalized without changing its exact radius certificate.

## 5. Planar outer-loaded contact core: CLOSED structural reduction

**Source:** [PLANAR_STRESS_CORE.md](PLANAR_STRESS_CORE.md).

### O3.1a Four-way junction [CLOSED]
At most four squares meet at a point; four meeting squares form an
aligned 2x2 block. Only its two opposite-pair point contacts can cause
crossings in the contact support drawing.

### O3.1b Compatible diagonal choice [CLOSED]
At each four-way junction choose the same one of its two frame axes
for both opposite-pair separators before extracting stress. The axes
are true and tight; the choices for different junctions do not conflict.

### O3.1c Exact force uncrossing [CLOSED]
Subtract the smaller of the two crossing weights from both, and add
that amount to the two corresponding side contacts. Every square's
net force and the exact dual value remain unchanged; one diagonal
vanishes. Added side contacts create no new crossing diagonal pair.
No square moves. Angular stationarity is **not** asserted preserved.

### O3.1d.1 Planarity and exterior loading [CLOSED]
Resolve the local incidence drawings as triangles or quadrilaterals
with at most one diagonal. The positive-stress support is planar.
Each circle point belongs to at most one square; its loaded square
is accessible to the exterior face. All loaded square nodes are
cofacial on that exterior face. The whole graph need not be outerplanar.

### O3.1d.2 Sparse planar core [CLOSED]
Thin the conic representation within the planar support and retain a
connected component: still at most 19 positive terms, at least two
circle atoms, hence at most 17 positive contact edges. The full physical
contact graph is not claimed planar.

### O3.1d.3 Transmission paths [CLOSED]
Unloaded degree-two nodes transmit equal opposite parallel forces.
Their tight gaps telescope. At q0<=Q, the center diameter bound
excludes a path with three or more internal unit squares. Thus every
contracted edge has **0,1,2 internal squares**. Retained unloaded
nodes have degree at least three; contracted parallel edges are allowed,
but a closed all-transmission loop is impossible.

## 6. Separate full angular certificate: CLOSED necessary condition

**Source:** [ROTATION_STATIONARY_STRESS.md](ROTATION_STATIONARY_STRESS.md).

### O3.1e.1 Smooth support encoding [CLOSED]
Replace a selected owner's support maximum by four smooth nonowner-
vertex inequalities. This handles parallel-angle ties without taking
an invalid derivative of an absolute value.

### O3.1e.2 Full stationarity [CLOSED]
The same strict active direction supplies normalized nonnegative
multipliers in all translations, angles and the squared radius.
The angular equations include the derivative of the owning square's
separator normal, not just the other square's rotated vertex.

### O3.1e.3 At most 27 atoms [CLOSED]
Global rotation symmetry removes one dimension of the gradient span.
Conic thinning therefore leaves at most 27 positive circle/support-
vertex atoms for nine squares. Grouping support atoms recovers exact
center-dual attainment. A positive support atom belongs to a selected
constraint; it is not automatically a point-force inside the actual
shared contact segment.

**Nonclaim:** the <=27 angular certificate and <=19 planar
translational certificate can differ. Any argument requiring both
properties of one stress must first prove that additional bridge.

## 7. Exact regression record: completed, not a universal proof

`check_sparse_stress.py` uses rational arithmetic on the known
record-radius construction with an obliquely separated free pair.
The executed source was matched by Git blob and SHA-256; the report
is [SPARSE_STRESS_EXACT_CHECK.json](SPARSE_STRESS_EXACT_CHECK.json).

It checks all 36 pairwise SAT conditions, all 36 square corners,
normalization and all node force balances, a dual value exactly
1105/256, all angular balances for a separate 18-atom witness, and
the exact four-junction uncrossing identity. The translational example
has 11 positive terms. These checks do not prove global optimality,
planarity for arbitrary graphs, or the full mathematical manuscripts.

## 8. Actual remaining mathematical obligations

### O3.2 — Sharp core/completion classification [OPEN]
Every hypothetical unrestricted counterexample now produces the
proved planar outer-loaded sparse core. Classify its feasible
geometric types **together with the unstressed remaining squares**.
A low-radius core of fewer than nine squares can exist; omitting its
completion constraints would invalidate a nine-square lower bound.

### O3.3 — Human-sized exhaustive terminal cover [OPEN]
Prove a small finite disjunction of signed 4+3/grid terminal families,
strictly impossible alternatives, or new sharp stress classes.
Account for bridges, cycles, contracted multiedges, zero-weight limits,
multiple circle-contact corners, and the actual count of all squares.
The finite bounds 19 and 27 alone do not constitute such a cover.

### O4 — Uniform sharp inequalities [OPEN]
Existence of exact multipliers at a minimizer is proved, but the
bound `q0>=Q` for every realizable nine-square core/completion remains
unproved. Obtain explicit inequalities valid over all orientations,
not sampled angle ranges or a mere numerical dual value.

### O5 / G2.X / G4 — Global sharp assembly [BLOCKED]
Combine the complete terminal cover and uniform sharp bounds, then
use minimizer attainment to contradict every hypothetical q<Q packing.
The known exact construction gives the converse upper bound.

### G5.U — Every unrestricted equality packing [OPEN]
After global optimality is proved, apply the necessary-condition
reduction to each original q=Q packing (it is then itself a global
minimizer). Prove necessity and sufficiency of every resulting
parameter domain. The current stratified and signed 4+3 families
remain conditional; no theorem makes them globally exhaustive yet.

### G6–G8 — Audit, Lean and integration [NOT COMPLETED]
Independent mathematical audit, standard-kernel Lean proof, final
axiom/dependency checks, and public n=9 theorem integration remain.
No compiled result, CI run or independent replay is asserted.

## 9. Progress rule

A new restriction on arbitrary minimizers closes a **reduction gate**,
not automatically the sharp theorem. The next acceptable advance must
cover a full remaining core/completion family or give one universal
sharp invariant. Do not return to tiny coordinate boundaries, repeat
the finished common-frame case, assume an unstressed square is free to
move, or merge the separate planar and torque certificates silently.
