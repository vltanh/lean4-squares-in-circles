# n=9 — finite subgates for the unrestricted G2 closure

**Checkpoint 2026-10-22.** The mathematical target is:
for every nine-square Packing at squared radius q≤1105/256,
derive a proved sharp terminal inequality (at equality preserve all
possible families). The class contains independently rotated squares,
including configurations with oblique-only pairwise separators. This
file separates **closed global facts** from **conditional branch results**
and explicitly states each remaining obstruction.

## Dependency diagram

G2.0 (exact encoding and false-normalization tests) CLOSED
  |
  +-- G2.T1 (four-anchor long/short stress) CLOSED: terminal, conditional
  +-- G2.T2 (four-corner grid stress) CLOSED: terminal, conditional
  +-- G2.T3 (global triple transversal) CLOSED: unconditional, weak
  |
  +-- G2.C (common-coordinate-separable class)
  |      C1 rank injection CLOSED
  |      C2 full 3x3 grid excluded CLOSED
  |      C3 four-chain exists CLOSED
  |      C4.1 chain-shadow barrier and coherent/zigzag split CLOSED
  |      C4.2a middle-pair zigzag normal form + cap bound CLOSED
  |      C4.2b exclude crossed perpendicular four-chain CLOSED
  |      C4.2c eliminate entire large-zigzag branch CLOSED
  |      C4.3a signed 4+3-chain terminal CLOSED
  |      C4.3b 3×3 center-band terminal CLOSED
  |      C4.3c residual five squares x-chain≤2 CLOSED
  |      C4.4 coordinate-separable closure CLOSED
  |
  +-- G2.O (genuinely oblique pairs)
  |      O1 refute global common-frame normalization CLOSED
  |      O2 identify invariant forcing anchor skeleton OR
  |         deform into a terminal class, without increasing q OPEN
  |
  +-- G2.I (center in one open square) OPEN
  +-- G2.B (center on boundary but in no interior) OPEN
  +-- G2.E (center outside all closed squares) OPEN
  |
  +-- G2.X (exhaustive union of terminal branches) OPEN
  |
  +-- G4 unrestricted sharp theorem BLOCKED

The center-position trichotomy I/B/E is a *partition of input
configurations*. The coordinate-separable/oblique split C/O is another
partition *relative to a specified frame*. They intersect and are NOT
separate exhaustive independent lists of cases to add together.
The correct final G2.X theorem should use whichever partition allows
a short proof, with no double-counting or unnamed exceptional class.

## 1. Three exact terminal templates: closed

**G2.T1 — Long/short four-anchor stress: CLOSED (hand).**
Four squares, independently rotated; one endpoint pair has horizontal
center span ≥2+h_L+h_R, another has ≥1+h_L+h_R, and the first pair
lies completely above the other. Then q≥1105/256, with four pinned
boundary anchors at equality.
Source: FOUR_ANCHOR_STRESS.md. No other five squares appear in the
proof.

**G2.T2 — Four-corner grid stress: CLOSED (hand).**
Four independently rotated squares forming four signed corners,
each with a one-square reserve in both horizontal and vertical
endpoint differences, force q≥9/2>1105/256.
Source: GRID_FOUR_CORNER_STRESS.md.

**G2.T3 — Independently rotated stratified nine-square theorem:
CLOSED within stratified class (hand).** If all nine squares admit
projection-disjoint horizontal layers and full vertical support
separation, then q≥1105/256. Equality includes only layer sizes
3,4,2 (or mirror 2,4,3), and its exact necessary-and-sufficient
parameter domain is in STRATIFIED_EQUALITY_FAMILY.md.

These are **terminal** theorems, not global structure extraction.

## 2. Common-frame coordinate-separable branch

Fix a frame (e,f). An arbitrary pair is coordinate-separated if
its open projections are disjoint along e or f. Some rotations
can be allowed, but this property is an added hypothesis.

**G2.C1 — Rank injection: CLOSED.**
The two longest-chain ranks map n coordinate-separated squares
injectively into the product of the two chain lengths: n≤ab.

**G2.C2 — 3×3 rank grid excluded: CLOSED.**
For n=9 and a,b≤3, all ranks are occupied. Equal y-rank forces
horizontal separability, and equal x-rank forces vertical
separability. The four corners certify the grid stress,
q≥9/2>1105/256.

**G2.C3 — Four-chain extraction: CLOSED.**
At q≤1105/256 no projection-separated chain of five fits.
Thus coordinate-separable n=9 packings have a horizontal or
vertical chain of four squares. This is an unconditional
implication **within** the coordinate-separable class.

**G2.C4.1 — Shadow barrier and finite incidence: CLOSED.**
[FOUR_CHAIN_SHADOW_BARRIER.md](FOUR_CHAIN_SHADOW_BARRIER.md)
proves that a four-chain covers almost the entire disk projection:
the total complement of its four projection intervals is below 1/4.
Every other square must have positive projection overlap with
1, 2 or 3 consecutive chain squares. In the coordinate-separable
class, each other square lies above/below those it overlaps, or
there is a chain-center vertical gap of at least two.
This is a finite incidence classification, not a claim that the
five extra squares form globally separated layers.

**G2.C4.2 — Large-zigzag branch: CLOSED (hand).**
C4.2a/b normalize the large zigzag; C4.2c gives the complete
five-extra-square obstruction, using a three-region capacity
argument requiring only the center disk bound and the necessary
L-infinity center separation. No generated table or MILP claim
enters the final hand proof.

**G2.C4.2a — Zigzag position and cap control: CLOSED.**
[FOUR_CHAIN_ZIGZAG_NORMAL_FORM.md](FOUR_CHAIN_ZIGZAG_NORMAL_FORM.md)
proves, for *arbitrary independent orientations*, that all four
horizontal chain center x-coordinates lie in narrow rational
intervals around (-3/2,-1/2,1/2,3/2), the outer center heights
have absolute value <2/5, and any vertical center gap ≥2
can only occur between the two inner chain squares. Those inner
centers must straddle the axis above 1/2 and below -1/2.
Moreover, at most one other square can fit entirely above the
higher inner square, and at most one entirely below the lower.

**G2.C4.2b — No perpendicular four-chain in zigzag: CLOSED.**
[NO_CROSSED_FOUR_CHAINS_IN_ZIGZAG.md](NO_CROSSED_FOUR_CHAINS_IN_ZIGZAG.md)
shows by exact center-coordinate comparisons that, in the
common-coordinate-separable class, a zigzag horizontal four-chain
cannot coexist with a vertical four-chain. Therefore its
rank rectangle is exactly 4×3 (and nine rank cells are occupied
among twelve).

**G2.C4.2c — All 4×3 zigzags: CLOSED (hand).**
[ZIGZAG_BRANCH_CLOSED.md](ZIGZAG_BRANCH_CLOSED.md) proves the
following *complete* exclusion: no nine-square configuration in
(q\le1105/256) is coordinate-separable in one orthonormal
frame and contains a four-horizontal-projection chain with
vertical center diameter ≥2. From the four center bounds,
the five extras fall into a left (capacity 2), central
(capacity 1), and right (capacity 2) region. If these
capacities were saturated, three extras must all lie in a
vertical band of height <1 and a horizontal band of width
<21/20, impossible for pairwise coordinate-separated unit
squares. All square orientations remain arbitrary.

**G2.O4 — Inner-pair shadow domination: CLOSED (hand).**
[INNER_PAIR_SHADOW_DOMINATION.md](INNER_PAIR_SHADOW_DOMINATION.md)
proves, WITHOUT a common-frame separability premise for the
five other squares, that whenever four square projections are
disjoint at (q\le1105/256), every other square's open
projection intersects one of the two inner chain squares.
The singleton incidence blocks {1} and {4} are impossible
because they force center distance <1 from an extreme square.
Every allowed incidence block is consecutive and contains 2
or 3. This is a global geometric input conditional only on the
existence of a four-chain, valid with oblique-only separators.

**G2.C4.3a — Signed matched-chain terminal: CLOSED (hand).**
[PAIRED_FOUR_ANCHOR_STRESS.md](PAIRED_FOUR_ANCHOR_STRESS.md)
proves a general long/short four-anchor dual using weights 23 and 9,
requiring only the sum of vertical gaps instead of a common seam.
[SIGNED_MATCHED_CHAIN_STRESS.md](SIGNED_MATCHED_CHAIN_STRESS.md)
strengthens it to **independently chosen vertical signs** for the two
corresponding endpoint pairs. Its endpoint interlocking lemma proves
that in any q≤q* packing, the left endpoints of *disjoint*
horizontal four- and three-chains necessarily overlap in horizontal
projection, as do the right endpoints, regardless of orientations.
Consequently **any common-coordinate-separable nine-square packing
containing disjoint 4+3 horizontal projection chains obeys q≥q*.**
Mixed vertical signs are covered by the same dual, and all equality
outer anchors are determined for each sign choice. This is a full
terminal structural class, not a small angle subcase.

**G2.C4.3b — Three-by-three center bands: CLOSED (hand).**
[THREE_BAND_GRID_OBSTRUCTION.md](THREE_BAND_GRID_OBSTRUCTION.md)
proves q≥9/2 for a coordinate-separable packing partitioned into
three horizontal projection chains of three with centers in the
upper (y≥1/2), middle (-1/2<y<1/2), and lower (y≤-1/2)
bands. Corresponding endpoint projections overlap because their
x-center differences are <39/40, so the grid stress applies.
No common orientations or fixed within-row heights are assumed.

**G2.C4.3c — Sharp residual five-square complement: CLOSED (hand).**

- **C4.3c.1 CLOSED:** [TWO_COLUMN_COMPLEMENT_REDUCTION.md](TWO_COLUMN_COMPLEMENT_REDUCTION.md)
  gives two vertical-projection-disjoint rank stacks of sizes
  **(4,1)** or **(3,2)** and an exact middle-height displacement.
- **C4.3c.2 CLOSED:** [FOUR_PLUS_FOUR_PLUS_ONE_EXCLUSION.md](FOUR_PLUS_FOUR_PLUS_ONE_EXCLUSION.md)
  rules out **all (4,1)** complements by a four-quadrant center
  cover. Eight crossed-chain squares can fit; the ninth cannot.
- **C4.3c.3 CLOSED:** [COORDINATE_SEPARABLE_NINE_COMPLETE.md](COORDINATE_SEPARABLE_NINE_COMPLETE.md)
  supplies the missing **(3,2)** sharp proof. With x-chain
  height ≤2 and five complementary squares, an x-antichain
  of four would give the excluded (4,1) case, so x-width≤3.
  An *elementary five-element matching lemma* partitions the
  five-square x-order into **two disjoint comparable pairs**
  \(L_1\prec_x R_1,L_2\prec_x R_2\), plus a singleton F.
  Exact outer-strip bounds prove:
  any complementary square with an x-successor overlaps
  the horizontal projection of the left inner M-anchor,
  and one with an x-predecessor overlaps that of the right
  inner anchor. The singleton F has a predecessor, a
  successor, or neither. Assigning it appropriately gives
  two x-antichains of sizes (3,2)/(2,3), each attached to
  a **different** inner anchor. By common-coordinate
  separation, these become **two disjoint perpendicular
  projection-separated chains of lengths four and three**.
  The existing signed 4+3 stress forces \(q\ge Q\) with
  the known equality structures.
- **C4.3c.4 CLOSED (conditional equality):** [SIGNED_MATCHED_EQUALITY_FAMILY.md](SIGNED_MATCHED_EQUALITY_FAMILY.md)
  gives the necessary-and-sufficient parameterization
  whenever the signed terminal chain hypothesis holds.
  [TWO_STACK_SHARP_EQUALITY_WITNESS.md](TWO_STACK_SHARP_EQUALITY_WITNESS.md)
  is an exact **(3,2) equality** packing, so the sharp
  result correctly **retains**, rather than excludes,
  this whole structural possibility.

**G2.C4.3 — Coherent-sign branch: CLOSED (hand).**
The x-disjoint 4+3 terminal, three-band grid
obstruction and now the entire two-stack complement
have complete geometric proofs. There is no residual
coordinate-separable case.

**G2.C4.4 — Full coordinate-separable nine-square theorem:
CLOSED (hand).** In the class where all pairs are
separated along one *common* orthonormal frame, nine
independently rotated unit squares always require
\[
                             q\ge Q=1105/256.
\]
Any equality packing in this class admits **in one
of the two coordinate directions** two disjoint
signed 4+3 terminal chains, so its seven chain
squares have the signed equality skeleton.
Source: [COORDINATE_SEPARABLE_NINE_COMPLETE.md](COORDINATE_SEPARABLE_NINE_COMPLETE.md).

**Critical limitation:** This does not prove the unrestricted
n=9 theorem, because [NO_GLOBAL_ORTHOGONAL_FRAME.md](NO_GLOBAL_ORTHOGONAL_FRAME.md)
shows that a legitimate sharp-radius packing may have
an **oblique-only** separating pair and fail common-frame
separability entirely. Global O3/O4/O5 remain OPEN.
No n=9 Lean/kernel verification or independent full
audit has been performed.

## 3. Oblique-separator branch

**G2.O1 — No global orthogonal frame: CLOSED negative control.**
NO_GLOBAL_ORTHOGONAL_FRAME.md exhibits a complete exact
nine-square packing at q=q*: seven rigid aligned anchors,
two other squares whose own oblique direction is the only
separating axis between them. The adjacent contacting anchors
force any globally separating frame to be axis aligned,
and that frame fails for the two upper squares.
Therefore global coordinate separability is a FALSE
normalization for unrestricted nine-square packings.

**G2.O2 — Anchor extraction permitting free oblique edges: OPEN.**
Find a geometrically invariant distinction between squares
forced into a sharp boundary skeleton and squares which can
move/turn freely. A possible route is to prove every q≤q*
packing can be deformed within its disk to a terminal
four-anchor model, or belongs to a small exceptional
geometric family with its own terminal dual. Any deformation
must explicitly preserve non-overlapping open interiors
throughout. Replacing an original packing by a visually
similar drawing is not a proof.

**G2.O2a — Exact separator-graph convex dual: CLOSED (general method).**
[SEPARATOR_GRAPH_CONVEX_DUAL.md](SEPARATOR_GRAPH_CONVEX_DUAL.md)
shows that with fixed square orientations and an actual selected
edge-normal separator for each required pair, the center feasibility
problem is convex. It gives a full explicit weak-dual bound, with
nonnegative separator multipliers and unit-square radial support,
eliminating **all center coordinates** from proof certificates.
It does **not** classify the finite owner graphs or prove uniformly
sharp orientation inequalities; O2/O3 remain the substantive gates.

**G2.O3 — Oblique stress/exception closure: OPEN.**
If O2 yields new non-row patterns, prove their lower bound
without attempting a long discretized list of tilt intervals.
No bound on the number of oblique-only pairs is presently known.

## 4. Exact origin-position partition (all three open)

For every fixed disk center o, its relation to the union of
nine closed squares falls in exactly one of three cases:

**G2.I — interior:** o is inside exactly one square's open
interior (uniqueness follows from non-overlap). Exclude this
case or derive a terminal four-anchor/grid obstruction
without importing n=8 core lemmas at the larger radius.

**G2.B — boundary, not interior:** o lies on one or more
square boundaries but in no open square interior. This
includes the known sharp record packing and is essential
for equality. Extract its sharp skeleton without treating
the record contact graph as universally compulsory.

**G2.E — exterior:** o belongs to none of the nine closed
squares. Derive a full angle/support exclusion or a
terminal decomposition, allowing tilted square outlines.

**Closure criteria** for I/B/E: a theorem from only Packing
and that case condition, with a finite provably exhaustive
conclusion. A conditional normalization of a selected
diagram does not close any of these gates.

## 5. Global assembly G2.X: OPEN

The final theorem must have no structural assumptions
on the nine square orientations, center or contact graph:

\[
 \forall S,o,q,\quad
 \mathrm{Packing}(S,o,\sqrt q)\wedge 0\le q\le q_*
 \Longrightarrow
 \text{one of finitely many *proved* sharp terminal hypotheses}.
\]

If exact equality packings admit a new terminal stress
pattern, include it rather than forcing the current 4+3
structure. Each leaf must terminate in a proved lower
bound and include a complete equality analysis as needed.

Once G2.X is closed, G4 derives the sharp radius immediately
by applying terminal theorems and the already known construction.
Until then, G4 is genuinely OPEN.

## 6. Completed equality branch and remaining global equality task

**G5.M (signed matched-chain equality): CLOSED as a conditional hand theorem.**
[SIGNED_MATCHED_EQUALITY_FAMILY.md](SIGNED_MATCHED_EQUALITY_FAMILY.md)
classifies the *entire terminal branch* of signed matched 4+3
projection chains at q=Q: four pinned endpoints, three inner
slider heights with exact mutual disjointness conditions, and
two arbitrary freely oriented squares checked by 15 true SAT
pair inequalities. Includes mixed endpoint signs, oblique free
separators, and the new exact two-stack equality witness.

**G5.S (stratified equality): CLOSED as a hand theorem.**
STRATIFIED_EQUALITY_FAMILY.md gives an explicit
three-slider-plus-two-free-squares model with necessary and
sufficient inequalities, preserving independent orientations.
Its parameter domain has nine local degrees of freedom.

**G5.U (unrestricted equality): OPEN.**
One must prove every optimal packing lies in a finite union
of explicitly parameterized families. The current G5.S
domain is provably not exhaustive as a family of record-radius
packings: the oblique example admits no global orthogonal coordinate
frame separating all its pairs, whereas every stratification would
supply exactly such a frame.
It still has the seven-anchor skeleton, and a future larger
four-anchor-based parameter domain may absorb it.

## 7. Strategy: avoid minor-boundary rabbit holes

The **remaining principal mathematical task** is G2.O3–O5:
structural coverage and sharp orientation-uniform stresses for
**arbitrary oblique-only separating axes**. The whole common-frame
coordinate-separable branch is now CLOSED by hand; do not
reopen its two-column or large-zigzag subcases by tightening
individual angle/height bounds.
Do not invest effort in strengthening the constants in
G2.1/G2.2, or excluding one of infinitely many very
small angular subintervals. Only prove facts that close
an entire named structural class or produce a rigorous
counterexample invalidating a proposed global gate.

Computer assistance should be used to:
- falsify structural conjectures via exact admissible packings;
- identify the real finite separator/adjacency graph alternatives;
- discover simple dual stress identities, then replace numerical
  evidence with a complete hand argument.

Exploration itself never counts as a proof. If C4 and O2 fail,
make a structural pivot to a different global invariant, and
keep the failed assumption documented. No claim is made
that this roadmap guarantees closure of an open problem.
