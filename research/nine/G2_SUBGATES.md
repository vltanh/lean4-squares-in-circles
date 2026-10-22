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
  +-- G2.1 (four-anchor long/short stress) CLOSED: terminal, conditional
  +-- G2.2 (four-corner grid stress) CLOSED: terminal, conditional
  +-- G2.3 (global triple transversal) CLOSED: unconditional, weak
  |
  +-- G2.C (common-coordinate-separable class)
  |      C1 rank injection CLOSED
  |      C2 full 3x3 grid excluded CLOSED
  |      C3 four-chain exists CLOSED
  |      C4 convert four-chain to sharp terminal branch OPEN
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

**G2.1 — Long/short four-anchor stress: CLOSED (hand).**
Four squares, independently rotated; one endpoint pair has horizontal
center span ≥2+h_L+h_R, another has ≥1+h_L+h_R, and the first pair
lies completely above the other. Then q≥1105/256, with four pinned
boundary anchors at equality.
Source: FOUR_ANCHOR_STRESS.md. No other five squares appear in the
proof.

**G2.2 — Four-corner grid stress: CLOSED (hand).**
Four independently rotated squares forming four signed corners,
each with a one-square reserve in both horizontal and vertical
endpoint differences, force q≥9/2>1105/256.
Source: GRID_FOUR_CORNER_STRESS.md.

**G2.3 — Independently rotated stratified nine-square theorem:
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

**G2.C4 — Four-chain completion: OPEN.**
From a four-square chain plus five remaining squares
(all with arbitrary orientations but coordinate-separated
along one common frame), prove *one* of:
(a) four-anchor long/short stress;
(b) grid stress; or
(c) an explicitly defined third terminal inequality.
The conclusion must be proved for all members of the
quantified class, not a growing list of subclasses.

**Falsification test:** a single exact q=q* packing in the class
lacking (a),(b) shows that the claimed two-template exhaustiveness
is false, though a third alternative may still succeed.
No theorem asserts that C4 is already solved.

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

**G5.S (stratified equality): CLOSED as a hand theorem.**
STRATIFIED_EQUALITY_FAMILY.md gives an explicit
three-slider-plus-two-free-squares model with necessary and
sufficient inequalities, preserving independent orientations.
Its parameter domain has nine local degrees of freedom.

**G5.U (unrestricted equality): OPEN.**
One must prove every optimal packing lies in a finite union
of explicitly parameterized families. The current G5.S
domain need not be exhaustive; in particular the oblique
example lies outside global stratification in the anchor frame.
It still has the seven-anchor skeleton, and a future larger
four-anchor-based parameter domain may absorb it.

## 7. Strategy: avoid minor-boundary rabbit holes

The **two central research tasks** are C4 and O2/O3.
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
