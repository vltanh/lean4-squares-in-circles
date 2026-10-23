# Nine unit squares in a circle — research index and handoff

**Research branch:** `research/nine-tablefree-hand`, draft PR #11.
**Canonical roadmap:** [DEEP_GATED_ROADMAP.md](DEEP_GATED_ROADMAP.md).
**Live proof-status ledger:** [G2_SUBGATES.md](G2_SUBGATES.md).
**Short status:** [ROADMAP.md](ROADMAP.md).
**Status (2026-10-22):** sharp table-free hand proofs are complete for
the four-anchor long/short terminal inequality, the **new four-corner
grid stress**, the independently rotated 4-versus-3 pattern, and
**every independently rotated horizontally stratified nine-square packing**. The unrestricted n=9 global
lower bound and the complete unrestricted equality classification
are **OPEN**. No n=9 Lean compilation or kernel checking has run.

The record construction has squared radius
\[
 q_*=\frac{1105}{256},\qquad
 R_*=\frac{\sqrt{1105}}{16}.
\]
We have proved that this radius is **attained**. The universal
inequality \(R_9\ge R_*\) is not yet proved.

## Latest exact C3.3 progress: two-stack normal form, equality witness and conditional family

- **[TWO_COLUMN_COMPLEMENT_REDUCTION.md](TWO_COLUMN_COMPLEMENT_REDUCTION.md):**
  the *completed* combinatorial reduction of the five-square complement
  to two canonical vertical stacks of cardinalities `(4,1)` or `(3,2)`.
  A vertical triple's middle center has `|y| < 21/40`, forcing one
  inner four-chain center to have `|y| > 19/40`. Only the **sharp
  terminal inequality covering the entire complement** remains open.

- **[NONSTRATIFIED_PARALLEL_NINE.md](NONSTRATIFIED_PARALLEL_NINE.md):**
  the exact two-stack equality witness has **no horizontal
  stratification in any frame**, even though every square is
  axis-aligned. Edge contact forces a common separating frame
  to be aligned, and connected center-height gaps below one
  exclude a partition in both axis choices. Consequently
  stratifability cannot be a global equality normal form.


- **[TWO_STACK_SHARP_EQUALITY_WITNESS.md](TWO_STACK_SHARP_EQUALITY_WITNESS.md):**
  nine exact rational axis-aligned squares fit (q=1105/256),
  while a selected horizontal four-chain has a five-square
  complement with horizontal chain length **only two**.
  This **refutes any plan to rule out all such complements at equality**.
  On rotating the frame, disjoint **vertical** four- and
  three-square chains appear, giving a sharp signed stress.
- **[CROSSED_FOUR_CHAINS_EIGHT_WITNESS.md](CROSSED_FOUR_CHAINS_EIGHT_WITNESS.md):**
  eight exact square centers form disjoint perpendicular
  four-chains at squared radius (17/4<Q), so merely forbidding
  crossed four-chains is a false shortcut. That particular
  eight-square arrangement cannot accommodate a coordinate-
  separable ninth square at (q\le Q), as an exact global
  center-covering calculation proves.
- **[SIGNED_MATCHED_EQUALITY_FAMILY.md](SIGNED_MATCHED_EQUALITY_FAMILY.md):**
  the **complete conditional equality domain** for all signed
  matched 4+3 projection chains: all seven chain squares become
  axis-aligned, four boundary anchors pin, and three slider
  heights plus two freely rotating/positioned squares remain.
  Mixed signs and oblique-only free-square separation are allowed.
  This is broader than the stratified equality family; global
  necessity from arbitrary Packing remains OPEN.

**Corrected next theorem:** From every coordinate-separable
nine-square packing with a selected horizontal four-chain and
five-square complement of x-chain length at most two, derive a
**perpendicular-frame 4+3 terminal** or another *sharp*
certificate. The residual class is nonempty at equality.

## New structural closure: signed 4+3 projection chains

**[SIGNED_MATCHED_CHAIN_STRESS.md](SIGNED_MATCHED_CHAIN_STRESS.md)**
proves the entire common-coordinate-separable branch whenever the nine
squares contain two **disjoint** horizontal projection chains of sizes
four and three. The physical disk and center-distance bounds force
the corresponding outer endpoint horizontal projections to overlap.
The resulting vertical separators may point in *opposite* directions:
a signed four-tangent stress with weights 23 and 9 proves
\(q\ge1105/256\) in every sign pattern, without global row ordering.
This replaces the earlier common-seam requirement.

**[THREE_BAND_GRID_OBSTRUCTION.md](THREE_BAND_GRID_OBSTRUCTION.md)**
also excludes any common-frame coordinate-separable 3+3+3 packing
whose three x-projection chains occupy respectively the upper,
central and lower coarse center-height bands. The forced corresponding
endpoint vertical chains yield \(q\ge9/2\).

**Exact remaining coordinate-separable question:** If M is a horizontal four-projection chain and the five remaining
squares have horizontal projection-chain length at most **two**,
we now know this can occur **exactly at the record radius**. The
missing theorem is a sharp *all-poses lower bound* and equality
classification for this branch, possibly by a 90-degree frame switch.

**[SEPARATOR_GRAPH_CONVEX_DUAL.md](SEPARATOR_GRAPH_CONVEX_DUAL.md)**
gives a general convex weak-dual proof certificate for arbitrary
oblique SAT separating axes. Once orientations and selected separator
owners are fixed, all centers are eliminated exactly from its lower
bound. This shifts the global research problem toward a finite
**separator-graph coverage** theorem and orientation-uniform dual
inequalities, rather than enormous continuous center grids.

**[CENTER_RELAXATION_COUNTEREXAMPLE.md](CENTER_RELAXATION_COUNTEREXAMPLE.md)**
proves that center-radius and L-infinity spacing alone do not exclude
nine centers with crossed 4-chains; true square widths and supports
must be retained. This is a falsification control, not a packing at
the record radius.

## Latest subgate closure: global-frame obstruction and four-chain shadow

- **[G2_SUBGATES.md](G2_SUBGATES.md)** is the detailed finite
  branch ledger. The two genuinely open mathematical targets are
  **G2.C4.3c.3** (sharp whole-class stress for the `(4,1)` and `(3,2)`
  two-stack complement) and **G2.O3–O5** (arbitrary oblique separator
  graph coverage and uniform stresses). The two-stack rank decomposition,
  middle-height bound, and large-zigzag exclusion are already closed.
- **[NO_GLOBAL_ORTHOGONAL_FRAME.md](NO_GLOBAL_ORTHOGONAL_FRAME.md)**
  constructs nine exact unit squares at q=1105/256 with seven
  rigid anchors and two freely rotated top squares. The pair
  requires an oblique separator, while an adjacent touching
  anchor pair forces any common separating frame to be aligned.
  Hence *no* common perpendicular coordinate frame can
  separate all pairs. The rank-grid theorem cannot be
  promoted to unrestricted G2 by assuming global coordinates.
- **[INNER_PAIR_SHADOW_DOMINATION.md](INNER_PAIR_SHADOW_DOMINATION.md)**
  is a new *oblique-safe* G2 result. Conditional only on a
  horizontal four-projection chain, every other square must
  have positive projected overlap with M2 or M3, the two
  middle chain squares. Exclusive overlap with M1 or M4
  forces two inscribed unit-half-radius disks to intersect.
  Unlike the coordinate rank argument, this result assumes
  no common x/y separator for other-square interactions.
- **[ZIGZAG_BRANCH_CLOSED.md](ZIGZAG_BRANCH_CLOSED.md)**
  excludes every nine-square coordinate-separable four-chain
  with center-height zigzag at least two. Five other squares
  must fill regions with capacities 2, 1 and 2. Saturating them
  forces three centers into a narrow horizontal band, impossible
  for unit coordinate separation. This closes all C4.2 cases.
- **[FOUR_CHAIN_ZIGZAG_NORMAL_FORM.md](FOUR_CHAIN_ZIGZAG_NORMAL_FORM.md)**
  closes G2.C4.2a for all square orientations: any vertical
  zigzag ≥2 in a four-projection chain must be between the
  **two middle squares**. Their centers straddle the horizontal
  axis outside ±1/2; the outer center heights lie in ±2/5.
  Each extreme upper/lower vertical cap can hold at most one
  additional square.
- **[NO_CROSSED_FOUR_CHAINS_IN_ZIGZAG.md](NO_CROSSED_FOUR_CHAINS_IN_ZIGZAG.md)**
  closes G2.C4.2b: in a common coordinate-separable packing,
  a four-chain with a vertical zigzag ≥2 cannot coexist
  with a perpendicular four-chain. The entire zigzag branch
  therefore has rank sizes exactly (4,3), not an unbounded
  succession of cases. **The entire large-zigzag branch was subsequently
  excluded** by [ZIGZAG_BRANCH_CLOSED.md](ZIGZAG_BRANCH_CLOSED.md);
  the old 4×3 intermediate classification is not a live blocker.
- **[FOUR_CHAIN_SHADOW_BARRIER.md](FOUR_CHAIN_SHADOW_BARRIER.md)**
  proves an exact structural lemma for any four-square
  projection-separated chain: its four projection intervals
  leave under 1/4 of the disk's diameter uncovered, forcing
  each remaining square to overlap the projections of one,
  two or three consecutive chain squares. In a common-frame
  separable packing, a square switching from above to below
  its overlapping chain members forces their vertical centers
  to differ by at least 2. This closes the C4.1 subgate.
- **[STRATIFIED_EQUALITY_FAMILY.md](STRATIFIED_EQUALITY_FAMILY.md)**
  gives a necessary-and-sufficient explicit 9-parameter
  domain for all equality packings *within the stratified
  class*, retaining three scalar sliders and two freely
  rotated top squares. The no-global-frame witness proves
  this conditional family is not all record-radius packings.

**Current boundary:** G2's quantified global case coverage
and G4's sharp unrestricted theorem are **not proved**.
No Lean, CI, or full independent audit is claimed.

## Reading order

1. [DEEP_GATED_ROADMAP.md](DEEP_GATED_ROADMAP.md): authoritative
   G0–G8 gated roadmap with theorem-level subgates and subsubgates.
   [ROADMAP.md](ROADMAP.md) is the concise, current status summary,
   and [G2_SUBGATES.md](G2_SUBGATES.md) is the live technical ledger.
2. [ORTHOGONAL_RANK_DICHOTOMY.md](ORTHOGONAL_RANK_DICHOTOMY.md):
   a full combinatorial rank injection for any nine independently
   rotated squares whose pairwise separation is witnessed by one
   common perpendicular coordinate frame. If neither coordinate
   direction contains a four-square projection-separated chain,
   nine squares force a 3×3 rank grid, excluded at q≤q* by
   the four-corner stress. Thus a four-chain is structurally forced
   throughout this broad separability class.
3. [GRID_FOUR_CORNER_STRESS.md](GRID_FOUR_CORNER_STRESS.md):
   four **independently oriented** outer corner squares, with
   one-square reserves in both horizontal spans and both
   vertical spans, force squared radius q≥9/2. The proof is
   four tangent vectors and one exact orientation factorization.
4. [FOUR_ANCHOR_STRESS.md](FOUR_ANCHOR_STRESS.md): the strongest
   geometric terminal certificate so far. **Only four arbitrary
   rotated squares** are needed: one pair has projected horizontal
   center span at least \(2+h_L+h_R\), another has span at least
   \(1+h_L+h_R\), and the first pair lies completely above the
   second. The two-tangent hand proof forces \(q\ge q_*\) and pins
   all four extremal squares at equality.
5. [ORIENTATION_STABLE_SEVEN_ANCHOR.md](ORIENTATION_STABLE_SEVEN_ANCHOR.md):
   one-square orientation penalty; independently rotated
   projection-separated cap-row bound; 4-over-3 terminal obstruction,
   equality included. It is a concrete consequence of the
   four-anchor stress certificate.
6. [ROTATED_STRATIFIED_NINE.md](ROTATED_STRATIFIED_NINE.md):
   complete five-case structural proof for **all nine independently
   rotated squares** whenever they admit horizontally
   projection-separated layers and full vertical support separation.
   The equality layer sizes are \(3,4,2\) or \(2,4,3\).
7. [GLOBAL_TRIPLE_TRANSVERSAL.md](GLOBAL_TRIPLE_TRANSVERSAL.md):
   an unconditional G2 input: in *every* direction some
   perpendicular line meets the interiors of at least three
   squares. It does not yet force the four anchors.
8. [HAND_PROOF.md](HAND_PROOF.md): the initial exact 2–4–3
   construction, axis-aligned stratified proof and original
   seven-anchor argument. The newer rotated results supersede
   its *scope*, not its valid special-case arguments.
9. [NONRIGID_WITNESS.md](NONRIGID_WITNESS.md): exact
   Pythagorean-frame construction with one of the other two
   squares independently rotated. It disproves a proposed
   all-nine-aligned equality normal form.
10. [STRUCTURAL_NEGATIVE_TESTS.md](STRUCTURAL_NEGATIVE_TESTS.md):
   exact negative tests: no central open square in the record
   packing; general nonoverlapping parallel squares need not
   be layered in a fixed frame; true separating axes must be
   drawn from the actual square edge normals.

## New proof core — two tangent vectors, no case table

For a rotated unit square S, let \(h_S\ge1/2\) be its
equal horizontal and vertical projection halfwidth.
For any \(A\ge p\ge0\), define the support function
\(H_S(z)=\bigl(|u_S\cdot z|+|v_S\cdot z|\bigr)/2\).
The crucial exact identity/inequality is
\[
 (A+p)h_S+H_S((\pm A,p))\ge A+p.
\]
It is proved by **two sign cases** and \(a^2+b^2=1\),
not numeric bounds. With a square above floor \(y=s\),
the Euclidean tangent identity
\[
 2P\cdot v=\|P\|^2+\|v\|^2-\|v-P\|^2
\]
gives a sharp supporting-line estimate at
\(P=(\pm A,s+1)\).

Applying it to two widely separated endpoint squares
with long span parameter \(A=2\) yields
\(q\ge4+(s+1)^2\); applying its reflection to
the short-span pair with \(A=3/2\) yields
\(q\ge9/4+(1-s)^2\).
They intersect at \(s=-7/16\), giving \(q_*\).
At equality, the four endpoints align exactly
with the selected frame and are pinned.

## The precise remaining G2 target

**New finite reduction already proved:** with any common
coordinate-separating frame, all nine squares either have a
four-projection chain or the disk radius satisfies q≥9/2.
This eliminates the entire 3×3 rank-grid class at the proposed
sharp radius without a computational case classification.
But an arbitrary independent-orientation packing need not be
coordinate-separable in one common frame, and a four-chain by
itself is still insufficient for the long/short stress.

The desired unrestricted statement from the original
Packing predicate is:

> For *every* configuration of nine arbitrarily oriented
> unit squares in a disk of squared radius \(q\le q_*\),
> exhibit a frame and four squares satisfying the three
> inequalities of FOUR_ANCHOR_STRESS.md, **or**
> prove that the configuration enters a finite collection
> of explicitly defined alternative geometric patterns,
> each with a separate analytic sharp obstruction.

Do not replace this by a claim of global stratifiability,
the existence of a square containing the disk center,
or seven parallel squares: those are stronger unjustified
hypotheses, and some fail for known exact examples.

Use the three exhaustive origin-incidence branches of
DEEP_GATED_ROADMAP.md/G2.P: interior of a square; boundary but no
interior; outside all closed squares. The equality record
is in the **boundary** branch, not in the interior branch.

No numerical search can discharge the quantified
extraction step by itself. Computer assistance is
appropriate to falsify candidate finite patterns and
discover geometric invariants; the final gate must be
a human-checkable proof.

## Next concrete task

**Coordinate branch:** close G2.C3.3.b–c (equivalently
G2.C4.3c.3) with a whole-class **sharp** frame-switch or alternate
stress covering both `(4,1)` and `(3,2)` vertical-stack complements.
Do not re-prove their finished two-stack classification, and do not
exclude the whole `(3,2)` class: the exact q=Q witness realizes it.

**Unrestricted branch:** close G2.O3's human-sized exhaustive
geometric SAT separator-graph classification and G2.O4's
orientation-uniform stress certificate, then G2.O5/G2.X.
A common orthogonal separating frame is false even at equality.

Only then complete G4 unrestricted optimality, G5 unrestricted
equality, G6 independent audit, and G7–G8 Lean/registry integration.
Keep exact counterexamples and do not proliferate arbitrary
small-angle or height-window subcases.

**Verification scope:** mathematical hand proofs and small
exploratory numerical checks, without an independent
complete manuscript audit and without Lean elaboration.
