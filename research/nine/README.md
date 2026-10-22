# Nine unit squares in a circle — research index and handoff

**Research branch:** research/nine-tablefree-hand, draft PR #11.
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

## Latest subgate closure: global-frame obstruction and four-chain shadow

- **[G2_SUBGATES.md](G2_SUBGATES.md)** is the detailed finite
  branch ledger. The remaining core is G2.C4.2/C4.3
  (large-zigzag versus coherent side of a four-chain) and
  G2.O2/O3 (unrestricted oblique-separator normalization).
- **[NO_GLOBAL_ORTHOGONAL_FRAME.md](NO_GLOBAL_ORTHOGONAL_FRAME.md)**
  constructs nine exact unit squares at q=1105/256 with seven
  rigid anchors and two freely rotated top squares. The pair
  requires an oblique separator, while an adjacent touching
  anchor pair forces any common separating frame to be aligned.
  Hence *no* common perpendicular coordinate frame can
  separate all pairs. The rank-grid theorem cannot be
  promoted to unrestricted G2 by assuming global coordinates.
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

1. [ROADMAP.md](ROADMAP.md): G0–G8 gated roadmap, complete dependency
   and closure criteria. G1 is closed by a hand proof, G2 remains
   the dominant open geometric normalization task; G3's stratified
   branch is closed but nonstratified branches are not.
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
ROADMAP.md/G2: interior of a square; boundary but no
interior; outside all closed squares. The equality record
is in the **boundary** branch, not in the interior branch.

No numerical search can discharge the quantified
extraction step by itself. Computer assistance is
appropriate to falsify candidate finite patterns and
discover geometric invariants; the final gate must be
a human-checkable proof.

## Next concrete task

First complete the **coordinate-separable four-chain** branch:
from the chain forced by ORTHOGONAL_RANK_DICHOTOMY.md and the
five remaining squares, derive the long/short four-anchor
certificate or a small number of exact new terminal patterns.
Second handle the **oblique-separator branch**, in which no
single perpendicular frame separates all square pairs; a
coordinate rank injection cannot be used there.

Attack the **four-anchor extraction** under the central-seam
case G2.2, not the more demanding extraction of seven
common-frame anchors. The inner squares can be used only
to certify the two horizontal spans, and need not be
classified individually if a global combinatorial/geometric
span lemma can establish those inequalities.

Parallel tracks: the central-open-square branch G2.1
and the fully exterior branch G2.3 may require
different angular/dual-support obstructions.
Record exact counterexamples if a proposed global
normalization is false, rather than growing thousands
of rational cases.

**Verification scope:** mathematical hand proofs and small
exploratory numerical checks, without an independent
complete manuscript audit and without Lean elaboration.
