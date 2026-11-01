# Independent review: four-cycle available area and the literal prism exclusion

Date: November 1, 2026 UTC. Reviewer: four_chain continuation.

**Decision: PASS the complete four-cycle theorem and the degree-independent
literal triangular-prism exclusion.**

The frozen target is
`FOUR_CONTACT_CYCLE_ENCLOSES_AT_MOST_ONE_UNIT_AND_NO_POSITIVE_TRIANGULAR_PRISM_2026_11_01.md`,
SHA-256 `b573067a430d8508892632043864149c52aaed2a6e86c4a8e877b60b0e209c97`.
I read its whole body and independently checked all area, equality,
winding, inner-core, junction and restricted-graph steps.

I also read the entire current `NO_POSITIVE_K4_SUBGRAPH.md` directly at
`cb411042ad89d55d2f4c8d6e24682cec34677c89`, Git blob
`0a3e81e1e941af7cbeb5d5176a8108ed9a3f5ff1`. Its Sections 1--2 provide
exactly the stated arbitrarily small edge homotopies, fixed centers and
simultaneous empty-three-cycle property. Their compatible physical
selection premise is retained; the target does not assert planarity
of the complete physical touching graph or change a force certificate.

## 1. Available area is strictly less than two

The four original contact segments each lie in one actual unit square
and have length at most sqrt(2). The two triangles across p_1p_3 each
have area at most one by their two consecutive leg bounds, whether the
contact walk crosses itself or has degenerate or repeated points.
Thus their union V has area at most two.

If the union area equals two, both individual areas equal one and
their interiors are disjoint. The two legs at each of p_2,p_4 have
length sqrt(2) and are perpendicular. Their common hypotenuse therefore
has length two. For this fixed hypotenuse the right-isosceles third
vertex has only the two opposite-side choices. Disjoint interiors
force different choices, so V is a square of side sqrt(2).

Every cycle contact segment now joins opposite vertices of its own
unit square. Its midpoint is that actual square's center and lies
strictly inside the square. A small disk there intersects the interior
of V in a nonempty open half-disk. Thus a positive area of V is already
occupied by a cycle-square interior. In both the strict and equality
branches, the available area after removing those four interiors is
strictly below two. No uniform numerical reserve across packings is
needed or asserted.

## 2. Winding is valid for every contact walk

As oriented chains, the quadrilateral is the sum of the two triangle
boundaries because the diagonal traversals cancel. Winding is additive
at every point off those finitely many segments. Outside their closed
union V both triangle windings vanish, hence so does the quadrilateral
winding. This proves the required containment of any nonzero-winding
region without assuming the straight contact walk is Jordan. Repeated
contacts, crossing segments and endpoint means cause no gap.

## 3. The small physical embedding has the claimed simultaneous property

For each fixed original cycle, its strict available area a < 2 permits
a delta in (0,1/2) with 2(1-2delta)^2 > a. Every other unit's concentric
delta inner square is at distance at least delta from every cycle
square: a different actual closed square cannot meet its open interior.
Consequently an embedding and all its accepted individual edge
homotopies inside the epsilon-neighborhood of cycle squares, with
epsilon < delta, avoid these inner squares. The fact that edge
homotopies may cross each other is irrelevant to winding about the
avoided inner squares.

If two other centers were enclosed, each connected inner square would
lie wholly on the bounded side of the embedded Jordan cycle. Its winding
is nonzero there. Homotoping each original edge back to its physical
strand, and then replacing each two-half-strand passage inside its
convex square by the actual contact segment, preserves this winding.
Both entire inner squares therefore lie in V and avoid every cycle
square interior. Their disjoint interiors have total area exactly
2(1-2delta)^2 > a, contradiction. In fact the final contact segments
also avoid those inner squares; the manuscript's measure-zero boundary
qualification is harmless.

The fixed original graph has finitely many four-cycles. Choosing the
one epsilon below all their individual deltas and below 1/80 gives
one physical plane embedding with all asserted four-cycle and existing
three-cycle properties simultaneously. This is an auxiliary drawing
choice for unchanged actual squares and forces. No varying packing,
certificate limit or unsupported junction perturbation is used.

## 4. The entire literal prism caller

The restricted prism graph is biconnected by the printed vertex-deletion
argument, so its face boundaries are simple cycles. Its only triangles
are the two displayed disjoint ones. The empty-three-cycle theorem
makes each an empty bounded face. An edge cannot enter the bounded
side and then leave without either crossing the cycle or returning
through a forbidden repeated edge point; there is no interior vertex
or additional triangle chord in this simple prism subgraph.

Euler gives five faces. The other three have lengths at least four,
and the sum of all face boundary lengths is 2*9 = 18. Therefore their
lengths are exactly four. In particular the unbounded-face boundary is
a four-cycle. The other two of the six distinct vertices lie strictly
inside that Jordan boundary, contradicting the simultaneous four-cycle
property. Original extra positive edges and additional body centers
cannot weaken this contradiction; the one embedding was merely
restricted, not replaced by an arbitrary abstract drawing.

## 5. Scope and verification

The source excludes every literal positive triangular prism at the
existing compatible selected-embedding scope, at arbitrary radius,
degrees and loads. It does not exclude a subdivided prism automatically,
assume all graphs outerplanar, or assert that four-cycles enclose no
single body. A graph-classification caller is still needed where no
literal prism has yet been proved.

All new arguments and this review are hand proofs. Document hashing
was used solely for identity. No mathematical script, geometric sample,
graph enumeration, Lean, build, CI, frozen-source edit, ledger change
or remote mutation was performed.
