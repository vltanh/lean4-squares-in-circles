# Independent review: genuine D leaf excludes every enclosed four-ring and positive K2,3

Date: October 27, 2026.

Reviewer: mixed-blocks agent, independent of the source author.

Reviewed source: `TWO_LEAF_D_LEAF_ANYWHERE_FOUR_RING_AND_K23_EXCLUSION.md`.

Reviewed source SHA-256:
`b78e284ed41a8ecf8103cdd0f646f66dc46e823301d3d92ae11317eeb2cc6405`.

**Verdict: PASS for the complete stated theorem and its stated graph scope.**
This is a full-source and direct-dependency audit, not a numerical pose
check. No original ledger or checkbox is changed by this review.

## 1. Genuine leaf and unchanged physical scope

Theorem 6.1 and Corollary 6.2 of
`RADIAL_BRIDGE_AND_LEAF_REDUCTION.md` provide precisely the genuine D
leaf used in the proof: actual radial inner vertex `(R-sqrt(2))e`, true
degree one, and relative-side-interior contact on its actual root under
the existing compatible selection. The root interval is consequently
`[r-1,r]e+[a-1,a]Je`, with `0<a<1`; no root force is discarded. The
strict arithmetic bounds `1/2<r<2/3` and `1/3<1-r<1/2` are valid in
the original full radius window. Thus the origin belongs to the open
interior of this same root, regardless of its other actual forces.

The contained-center inequality `|c|<=d+1/2` is the force-free sharp
bound from `END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md`, Section 1.
The physical boundary/exterior and retained-cycle separation facts
are supplied by `PHYSICAL_BODY_GRAPH_UNCROSSING.md`. A genuine loaded
D leaf is an actual physical boundary body, not merely a formal force
atom.

## 2. Enclosed-ring equality and all origin positions

Section 2 of `SPANNING_K23_LEAF_BLOCK_EXCLUSION.md` is an unconditional
four-ring equality lemma: an enclosed actual unit forces the actual
aligned five-unit cross. Its proof does not require the later leaf-block
or boundary-count hypotheses. The new source explicitly uses only that
degree-free equality lemma.

The original containing-circle bound gives `0<=x,y<3/5` in the reflected
cross frame. The corner comparisons exclude `x>1/2,y>=1/2` and its
transpose. The remaining cases put the origin in the closed central
unit or the open left/bottom unit. This covers the equalities at `1/2`.
Every different closed unit containing the origin would overlap the
open origin-containing D root. Hence the D root is one of the actual
five cross units, with boundary-origin alternatives correctly excluded.

If that root is central, the true-degree-one D leaf cannot be a ring
unit, and its physical exterior position makes its original edge from
the enclosed root cross the retained positive Jordan cycle. This is a
valid same-embedding contradiction, with no suppression of forces.

## 3. The ring-root overlap is strict and exhaustive

If the D root is a ring member, the opposite actual ring center gives
`0<sigma<=d-1<1/60`. In particular `d>1` is derived, not added as a
hidden initial restriction. The true D radial side axis cannot be the
shallow axis because both its distances `r` and `1-r` exceed `1/3`.
After reflection the resulting root and D-diamond formulas are exact.

The displayed point `q=(-1/5,-r-3/10)` lies strictly inside the actual
lower cross unit: `0<sigma<1/60<1/5`, and its vertical displacement is
strictly between zero and one. Its D-diamond norm is
`1/sqrt(2)-1/10<1/sqrt(2)`, so it is strictly inside the D leaf as well.
These units are distinct because a ring member has two distinct
positive ring neighbors while the genuine leaf has true degree one.
The contradiction uses original physical interior disjointness and
therefore retains all zero-stress contacts and circle-mask endpoints.

## 4. Positive K2,3 and larger graph scope

In any plane embedding of the six positive K2,3 edges, the exterior
face boundary is a four-cycle through two pages, and the third page
center is enclosed. Restricting the drawing for this topological fact
does not assign reduced force degrees to its vertices. The genuine D
leaf remains in the full graph, so the four-ring theorem applies even
when that leaf and its root lie outside the five-vertex subgraph.

Each cited dense five-body type contains the actual spanning K2,3:
K2,3 itself, the three-page book, once-subdivided K4, and four-rim
wheel. The source correctly states the result only for a positive
subgraph, not an arbitrary minor, and makes no false implication for
C5, house, fan, or diamond without such a subgraph. Its warning that
a long arm's far root is not the adjacent D-leaf root is correct.

The theorem is accepted at its stated complete scope. No Lean build,
CI, numerical certification, new fine ID, or coarse-parent closure
is claimed by this audit.
