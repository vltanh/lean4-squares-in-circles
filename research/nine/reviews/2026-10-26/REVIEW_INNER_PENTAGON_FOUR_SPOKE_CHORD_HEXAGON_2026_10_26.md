# Independent review: the complete four-spoke chorded interior pentagon

Date: October 26, 2026.
Reviewer: separate hexagon proof worker, at source snapshot
INNER_PENTAGON_FOUR_SPOKE_CHORD_EXCLUSION.md saved in this session.

**Verdict: accepted.** I checked the complete new geometric calculation,
the wheel-face join and both original graph/load domains against
SIX_BODY_INNER_PENTAGON_LOAD_COVER.md and the unchanged deep-roadmap IDs.
This is a review of the entire new proof, not only its numerical bounds.

## 1. Cross normalization and every inequality

The opposite-boundary-arm alternative is indeed impossible in the full
radius window. Equal right/left corner maxima give x=0. With y arbitrary,
their squared maximum is 9/4+(|y|+1/2)^2. Containment of the farther top
or bottom arm requires 1/4+(|y|+3/2)^2 no larger, hence 2|y|<=0.
Thus y=0 and R^2=5/2, excluded. Three boundary arms always include an
opposite pair, so exactly two boundary arms remain and they are adjacent.

For right/top boundary arms, right/left and top/bottom containment give
x,y>=0. Equality of the boundary maxima then gives x=y=t. The displayed
radius identity 2t^2+4t+5/2 is exact. Its values at 3/10 and 2/5 are
97/25 and 221/50, respectively; their stated reserves against the two
radius endpoints are 33/1600 and 663/6400. Thus 3/10<t<2/5 and
1/10<1/2-t<1/5, with strict inequalities throughout the original closed
radius window.

The additional square T touching both other arms has center coordinates
in [-w,w]^2, because projection overlap is necessary for each actual
contact. This does not assume the contacting point is their shared
vertex. Since w<1, the three cross squares occupy every point of this
box outside the open southwest quadrant. An actual center of T is an
interior point, and cannot belong to any of those closed squares.
Consequently both center coordinates are strictly negative and at least
-w. There is no unwarranted whole-square quadrant claim.

For an arbitrary unit orientation, the absolute offset coordinates of
each vertex are (w,d) in one of the two orders. The coordinate triangle
inequality therefore gives exactly (2w)^2+(w+d)^2 as a universal squared
norm upper bound about the cross corner. Expanding with
w=(cos(theta)+sin(theta))/2 and d=(cos(theta)-sin(theta))/2 gives
3/2+(1/2)cos(2theta)+sin(2theta), whose global maximum is
(3+sqrt(5))/2. The strict upper bound 11/4<25/9 is valid. Translation
back to the circle origin adds less than sqrt(2)/5<3/10, hence every
vertex has norm less than 59/30. The reserve 79/40-59/30=1/120 is exact.
Every corner is strictly inside D_R, proving physical circle-clearance.
All orientation endpoints and weak point/side tangencies remain covered.

## 2. Original embedding and equality theorem

The full prescribed embedding has outer pentagon012340 and H inside it.
The retained chord03 cuts this disk into the quadrilateral0123 side
and the triangular034 side. H cannot lie on the triangular034 side:
its actual edges H1 and H2 would have to cross03 to reach1,2. Thus H
is on the bounded side of the actual ring01230. This also verifies the
source's equivalent four-rim-wheel description without an assumed pose.

The degree-free four-ring equality theorem applies to the actual unit H
on that bounded side. Its winding/area proof covers actual shared means,
coincident-contact limits and any other forces at the ring vertices.
It forces the aligned cross used above. No circle-load assumption from
its later three-boundary corollary and no pendant-leaf premise is used.

## 3. Full load join and exact gate consequence

The original graph has spokes H0,H1,H2,H3 and chord03. Its true degree-3
vertices1 and2 are forced loaded by the neighbor-path obstruction. The
true degree-2 vertex4 is forced loaded because0 and3 touch through the
actual retained chord. The cover's two complete load representatives are
124 and0124. Both have the adjacent boundary arms1,2 in the cross.
The original square4 physically touches the other arms0,3, so the new
cross lemma makes it physically circle-clear, contradicting its forced
positive circle load. The optional0 load is not required; its presence
would independently introduce an impossible opposite boundary arm pair.

The complete proof therefore covers all original graph-preserving
reflections, physical masks, individual zero corner weights, actual
contact means and the three arbitrary other packing squares. It changes
no force, angle, mean or body. The exact original IDs justified are
M6.B6.PENTAGON.H4_D1.L124, M6.B6.PENTAGON.H4_D1.L0124, and their complete
graph parent M6.B6.PENTAGON.H4_D1_EXIT. The other four interior-pentagon
graph types, their common parent and C1.6.b0 remain outside the result.

No sampled pose or finite arithmetic packet is used in the new proof.
No Lean compilation or CI was run for this review.
