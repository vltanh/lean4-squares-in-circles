# Full independent review: origin routing among actual triangular blocks

Date: October 27, 2026.
Reviewer: rooted_blocks.

**Verdict: ACCEPT the complete stated theorem at the corrected scope.**

Reviewed source:
`GLOBAL_CLOSURE_RADIAL_TRIANGLE_BLOCK_ORIGIN_ROUTING.md`

Frozen SHA-256:
`9dc7c420a8c9900bf20119a6c47dd8c1f2d1e2e6755abe92e43a726152a4a100`.

I read the entire source, including all zero-moment, contact-polygon,
embedded-cycle, nested-block and boundary-origin cases. I checked the
full physical embedding construction in PHYSICAL_BODY_GRAPH_UNCROSSING.md,
the exact proper-port and noncollinearity inputs, and the complete
nonzero-moment contact-winding proof whose local scope is transferred.
This review concerns the new block routing and closed-origin assembly;
its imported local winding theorem already has a separate full audit.

## 1. Zero cycle moment and the exact local winding scope

At least two pairs are nonparallel by the genuine noncollinearity theorem.
At zero cycle moment their concurrence points are O, and their mutual
proper-port relations force the unchanged common application to be O.
Both actual closed units consequently contain O. There is no assertion
of positive radial concurrence at zero moment.

When all three actual closed units avoid O, the nonzero-moment proof
needs only this strict physical avoidance to construct its O-free convex
homotopies. Its outside origin-interior square was used later, for area,
not in the concurrence or winding steps. Thus the precise Section 2
scope transfer is valid, including the one-parallel-pair corrections and
all zero proper lengths. Center-to-port detours are homotopic to actual
contact chords inside their own O-free square.

## 2. Enclosure of another actual unit is impossible

The physical embedding uses local junction disks and thin center-to-port
tubes. They can simultaneously avoid the finite set of all nonincident
actual centers. Undoing those drawing changes preserves winding at a
chosen outside center. Contracting each square's detour to its contact
chord also avoids that center, since it belongs to the distinct unit's
open interior.

The whole open interior of that actual outside unit avoids the three
closed triangle units, so winding is constant on it. Nonzero winding
therefore puts area one inside the actual three-contact triangle. Its
three chord lengths are at most sqrt(2), giving area at most sqrt(3)/2.
Repeated or collinear contacts have zero winding and are covered before
the area comparison. No area of a perturbed graph drawing is substituted
for the actual geometric region.

## 3. The distinct-block nesting argument is complete

Two distinct graph blocks share at most one articulation. In the inherited
plane embedding their simple triangular cycles are disjoint or meet only
at that common actual center. The connected remainder of either Jordan
curve cannot cross the other; hence their bounded interiors are nested
or disjoint. Nonzero winding at O excludes the disjoint alternative.
An inner private center lies strictly inside the outer cycle and belongs
to a unit outside that triangle, giving the complete Section 2 area
contradiction. This remains valid when the two cycles are tangent at the
common articulation.

The corrected statement requires only the local drawing neighborhoods
used by the two chosen cycles to avoid O. Their actual closed units have
positive distance from O. An unrelated graph junction at O causes no
problem and is now explicitly retained. No unit or contact is moved.

## 4. A closed-origin outside unit suffices for the final propagation

If O is only a boundary point of E, the contact loop still avoids O and
has constant nonzero winding in a neighborhood of it. That neighborhood
contains points of int E because E is full-dimensional. Connectedness
then propagates the same winding throughout int E, again contradicting
its unit area. This covers a side origin and a vertex origin without
asserting that E contains O openly.

The theorem now states its full external-moment premise explicitly:
every triangular block is covered, as is any other positive triangle
whose three complete external moments separately vanish. A triangular
face in a diamond does not automatically acquire this premise. Original
branch moment sums retain all articulation circle forces and all other
positive pairs.

## 5. Changes requested and final scope

The audit requested only the two exposition/scope clarifications now
present in the pinned source: the zero-external-moment condition for a
nonblock triangle, and restricting O-free drawing neighborhoods to the
two chosen cycles. No mathematical change to the routing argument was
needed. Both corrections have been read back in the complete source.

The accepted result is closed-origin routing, not origin-interiority or
a whole graph exclusion. Its distinction between triangular blocks and
overlapping faces is preserved. No original fine ID, coarse row, force,
mean or selected normal is changed by this review.
