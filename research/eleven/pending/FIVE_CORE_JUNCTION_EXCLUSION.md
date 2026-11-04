# A five-body retained stress core has a planar physical contact graph

Let a retained connected stress core contain exactly five unit squares, at
an eleven-square minimizer. The core's actual position has minimum enclosing
squared radius q, and the universal lower bound gives `q>9/2`.

No point can belong to four of these five squares. At a shared point, the
open local sector of a unit square has angle pi/2 at a corner and pi at a
side-interior point. A point in a square's interior cannot belong to another
square. Four squares therefore contribute sectors of angle at least pi/2;
disjoint interiors force every contribution to be exactly pi/2, with the
four sectors exhausting the turn. Their edge rays agree in consecutive
quarter turns. Since all side lengths are one, the four squares form an
exact 2 by 2 square block with the shared point at its center.

That block has a containing disk of radius sqrt(2). Connectedness forces the
fifth square to touch at least one member of the block; its circumdisk has
radius sqrt(2)/2 and intersects the block's containing disk at the shared
point. Two intersecting disks of radii r and s have a containing disk of
radius at most r+s. Indeed, if one contains the other the assertion is
immediate; otherwise their standard collinear enclosing disk has radius
`(distance_between_centers+r+s)/2<=r+s`.

Thus all five squares fit in a disk of radius `3sqrt(2)/2`, contrary to
their minimum-disk identity and `q>9/2`. This proves the junction exclusion.

The full physical body contact graph of these five squares is consequently
planar. Here is the required drawing argument, including degeneracies.
Use each square center as a graph vertex. For a pair meeting along a
nondegenerate segment, choose a point in its relative interior; no third
square can share an interior subsegment, since its local interior half-plane
would overlap one of the first two. For point contacts use the shared point.
Draw spokes through each square's open interior from its center to the
chosen contact points. Spokes in different squares cannot cross. Within
one square, distinct spokes meet only at its center, except for spokes
headed to the same multiple junction.

Choose disjoint small neighborhoods around the finitely many multiple
junctions. At a two-body junction join the two spokes. At a three-body
junction the three pair connections form a subgraph of a triangle and can
be routed without crossings in their cyclic sector order. Separate coincident
spoke endpoints locally. No four-body junction remains, so no crossing is
needed anywhere. Convexity makes each pair's contact set connected, and one
graph edge is used for that pair, so the graph is simple.

The planar graph bound gives at most `3*5-6=9` physical contacts among the
five core bodies. Every omitted body and all its original nonoverlap
constraints remain part of the eleven-square completion. This is a
restriction on five-body core signatures, not an exclusion of every
five-body core or a sharp global radius proof.
