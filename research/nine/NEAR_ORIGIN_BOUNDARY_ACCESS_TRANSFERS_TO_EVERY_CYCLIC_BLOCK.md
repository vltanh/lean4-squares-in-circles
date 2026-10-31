# Near-origin exterior boundary access forces every separate cyclic block near the origin

Date: October 28, 2026. Author: two_blocks.

**Status: complete proposed uniform theorem, frozen for full root and
separate independent review. No original coarse or fine count changes.**

Retain all nine actual interior-disjoint closed unit squares, the
original containing circle, and one compatible selected physical
positive graph in the full window

    79/40 <= R <= sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1 <61/60,
    epsilon=max(d-1,0)<1/60.

All original degrees, positive magnitudes, selected common normals,
actual common applications, side means, circle masks and individual
zero weights are retained. Physical contacts and completion squares
outside the positive graph remain occupied.

## 1. The uniform boundary-access theorem

Let Q be a maximal cyclic block of the original positive graph.
Let E be an actual unit outside Q with an original positive path to
a physical boundary unit T, every vertex of that path lying outside
Q. Suppose

    E meets the closed disk D_epsilon.

Then **at least one actual unit of Q meets closed D_epsilon**.
E need not contain O, even as a boundary point. The path may have
any length and T need not be a genuine leaf.

Assume to the contrary that every Q unit avoids closed D_epsilon.
We first reconstruct the complete block argument, and then give the
near-point transfer with all closed endpoints.

### 1.1. Every actual Q edge has nonzero origin moment

Suppose a Q edge had radial common application. Its application
cannot be O, since both incident units avoid D_epsilon. Choose the
radial direction e and its inner endpoint U so that

    p=t e, t>0,
    e.x<=t on U, e.x>=t on its actual neighbor V.

The contained-neighbor support bound gives t<=d. In an own interval
of U missing zero, reflect the coordinate to write [a,a+1], a>0.
The corresponding coordinate of p is positive, as is the component
of e=p/t. Since p is a maximum-e support of U, that coordinate
equals a+1. Thus t>1 and a<=t-1<=epsilon. If both own intervals
missed zero, the two absolute coordinates of p would exceed one,
giving t>sqrt(2)>d. Otherwise the other interval contains zero,
and the actual point (a,0) of U lies in closed D_epsilon. Both
alternatives contradict the assumed avoidance. This includes every
radial side mean and its endpoints.

### 1.2. Full block torques give a directed positive-moment cycle

Every connected component outside a maximal cyclic block attaches
to that block at at most one vertex. Otherwise its joining path
would belong to the same biconnected block. Sum the unchanged origin
torque equations in each such outside component. Every internal
pair cancels at its original common point and every circle atom has
zero origin torque. The total outside moment delivered at its sole
Q attachment is therefore zero.

Subtracting these complete zero contributions from each actual Q
vertex equation leaves a circulation of the original Q edge moments.
They are all nonzero by Section 1.1. Direct each Q edge in its
positive-moment direction and retain its positive moment magnitude.
At every vertex the incoming and outgoing sums agree. Following
directed edges and taking a first repeated vertex produces a directed
simple cycle C of length at least three.

The full degree-free port theorem in Sections 1--3 of
`GLOBAL_NEXT_DEGREE_FREE_MOMENT_PORT_ORDER_AND_INTACT_BLOCK_EXCLUSION.md`
applies: every C body and both its actual cycle neighbors avoid
closed D_epsilon, and its incoming and outgoing original moments
have opposite strict signs at that body. Its proof retains all
feature owners, side means, near-vertex equalities and arbitrary
true degrees. It makes the physical cycle wind positively about O.
In a sufficiently close compatible physical embedding, C is a
simple Jordan cycle with the same winding.

No body has been assigned a degree-two equation. The outside-cut
calculation used the entire original star at every attachment.

### 1.3. The whole connected disk lies on the same winding side

Let K be the union of the actual closed C units. K and closed
D_epsilon are disjoint compact sets. They have positive distance.
Choose the compatible routing neighborhoods smaller than this
distance, as well as the positive O clearance used in Section 1.2.
The resulting embedded Jordan cycle is disjoint from the whole
closed disk D_epsilon.

The disk is connected and contains O. Winding number is constant
on a connected set in the complement of the curve. Consequently
every point of closed D_epsilon has the same positive winding as
O, including all points on its boundary. When epsilon=0 the disk
is the singleton {O}, and this statement remains literal.

Choose an actual p in E intersect D_epsilon. It follows that p
lies strictly inside the embedded cycle. The point p may lie on
a side or a vertex of E. Every point of the half-open segment
(p,c_E] lies in int E, by convexity and the fact that c_E is an
interior point of the actual square. Such points are disjoint from
every closed C unit: a closed point of another full-dimensional
unit in int E would force overlap of open interiors. The endpoint
p is disjoint from all C units by their disk avoidance.

Thus the whole compact segment [p,c_E] is disjoint from K and has
positive clearance from it. Choose the same finite routing
neighborhoods also smaller than this clearance. The segment then
misses the embedded cycle, so c_E lies in its interior. This treats
epsilon=0 and all E-boundary choices of p without any assertion that
E contains O.

The actual original positive path from E to T has no C vertex.
In the one compatible physical embedding it cannot cross the
embedded C. It puts the boundary vertex T on the same interior
side as E. This contradicts the protected unbounded-face access
of every physical boundary vertex. The contradiction proves the
theorem.

## 2. Every cyclic block avoiding a genuine leaf root has a near unit

Let E have a genuine positive leaf L. The exact radial-leaf theorem
shows that E meets closed D_epsilon. For a genuine D leaf the root
contains O in its open interior. For a genuine S leaf the actual
contact is p=d e, and the complete inward unit segment

    p-[0,1]e is a subset of E

contains O if d<=1 and contains epsilon e if d>1.

Now take any maximal cyclic block Q avoiding E. A genuine degree-one
leaf L cannot belong to a cyclic block, so the original edge E--L
is a positive path entirely outside Q to the actual boundary unit L.
Section 1 therefore gives

    some actual Q unit meets closed D_epsilon.

This conclusion is uniform in the block size, chord set, articulation
degree, load mask and number of other branches. It uses neither
origin containment by an S root nor disk avoidance by an entire
block as an unproved premise.

Every unit meeting closed D_epsilon is physically circle-clear:
from an actual point x of norm at most epsilon, each other point
of the same unit has norm at most epsilon+sqrt(2), and

    epsilon+sqrt(2)<1/60+17/12=43/30<79/40<=R.

Thus the corollary forces an actual clear body in each such block.
It does not identify that body's true positive degree or shorten
any of its equations.

## 3. Exact operative inputs and scope

| Source | SHA256 | Operative scope |
| --- | --- | --- |
| GLOBAL_NEXT_DEGREE_FREE_MOMENT_PORT_ORDER_AND_INTACT_BLOCK_EXCLUSION.md | 8def789e0cde632795f81d8ecf92d6dd3642b37fd4ca6e79cc4890594264fd49 | Sections 1--3: actual contained-neighbor support bound, full port-order cover and directed-cycle winding; the full block-cut proof is reconstructed above. |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | One compatible physical embedding with arbitrarily small routing neighborhoods and protected exterior access of actual physical boundary vertices. |
| RADIAL_BRIDGE_AND_LEAF_REDUCTION.md | faf453b3c519b10590cf9d6f6dbf9282233bd2ff04c90aa0cd8cd89e060bc676 | Exact genuine S/D leaf/root forms and the full inward unit segment. |

This is a separate strengthening of the closed-origin boundary-path
argument. The previously frozen parallel-triangle source is unchanged.
No numerical pose, fixed mean, altered normal, force deletion, graph
table, Lean execution, compilation, CI, remote mutation or shared-ledger
edit is used. Original fine and coarse closure counts are unchanged.
