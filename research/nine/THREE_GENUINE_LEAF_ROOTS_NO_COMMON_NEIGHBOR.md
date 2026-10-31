# Three genuine leaf roots cannot have a common physical neighbor in a nine-square packing

Date: October 27, 2026.

**Status: accepted complete uniform physical capacity theorem and eight
whole original graph-domain consequences after full root and separate
independent reviews.** See
REVIEW_THREE_GENUINE_LEAF_ROOTS_NO_COMMON_NEIGHBOR_ROOT_2026_10_27.md and
REVIEW_THREE_GENUINE_LEAF_ROOTS_NO_COMMON_NEIGHBOR_MIXED_BLOCKS_2026_10_27.md.
Their mathematical source pins precede this acceptance-only header.
No original gate, coarse-cell count or shared ledger changes here.

Keep the same nine original physical units in the original radius window,
with their common compatible selected certificate. Put

    d=sqrt(R^2-1/4)-1,
    epsilon=max(d-1,0)<1/60.

Let C_1,C_2,C_3 be three distinct actual roots, each of positive degree
at least two and each with a genuine degree-one leaf. Let H be a fourth
distinct actual unit which physically touches each C_i. The physical
contacts with H need not carry positive stress.

**Theorem.** This entire original configuration is impossible.

H and all three roots retain arbitrary actual degrees, forces, frames,
circle masks, individual weights and means. The proof draws an auxiliary
topological graph to count occupied area. It does not introduce a new
force graph, change a physical contact or discard any original unit.

## 1. The whole leaf/radius cover and the small disk

The complete reduction THREE_GENUINE_LEAF_ROOTS_HIGH_S_REDUCTION.md
already excludes every D assignment and every d<=1 alternative for
these three actual roots, at their arbitrary higher degrees. Its
critical capacity argument retains all nine original squares.
Thus only

    d=1+epsilon>1, 0<epsilon<1/60,
    all three genuine leaves are S                     (1)

can remain. Each actual C_i meets the closed disk

    D={x:|x|<=epsilon}                                  (2)

at its original inward-unit-segment point epsilon e_i. Each root
also has its actual radial outward support d e_i.

If H meets D too, the four distinct actual units meet D_(1/60).
FOUR_NEAR_ORIGIN_UNITS_NINE_CAPACITY_EXCLUSION.md gives total
capacity at most eight. Hence it remains only to exclude

    H intersect D is empty.                            (3)

The compact sets in (3) have positive separation. The next step
uses the actual S-root geometry to justify a disk contraction;
mere proximity of arbitrary squares would not suffice.

## 2. A genuine high S root cannot have two adjacent shallow origin sides

Let C be an actual S root in (1). It cannot have the own-frame chart

    C=[-a,1-a] times [-b,1-b],
    0<a,b<=epsilon.                                    (4)

Indeed every radial support of C is either the perpendicular foot
on an own side or a vertex. The four positive side distances in
(4) are a,b,1-a,1-b, all less than d>1. The near vertex has norm
at most sqrt(2)epsilon<d. Each of the two adjacent vertices has
squared norm at most 1+epsilon^2<d^2.

The remaining far vertex has squared norm at least

    2(1-epsilon)^2 > (1+epsilon)^2=d^2,

because their difference is 1-6epsilon+epsilon^2>9/10.
No vertex has norm d either. These are all possible physical
support features for its genuine radial point d e_i. Thus (4)
is impossible, including the equality a=epsilon or b=epsilon.

This step is specific to the genuine S support. For arbitrary
near squares a disk can cut off a small corner, and that case
must not be assumed connected without this argument.

## 3. The clipped interior of every root is connected

For each actual C_i define the open region

    Omega_i=int(C_i) minus D.

It is nonempty. We prove it is path connected, retaining exact
disk tangencies.

First D cannot meet two opposite sides of a unit square, because
its diameter 2epsilon is less than one. It therefore meets at
most two adjacent sides. Its intersection with any one side is
an interval, a singleton, or empty.

If D met two adjacent sides but their common vertex v were
outside D, choose coordinates with v=(0,0) and the square
[0,1]^2. Write the original disk center in these coordinates
as (a,b). The actual intersections with x=0 and y=0 give
|a|,|b|<=epsilon.

Both a and b must be positive. For example, if a<=0, every
point (x,0) of the bottom side with x>=0 would have squared
distance (x-a)^2+b^2>=a^2+b^2>epsilon^2 from the disk center,
contradicting its disk intersection. The other coordinate is
identical. Thus 0<a,b<=epsilon, and translating the original
origin back to zero gives precisely the impossible chart (4).

Consequently the intersection D with the boundary of C_i is
empty or one connected boundary arc, allowing a singleton.
If two adjacent sides are met, their common vertex is in D,
so their two intersection intervals meet at that vertex. The
complementary boundary part outside D is path connected.

Here is an explicit interior connection argument. For any
x in Omega_i, continue its radial ray away from O until it
reaches the boundary of C_i. By convexity it stays in C_i,
and its norm only increases, so it stays outside D. Its
boundary endpoint lies in the connected boundary complement.
For two such endpoints, the compact boundary arc joining them
outside D has positive distance from D. Move that finite arc
slightly into the square, and shorten the two radial segments
accordingly. This gives a path wholly in Omega_i. The same
argument applies when D is strictly inside C_i: the full square
boundary is then available. The rays never start at O, because
their starting norms exceed epsilon.

Thus every Omega_i is a connected open physical region. It is
the interior of the unit with only the small central disk
removed; no assertion that arbitrary disk-clipped squares are
connected is used.

## 4. Each root retains a large rectangle outside the disk

For each i choose j!=i and an actual point z_j in C_j intersect D.
It cannot lie in int C_i, by the original physical nonoverlap.
Therefore one actual outward own-axis side of C_i, with unit
normal n_i and height h_i, satisfies

    h_i<=n_i.z_j<=epsilon.

The whole unit's projection interval in this axis is
[h_i-1,h_i]. Trim a strip of width 2epsilon from this one side.
The remaining closed rectangle has side lengths 1-2epsilon
and one, and every one of its points satisfies

    n_i.x<=h_i-2epsilon<=-epsilon.

For a sufficiently small eta>0, inset this rectangle by eta
from each of its four sides. Denote the resulting compact
rectangle by R_i. It is wholly in int C_i and outside D, with
strict positive clearance from D, and

    area(R_i)=(1-2epsilon-2eta)(1-2eta).

Because 1-2epsilon>29/30, eta can be chosen sufficiently small
that all three actual rectangles satisfy

    area(R_i)>29/30.                                   (5)

The same eta works for all three, since there are only three.
Each R_i also has positive distance from every other closed
actual unit. We will keep these entire large rectangles fixed
through the auxiliary drawing and its homotopies.

## 5. A physical theta graph has one root inside the other two paths

Use one auxiliary vertex in the interior of each R_i, one in
int H, and the original O as a vertex for D. Draw the three
paths

    D -- C_i -- H,       i=1,2,3.                       (6)

Each edge D--C_i uses a point q_i on the actual intersection
of C_i with the circle |x|=epsilon. Such a point exists: C_i
meets D and has points outside D, and it is convex. The part
from O to q_i lies in D. The rest runs inside Omega_i to its
chosen representative. The edge C_i--H uses an actual contact
p_i in C_i intersect H; by (3) this contact is outside D.
Its Ci-side path can be drawn in Omega_i, and its H-side path
in H. The path-connectivity proved in Section 3 is exactly
what permits the two paths at C_i to form one connected star.

These six edges admit a plane embedding in arbitrarily small
neighborhoods of the indicated physical paths. Within each
connected open region choose the two Ci half-edges as a simple
arc through its representative. Within the convex H and D,
choose their incident half-edges as stars with the actual port
order. Different regions have disjoint interiors. At a coincident
contact, all local edges are a star from just one of the two
hubs H or D to the incident Ci regions; H and D are disjoint
by (3). Such a star has noncrossing local routing. There are
no Ci--Cj edges or H--D edge imposing an interlacing matching.
This also covers singleton disk tangencies and shared physical
side endpoints.

Take the routing neighborhoods small enough that an edge not
incident to C_i avoids all of R_i. This is possible by the
positive clearances in Section 4. No physical stress or chosen
normal is involved in this auxiliary topological construction.

The resulting graph is K2,3, that is, three internally disjoint
two-edge paths between the two different hubs D,H. Its outer
face is bounded by two of the paths, and the third path's
internal vertex lies strictly inside that simple four-cycle.
Relabel so that the outer cycle uses C_1,C_3 and the enclosed
representative belongs to R_2.

The entire connected R_2 avoids that cycle. Hence it lies in
the cycle's bounded interior and has winding number one after
orienting the cycle appropriately. This statement concerns a
large rectangle in the actual C_2, rather than a point with
no controlled occupied area.

## 6. Contracting that cycle leaves too little enclosed area

Contract its Ci portions, for i=1,3, to their straight actual
contact segments [p_i,q_i] inside their convex original units.
Contract its H portion to [p_1,p_3] inside H, and its D portion
to [q_1,q_3] inside D. Every homotopy avoids R_2: the other
closed original units and D are disjoint from that rectangle.
The original embedding can first be taken sufficiently close
to its physical paths to make the same assertion before these
straight contractions.

The resulting polygonal loop is

    p_1 -- q_1 -- q_3 -- p_3 -- p_1.                  (7)

It has winding one about every point of R_2 and has the exact
side bounds

    |p_1-q_1|, |p_3-q_3|, |p_1-p_3| <= sqrt(2),
    |q_1-q_3| <= 2epsilon.                            (8)

Degenerate or self-intersecting endpoints cause no issue in
the area bound. Split (7) along [q_1,p_3] into its two triangle
loops. Winding is additive. Any point with nonzero winding in
(7) belongs to at least one of the two closed triangles, so
its winding-one region has area at most the sum of their areas.

The triangle p_1,p_3,q_1 has perimeter at most
3sqrt(2)+2epsilon, by (8) and the triangle inequality through
q_3. A triangle of perimeter P has area at most P^2/(12sqrt(3)):
Heron's formula and the arithmetic-geometric mean inequality
give this directly, with equality only at an equilateral triangle.
The triangle p_3,q_3,q_1 has area at most epsilon sqrt(2),
using its two sides from q_3. Therefore

    area(R_2)
      <= (3sqrt(2)+2epsilon)^2/(12sqrt(3))
           +epsilon sqrt(2)
      < (30/7+1/30)^2/(144/7)+1/42
       =120607/129600
       <29/30.                                        (9)

Here sqrt(2)<10/7, sqrt(3)>12/7, and epsilon<1/60.
The last exact reserve is

    29/30 - 120607/129600 = 4673/129600 > 0.

Equation (9) contradicts the retained rectangle area (5).
This excludes (3). The alternative H meeting D was already
excluded by the same-nine four-near capacity theorem in Section 1.
The complete common-neighbor theorem follows.

## 7. Eight complete C2.34.b3 graph-domain consequences

Use precisely the labels and actual graph roles of
TRIANGLE_FOUR_BLOCK_THREE_BRIDGES_COMPLETE_ATTACHMENT_REMAINDER.md.
Its remaining shared direct-leaf rows have three distinct genuine
roots, at their unchanged original degrees. Whenever all three
are physical neighbors of the same fourth unit, the theorem
applies with that actual common neighbor as H.

This excludes the following whole graph domains, with every
private four-block load mask, side mean, normal and circle mask:

| Shared four-block/root type | Whole original leaf-root multisets excluded |
| --- | --- |
| C4 | ABP and APQ |
| Diamond with H a hub | ABK, ABP, AKP and APQ |
| Diamond with H a page | ABP and APQ |

In ABP the real H touches the three genuine roots A,B,P by
its original triangle edges and four-block edge. In APQ its
neighbors A,P,Q are the three roots. In the hub diamond H
also touches K, so its genuine-root neighbor triples A,B,K
and A,K,P are present in ABK and AKP. All these are actual
positive contacts, although the uniform theorem needs only
physical contact. H is different from all three roots in
every displayed application.

No triangle-tip equation, root clearance, four-block terminal
equation, or full resultant is imported at a changed degree.
The whole original graph domains disappear by the physical
capacity theorem with all nine units retained.

After full root and separate independent acceptance, these eight
domains would reduce the earlier 25-domain necessary remainder
to 17: twelve shared domains and five disjoint domains. The
shared domains would be five direct-leaf rows plus the arm row
for C4, three direct-leaf rows plus the arm row for hub diamond,
and two direct-leaf rows for page diamond. The entire C2.34.b3
cell is not declared closed, and no central count is changed here.

The proof uses no numerical pose search, new scalar certificate,
physical motion, force deletion, mean replacement, normal reselection,
Lean compilation, CI run or remote action.
