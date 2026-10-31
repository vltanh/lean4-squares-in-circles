# A tilted S-side-arm root cannot attach to any terminal biconnected block

Date: October 27, 2026.

**Status: accepted complete uniform hand implication after full root
and separate independent geometry, physical-embedding and scope reviews.**
See `REVIEW_S_SIDE_ARM_NEAR_VERTEX_BLOCK_ROOT_2026_10_27.md` and
`REVIEW_S_SIDE_ARM_NEAR_VERTEX_BLOCK_MIXED_BLOCKS_2026_10_27.md`.
No original gate or coarse-cell status is changed by this source.
The aligned root with an interior side application remains a separate
original obligation.

Keep all nine original interior-disjoint unit squares, the common
compatible selected physical certificate, every real normal, force,
circle mask, individual zero weight and actual shared-side mean in

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1,
    epsilon=max(d-1,0)<1/60,
    M=91/60.

Every contained unit center has norm strictly below M. This follows
from the usual farthest-corner bound |c|^2+|c|+1/2<=R^2 and the
strict reserve M^2+M+1/2-1105/256=31/57600.

## 1. A sharp physical corner-reach lemma

Let the reference unit be Q=[0,1]^2. Let T be any other physical
unit with disjoint open interior. Suppose T has some point with
x>=1 and some point with y>=1; these need not be the same point.
Then its center C satisfies

    |C|^2>=5/2.                                        (1)

This is a radius-free statement about the unchanged two squares.

Write C=(X,Y). A unit square has the same support halfwidth in
the two reference coordinate directions:

    w=(|cos t|+|sin t|)/2,       1/2<=w<=1/sqrt(2).

The two reach assumptions therefore give

    X,Y>=L:=1-w>1/4.                                  (2)

The ordinary separating-axis theorem for two rectangles gives a
separating direction owned by Q or by T. This auxiliary physical
axis is not substituted for any selected force normal.

### 1.1. A reference-owned separator

A negative reference coordinate axis would put X<=-w or Y<=-w,
contrary to (2). A positive axis instead gives X>=1+w or Y>=1+w.
Using (2) in the other coordinate yields

    |C|^2>=(1+w)^2+(1-w)^2=2+2w^2>=5/2.

### 1.2. A T-owned separator with two nonnegative components

Write this unit normal as n=(c,s), with c,s>=0 and c^2+s^2=1.
Exchange the two reference coordinates so c>=s. Here
w=(c+s)/2. The true separating support inequality is

    cX+sY>=c+s+1/2=:A.                                 (3)

If c+s>=11/10, Cauchy gives |C|^2>=A^2>=64/25>5/2.

Otherwise c+s<11/10. Since c>=1/sqrt(2)>7/10 and
2cs=(c+s)^2-1<21/100, we have s<3/20. Consequently

    A s<6/25<9/20<L.

The orthogonal projection of zero on the boundary of (3) has
Y-coordinate As below the permitted Y interval. The squared
distance minimum over (2)--(3) is therefore attained with Y=L
and X=(A-sL)/c. For an explicit verification, while (3) is active
the derivative of [(A-sY)/c]^2+Y^2 is
2(Y-As)/c^2>0 for Y>=L. If the constraint X>=L becomes active,
L^2+Y^2 remains increasing. The candidate at Y=L has X>1>=L.

At this minimum,

    X=1+(1/2+s w)/c>=3/2+s/2,
    Y=L>=1/2-s/2.

Both lower bounds are nonnegative. Hence

    |C|^2>=(3/2+s/2)^2+(1/2-s/2)^2
            =5/2+s+s^2/2>=5/2.

### 1.3. A T-owned separator with opposite component signs

After exchanging the coordinates if needed, write n=(c,-s),
c>0, s>=0, c^2+s^2=1. The case c=0 would put a positive
coordinate in a negative half-plane and is impossible by (2).
The exact separating inequality now is

    cX-sY>=c+1/2,
    X>=1+(1/2+sY)/c.                                  (4)

The smallest squared norm allowed by (2),(4) occurs at Y=L.
If s>=1/2, then L>1/4 and c<=sqrt(3)/2<7/8, so

    X>1+(5/8)/(7/8)=12/7,
    |C|^2>144/49>5/2.

If 0<=s<=1/2, use c<=1 and L>=1/2-s/2. These give

    X>=3/2+s/2-s^2/2,
    Y>=1/2-s/2,

and therefore

    |C|^2>=5/2+s-s^2-s^3/2+s^4/4
            >=5/2+(3/8)s>=5/2.

The second inequality uses 1-s-s^2/2>=3/8 on [0,1/2].
An owned separator with two negative components is impossible:
its dot product with (2) is negative whereas separation from
Q would require it to be at least 1/2. All separating-axis
orientations and touching equalities are now covered, proving (1).

For comparison, (1) is sharp for an adjacent aligned unit such as
[1,2] times [0,1]. The proof makes no assumption that T contains
the far vertex (1,1). In that special case there is an even shorter
check: |C-(1/2,1/2)|^2>=1 and |C-(1,1)|^2<=1/2 imply
|C|^2>=5/2 directly.

## 2. A near vertex gives a genuinely empty opposite quadrant

Let an actual contained root H have a vertex p with |p|<=epsilon.
Use its two original inward orthonormal side axes u,v at that vertex:

    H=p+[0,1]u+[0,1]v,
    F=p+u+v.

No other actual physical unit can meet both of the two closed
far half-planes

    u.(x-p)>=1,       v.(x-p)>=1.                       (5)

Indeed Section 1, applied after this rigid coordinate change, would
give |c_T-p|>=sqrt(5/2), whereas the unchanged containing circle gives

    |c_T-p|<=|c_T|+|p|<M+epsilon<23/15<sqrt(5/2).

The last squared reserve is exactly 67/450. In particular no other
physical unit contains F, and no point of any other unit belongs
to the closed far quadrant where both inequalities (5) hold.

The entire actual ray

    F+t(u+v),       t>=0,                              (6)

therefore avoids all other closed units and leaves H immediately.
It reaches the containing circle and then infinity without meeting
an occupied square. This is a real free route, not an inference
from a force-line concurrence. Since F has a positive distance
from every other closed unit, sufficiently small compatible
physical routing preserves this exterior access.

## 3. The actual S-side arm and its nonparallel root

Suppose the selected component consists of an actual biconnected
cyclic block rooted at H and the one genuine pendant path

    H-T-L.

L is a genuine S leaf. T has its exact original unloaded degree
two and actual side-normal width one. There are no further
positive forces outside the block at H. The block may have any
original true private degrees, loads or chords; nothing is
deleted or turned into a smaller rooted graph.

Rotate the original genuine leaf direction to a unit vector e.
The true radial arm equations give its unchanged root application
and support

    p=(d-1)e,
    H subset {x:e.x<=d-1},
    T is aligned with e,
    full transmitted H force is lambda e, lambda>0.     (7)

Assume H is not parallel to T. Then p is H's actual strict
maximum-e vertex. The actual positive H-T normal is T's side
axis e. At a singleton vertex/vertex contact that side-axis
normal is forbidden by the original compatible strict point
convention. Thus the unchanged p lies in the relative interior
of T's minimum-e side.

At p, T occupies its full inward half-plane locally. H occupies
a right-angle sector strictly inside the opposite half-plane,
since its maximum-e vertex is strict. The two remaining local
sectors each have angle strictly less than pi/2. A third unit
through p would require at least a right-angle inward sector.
It cannot fit. Hence

    no other actual physical unit contains p.          (8)

The arm-root point has |p|=|d-1|<31/60< R-sqrt(2), so H is
physically circle-clear by the boundary-point distance floor.
The nonzero full block force is consequently exactly -lambda e.

If d<1, then T itself contains O openly: its radial interval
[d-1,d] contains zero strictly and its transverse interval
contains zero strictly by the preceding side-interior conclusion.
The accepted universal occupied-origin terminal-four-block theorem
already excludes the original C4/diamond applications of this
source. The new geometric argument below treats d>=1; it does
not assert the same arbitrary-block low-radius conclusion.

For d>=1, p=epsilon e and |p|<=epsilon. In H's inward axes,
write

    e=-a u-b v,       a,b>0,       a^2+b^2=1.            (9)

Every hypothesis of Section 2 now holds at this unchanged H.

## 4. Two opposite root-corner sectors are on the same exterior face

Consider the original compatible physical plane embedding of just
the biconnected cyclic block. Its real incident edge ports on H
retain their cyclic boundary order; coincident ports retain their
actual tangent-sector order. These are the exact conventions of
`PHYSICAL_BODY_GRAPH_UNCROSSING.md`.

The p sector is exterior to this block. The actual positive bridge
H-T and its genuine continuation T-L give a physical path from
that sector to a circle boundary point of L, disjoint from the
block apart from H. Equivalently, a boundary leaf vertex cannot
lie inside a positive block cycle. Equation (8) gives a strict
gap between p and every actual block port, so no junction ordering
ambiguity occurs there.

The opposite vertex F has exterior access by the actual empty ray
(6). It too is strictly separated from every block port. Both
statements persist in one sufficiently close compatible routing
of the original embedding; no mean or selected normal changes.

In a plane biconnected graph, the unbounded face visits any vertex
at most once. In the physical unit representation, the exterior
sector at H is therefore one connected boundary arc between the
two outermost block ports; all actual internal block spokes lie
on its complementary occupied arc. This also holds for a simple
cycle, which has exactly two root spokes. Since the exterior arc
contains both p and F, the whole occupied arc lies in one of the
two components of the square boundary with p,F removed:

    p to p+u to F,       or       p to p+v to F.          (10)

This is a statement about the full original block embedding,
including every diamond chord and every coincident original
port. No extraction of a smaller positive cycle is used in the
root force equation.

## 5. The full original root force cannot lie on either occupied arc

Along the first arc in (10), every actual outward H normal has
v-component at most zero: on the p-to-p+u side it is -v, on
the p+u-to-F side it is u, and at p+u it is in their closed
quadrant. The endpoints p,F carry no block port by (8) and
Section 2. The sum of all unchanged positive block forces
therefore has v-component at most zero.

Along the other arc, the identical full support-cone calculation
gives u-component at most zero for every original block force.
But (7),(9) give the complete actual block resultant

    -lambda e=lambda a u+lambda b v,
    lambda a>0,       lambda b>0.

Both alternatives in (10) are impossible. This proves the entire
d>=1 nonparallel-root S-side-arm exclusion for every original
biconnected block, using its full actual root equation.

For the original terminal C4 and hub-diamond arms, the d<1
origin-interior transmitter exit from Section 3 completes the
whole radius interval. Every physical private load mask,
original mean, chord, true degree and all arbitrary extras remain.

## 6. Exact original scope retained

For C1.4.b2 this excludes all root frames nonparallel to the real
S-side transmitter in every C4 arm load orbit and in the hub-
diamond arm. It does not alone close their original full leaf/
width gates, because the parallel root with its actual side
application and full transverse slider has not been removed.

The corner-reach lemma and empty-quadrant implication are purely
physical and may be reused independently of the arm proof. The
arm proof requires exactly its stated complete external force
and genuine path, not an artificial radial aggregate with no
physical path to the boundary. It makes no smaller-degree
assumption at H or any private block vertex.

No added fine gate, numerical pose, coefficient packet, physical
motion, post-extraction normal choice, Lean compilation, CI or
remote operation is used.
