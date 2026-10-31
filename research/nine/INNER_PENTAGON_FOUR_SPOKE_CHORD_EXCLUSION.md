# A four-ring cross excludes the whole four-spoke chorded pentagon

Date: October 26, 2026.

**Status: accepted complete hand proof after the two independent full
source/scope reviews REVIEW_INNER_PENTAGON_FOUR_SPOKE_CHORD_HEXAGON_2026_10_26.md
and REVIEW_INNER_PENTAGON_FOUR_SPOKE_CHORD_ROOTED_BLOCKS_2026_10_26.md.**
No checklist label is changed by this source alone.

Put Q=1105/256. Retain the same nine actual unit squares, with disjoint
open interiors, in D_R, where 79/40<=R<=sqrt(Q). Use the common selected
physical plane embedding. Every positive force, original normal, actual
application mean, physical circle mask and individual zero circle weight
remains. In particular no fourth spoke is dropped from a hub equation.

**Theorem.** The entire interior-pentagon graph with rim 012340,
interior body H, spokes H0,H1,H2,H3 and rim chord03 is impossible.
Both complete residual load families 124 and 0124 are covered. The
three other physical packing squares are arbitrary and remain present.

The new geometric lemma below does not use any force equation or exact
degree. It also applies to a larger graph containing the same physical
cross and the specified boundary square.

## 1. A unit meeting the two inner arms of a cross is circle-clear

Consider an aligned cross: a central unit C and the four units sharing
its four full sides. Suppose at least two of the four arms physically
touch the containing circle. The exact cross comparisons in
SPANNING_K23_LEAF_BLOCK_EXCLUSION.md, Section 3, are independent of the
leaf hypothesis used later in that source. They give the following
complete alternatives.

An opposite boundary pair forces the central center to be O and
R^2=5/2. For clarity, equality of the right/left corner maxima first
gives x=0. Comparing their common radius with the farther of the top
and bottom arms then gives y=0. This is impossible in our radius window.
Thus there are exactly two boundary arms, and they are adjacent.

Rotate and reflect the entire actual configuration so these are the
right and top arms. Comparing right/left containment gives x>=0, and
comparing top/bottom gives y>=0 for C's center (x,y). Equality of the
right and top corner maxima gives x=y=t. Hence

    c_C=(t,t),              R^2=2t^2+4t+5/2.               (1)

The right side increases on t>=0. At t=3/10 it is 97/25, below
(79/40)^2=6241/1600, by 33/1600. At t=2/5 it is 221/50,
above Q by 663/6400. Therefore

    3/10<t<2/5,             1/10<u=1/2-t<1/5.            (2)

Let W and S denote the two other arms, to the left and below C. Their
common vertex is P=(-u,-u). In coordinates translated by P, the three
actual squares C,W,S are

    C=[0,1] x [0,1],
    W=[-1,0] x [0,1],
    S=[0,1] x [-1,0].                                    (3)

Let T be any other actual unit square touching both W and S. No contact
force or circle weight at T is assumed. Write z=(z_x,z_y) for its center
in the coordinates (3), and w for its half-width along either coordinate
axis. For a unit square these two widths are equal and

    1/2<=w<=1/sqrt(2)<1.

Touching S, whose x projection is [0,1], gives z_x+w>=0.
Touching W, whose x projection is [-1,0], gives z_x-w<=0.
The two y projections give the same inequalities in the other order.
Thus

    -w<=z_x<=w,             -w<=z_y<=w.                  (4)

The center z is an interior point of T, so it belongs to none of the
three closed squares in (3). Indeed an open neighborhood of a point
in any of those squares meets its open interior. Since w<1, every
point of [-w,w]^2 outside the strict southwest quadrant belongs to
C, W or S. Equations (3)--(4) consequently imply

    -w<=z_x<0,              -w<=z_y<0.                  (5)

This is a restriction on the actual center, with no assertion that T
lies wholly in the southwest quadrant and no prescribed contact point.

We next bound every actual vertex v of T about P. Choose an orientation
representative a=cos(theta), b=sin(theta), 0<=theta<=pi/4. Reflections,
quarter turns and exchange of the coordinate axes do not change the
following absolute-coordinate estimates. Set

    w=(a+b)/2,              d=(a-b)/2.

The absolute coordinates of a vertex offset v-z are w,d in one of the
two orders. By (5), for each coordinate
|v_i|<=w+|(v-z)_i|. Therefore every vertex satisfies

    |v|^2 <= (2w)^2+(w+d)^2
          = (a+b)^2+a^2
          = 3/2+(1/2)cos(2theta)+sin(2theta)
          <= (3+sqrt(5))/2
          < 11/4 < 25/9.                                (6)

The non-strict comparison is Cauchy--Schwarz applied to (1/2,1).
The first strict comparison uses sqrt(5)<5/2. Hence |v|<5/3.
Returning to the unchanged circle origin, (2) gives |P|=sqrt(2)u<3/10,
using sqrt(2)<3/2. Every actual vertex of T consequently has norm

    |P+v| < 5/3+3/10 = 59/30 < 79/40 <= R.              (7)

The middle strict comparison has reserve 1/120. Convexity of the disk
then puts the whole T strictly inside D_R. We have proved:

**Cross lemma.** In the stated radius window, an aligned cross with at
least two physical boundary arms has exactly two adjacent boundary arms.
Any additional unit touching both other arms is physically circle-clear.

This covers every orientation, point/side contact, tangency, contact mean
and weak endpoint of T. Only its actual physical touching and disjoint
interiors were used. Its center need not be O, and its sides need not
align with the cross.

## 2. The exact wheel subgraph forces that cross

In the stated pentagon graph, retain the positive four-cycle 01230 and
its actual spokes from H to all four cycle vertices. H is on the bounded
side of this four-cycle in the given physical embedding.

Here is the embedding check without a drawn-pose assumption. The spokes
H0 and H3 split the rim pentagon into the sector bounded by H0123H and
the sector bounded by H0340H. The positive outer chord03 lies in the
latter sector; it cuts off the outer triangular face034. The union of
the four actual triangular sectors H01,H12,H23,H30 therefore has outer
boundary01230 and contains H. Equivalently this is the embedded
four-rim wheel obtained by retaining the rim path0123, chord03 and
the four unchanged spokes. The actual extra rim body4 lies outside it.
No equilibrium equation is applied after this topological restriction.

The degree-free equality theorem FOUR_CYCLE_THREE_BOUNDARY_HOLE_EMPTY.md,
Sections 1--2, or SPANNING_K23_LEAF_BLOCK_EXCLUSION.md, Section 2, applies
to H inside that actual four-ring. It forces H and the four ring units
to be the exact aligned cross: H is its central unit and 0,1,2,3 are
its four arms in their actual cyclic order. The conclusion includes
the original shared means and arbitrarily close routing at coincident
contact junctions. The three-boundary and leaf premises in the later
sections of those sources are not used.

## 3. Both complete load families and the whole graph are excluded

The exact graph/load cover SIX_BODY_INNER_PENTAGON_LOAD_COVER.md,
Sections 2 and 6, forces 1,2,4 to be positively loaded. Vertices1 and2
are genuine positive-degree-three vertices whose neighbor H touches
their other two neighbors; vertex4 is a genuine positive-degree-two
triangle tip because chord03 is retained. The cover leaves precisely
the representatives124 and0124, including their full graph-preserving
reflections, physical masks and means.

In the cross just proved, 1 and2 are adjacent boundary arms. Vertices0
and3 are the other two adjacent arms. The actual unit4 touches both0
and3 through its two unchanged rim edges. Section 1 therefore proves
that4 is physically circle-clear. This contradicts its positive load.

This single contradiction covers both complete load families, without
requiring the optional fourth load in0124. That fourth load also gives
an opposite boundary pair in the cross and is independently impossible.
The argument never calls a degree-two transmitter theorem at any of H,
0 or3, whose genuine positive degrees are four. It changes no weight,
force, application point, original side mean or square position.

## 4. Exact original gate scope

After independent source and original-domain review, the complete exits
provided here are exactly:

* M6.B6.PENTAGON.H4_D1.L124;
* M6.B6.PENTAGON.H4_D1.L0124;
* M6.B6.PENTAGON.H4_D1_EXIT.

The original nine physical squares remain throughout; in fact the
contradiction is already among the displayed six physical units. No
completion region or force deletion is used. This closes one entire
pentagon graph type, not the whole pentagon cover or coarse C1.6.b0.
The four other interior-pentagon graph types retain their complete
original obligations. No new gate label, sampled pose, coefficient
packet, Lean compilation or CI is introduced.
