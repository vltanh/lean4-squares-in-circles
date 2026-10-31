# A central quarter-disk excludes every nine-square completion

Date: October 26, 2026.

**Status: accepted complete shared geometric obstruction after the full-source
reviews REVIEW_QUARTER_DISK_COMPLETION_OBSTRUCTION_ROOT_2026_10_26.md and
REVIEW_QUARTER_DISK_COMPLETION_ROOTED_BLOCKS_2026_10_26.md.**
The five-boundary-neighbor margin needed to apply it to every exterior fan
is not proved here. No original graph/load family or ledger label is closed.

Put Q=1105/256 and rho=5/4. Every square below is an actual unit square;
all physical squares have pairwise disjoint open interiors and lie in the
same disk D_R with R<=sqrt(Q). No force, normal-selection, circle-load,
positive-degree, or symmetry premise is used in Sections 1--2.

## 1. The weak quarter-distance arc-measure endpoint

The accepted `GENERAL_SIDE_CHANNEL_CAP_INNER_ARC.md`, Section 1, proves:
if a unit E has distance strictly greater than 1/4 from O, its open
interior meets |p|=rho in a connected open arc of length greater than
pi/4. The actual circle-angle measure conclusion remains true when

    dist(O,E) >= 1/4.                                    (1)

Connectedness and membership of the radial center point are deliberately
not claimed at equality. Here is the full additional endpoint check.

Use the same own-axis coordinates as the accepted source:

    E=[A,a] times [B,b],
    a=A+1, b=B+1, a>=b>=1/2,
    a^2+b^2<=Q.

If a>rho, the entire accepted inner-face argument is unchanged. Its
strict interval-length reserves depend only on a>rho and the target
radius, not on strictness of (1).

Suppose a<=rho. If B>0, then

    0<B<=A<=1/4,
    k^2=A^2+B^2>=1/16.

In the accepted outer-face calculation, the derivative sign is the sign of

    (A-B)[(A+B-1/4)^2+(k^2-1/16)(A+B+1)],

which remains nonnegative. Its outer-outer candidate length therefore
satisfies

    L >= 2 asin((1+k/sqrt(2))/(5/4))-pi/2
      >= 2 asin((4+1/sqrt(2))/5)-pi/2
      > pi/4.

The last comparison retains the accepted strict squared reserve
(16-9 sqrt(2))/100>0. The other three candidate differences are unchanged
strict strip or inner-face estimates. Thus this branch also has the
claimed strict arc-measure bound, including k=1/4.

The only new case has B<=0. Then the nearest-point norm is max(A,0),
so (1) and a<=rho force

    A=1/4, a=5/4, -1/2<=B<=0, 1/2<=b<=1.

The y-coordinate restrictions on the circle give the angular interval

    asin(B/rho) < theta < asin(b/rho).

Throughout this interval x>1/4: its endpoint absolute y-coordinates are
at most one, so x>=sqrt(rho^2-1)=3/4>1/4. The outer restriction x<a=rho
only removes the point theta=0. It does not change angular measure.
Consequently the total open-interior angular measure is exactly

    asin(b/rho)-asin((b-1)/rho)
      >= 2 asin(2/5) > pi/4.

For b in [1/2,1], the difference is nondecreasing because
b>=|b-1| and the derivative of asin is increasing with the absolute
argument. The strict comparison is the accepted elementary inequality
sin(pi/8)<2/5. This covers every equality case of (1).

The weak endpoint can have two open arcs separated by the removed radial
outer-face point. Their total measure is the quantity just computed.

**Lemma 1.** Every actual unit E satisfying (1) contributes more than
pi/4 of open-interior angular measure on |p|=5/4.

## 2. No one unit can contain the closed quarter-disk

Suppose one unit H contains the closed disk D_(1/4). Every point whose
norm is strictly smaller than 1/4 then lies in int(H): the open disk
itself is an open subset of H. By the original pairwise interior
disjointness, every other unit E is disjoint from that open disk, even
on its own boundary. If a boundary point of E belonged to int(H), a
small neighborhood in int(H) would meet int(E), which is impossible.
Thus every other physical unit has dist(O,E)>=1/4.

In a nine-unit packing there are eight such units. Lemma 1 gives eight
pairwise disjoint open-interior subsets of the same radius-5/4 circle,
each of angular measure strictly greater than pi/4. Their sum exceeds
2pi, a contradiction.

**Theorem 2.** In any nine-unit-square packing inside D_(sqrt(Q)), no
actual unit square contains the closed disk D_(1/4).

This includes weak contact and equality endpoints. It does not assume
that the eight other units touch the containing circle or belong to one
stress component, and it does not move any square.

In the own axes of any unit H, with actual center coordinates (x,y),
closed quarter-disk containment is exactly

    |x|<=1/4 and |y|<=1/4.

Thus every actual unit of such a nine-square packing has

    max(|x|,|y|)>1/4.                                   (2)

The coordinate choice is the square's actual frame, not an independently
selected frame about O.

## 3. Exact consequence for the full exterior fan and the open premise

The full three-chord exterior-hexagon fan in
`SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md` has the one load set 12345.
Its actual hub H=0 is clear and has true positive degree five. The
five boundary bodies form their original physical path 1--2--3--4--5.
Every hub spoke, boundary force, original side mean, physical circle
mask, zero individual corner weight and all three completion units remain.

The accepted `CHORDED_HEXAGON_CENTRAL_CAPACITY_ONE.md` gives zero central
capacity for this triangulated graph. Direct touching-boundary-pair
outer pockets also have zero unit capacity. Thus all three completion
units, if present, occupy the sole exterior pocket passing through H
between boundary bodies 5 and 1.

Theorem 2 gives an independent necessary condition on every such
surviving full fan: the actual H frame must satisfy (2). Therefore a
uniform theorem forcing |x|,|y|<=1/4 from its five actual boundary
neighbors and retained force equations would exclude the whole fan
immediately, without a separate exterior-pocket count.

**That five-neighbor margin theorem remains open in this source.**
Neither a numerical star search nor a center-only annular relaxation
establishes it. A stronger claim that no five-boundary-neighbor star
exists, after dropping the fan's additional path-contact requirements,
is also not an input and must not be substituted for the stated missing
margin premise.

The new proved input is the complete weak quarter-distance arc-measure
lemma and its nine-square central-disk exclusion. The remaining original
fan still requires a whole-domain geometric or force argument. No pose
box, finite sample, new label, Lean compilation, CI run, remote write, or
shared-ledger change is part of this source.
