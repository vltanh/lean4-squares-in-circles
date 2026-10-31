# A D leaf excludes a boundary path with triangular or quadrilateral hub faces

Date: October 26, 2026.

**Status: complete uniform hand proof; full root and separate independent
reviews accepted.** This source keeps every actual spoke while allowing
some internal spokes to be absent from the original positive graph. Its
new whole original caller is the four-load D-leaf house at a hub.

## 1. Original component and full retained domain

Keep the same nine interior-disjoint unit squares, containing circle,
compatible physical certificate and radius window

    79/40 <= R <= sqrt(1105)/16.

Suppose an entire positive component has the following actual edges:

    B_i B_(i+1), 1<=i<k;
    H B_i, i in I;
    H L_j, 1<=j<=m.

Here k>=2, m>=1, k+m+1<=9. Every B_i physically touches the circle.
The set I contains 1 and k, and consecutive indices in I differ by
at most two. Every L_j is a genuine radial S or D leaf, and at least
one is D. There are no other positive edges in this component.
The original B endpoints therefore have true positive degree two;
an internal B retains its true degree two or three. All original
magnitudes, normals, contact owners and means, every physical circle
mask and individual zero corner weight remain. A physically boundary
B is allowed to have zero total circle load. No missing spoke is
inserted and no present spoke is removed. The other 8-k-m original
physical units remain arbitrary and present.

**Theorem.** This entire family has no nine-square completion.

Use the accepted same-nine NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md
to reduce to R>2, retaining all its declared arithmetic dependencies.
If k+m=8, the eight distinct physical boundary units B_i,L_j already
give the eight-arc contradiction in Section 6. Thus the rest of the
proof can assume k+m<=7 and hence k<=6. In particular the possible
seven-cycle exception for the physical boundary graph is not discarded.

## 2. The unchanged D root and the two endpoint moments

Orient the actual D leaf L_1 east. The full original chart from
RADIAL_BRIDGE_AND_LEAF_REDUCTION.md is

    r=R-sqrt(2), s=1-r,
    H=[-s,r] times [-b,a],  a,b>0, a+b=1,
    p_(H,L_1)=(r,0), n_(H,L_1)=e_x.

The complete margin calculation in
D_LEAF_BOUNDARY_FAN_COMPLETE_EXCLUSION.md, Section 2, gives

    1/2<r<2/3,   1/3<s<r,
    r^2-s^2>1/16.                                      (1)

The origin is in int(H). Every point x of every physical boundary
unit has |x|>=r: choose one of its physical circle corners z and
use |x|>=R-|x-z|>=R-sqrt(2). This does not use the weight at z.

All B bodies occur on the boundary of the unbounded face. The actual
outer-face order is H,B_1,...,B_k,H, and the internal positive spokes
have their index order on the occupied H arc. The bounded faces
between consecutive actual spokes are triangles or four-cycles;
the latter have three physical boundary B bodies. These facts follow
from the physical boundary order and plane embedding, exactly as in
GENERAL_SINGLE_HUB_BOUNDARY_PATH_POCKET.md, Section 1. That geometric
order proof does not use its separate zero-total-hub-force premise.
All genuine boundary leaves are in the exterior face.

No other physical square contains the true leaf point (r,0). H has
a tangent half-plane there and L_1 has the outward symmetric right
quadrant; the two remaining tangent sectors have angle pi/4 each.
Neither admits the tangent cone of a further square. Cut the H
boundary at this actual point and label the B path in counterclockwise
occupied-arc order. For each i in I let p_i,n_i,mu_i be its unchanged
H application, outward unit normal and positive magnitude. The actual
normal lifts satisfy

    0<=theta_1<=theta_i<=theta_k<=2pi,                  (2)

in index order. Angle 0 belongs to the upper right side and angle
2pi to the lower right side. Coincident vertex applications retain
the physical tangent-sector order; shared-side means retain their
actual axes. This is the same full normal-order statement cited in
the single-hub source, and does not require an omitted spoke.

Let g_i,gamma_i,t_i be the unchanged normal from B_i to B_(i+1),
its positive magnitude and its original application. The degree-free
boundary-pair moment theorem, FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md,
Lemma 1.1, gives det(t_i,g_i)>0 in this counterclockwise physical
order. The true degree-two endpoint torque equations, with every
circle force radial about O, therefore give

    mu_1 det(p_1,n_1)= gamma_1 det(t_1,g_1)>0,
    mu_k det(p_k,n_k)=-gamma_(k-1) det(t_(k-1),g_(k-1))<0.

In particular

    det(p_1,n_1)>0,       det(p_k,n_k)<0.               (3)

This remains valid when an endpoint total circle weight is zero.
No degree-two equation is used at an internal degree-three body.

The endpoint applications are distinct. For k>=3 equality would
make the boundary bodies B_1 and B_k touch, closing a physical cycle
on k<=6 vertices, which is impossible. For k=2, a common application
p would put both unchanged normals in one ordered H normal cone.
On a side they would be identical. At a vertex, det(p,n(theta)) is
strictly increasing across that cone, since its derivative is
p.n(theta)>0 and O is in int(H). The cut point is not p, so the
order in (2) is precisely this local order, without a full turn.
Both possibilities contradict the first-positive/last-negative
signs in (3). Write E for the complementary H boundary arc from
p_k through (r,0) to p_1. It is a nontrivial arc containing the
actual leaf point in its relative interior.

## 3. No genuine direct leaf points toward a shallow horizontal side

If a,b>1/4, (1) puts a slightly larger concentric disk than D_(1/4)
inside int(H). Every other actual closed square avoids that disk,
so Section 6 immediately supplies the contradiction. Otherwise
reflect vertically if needed and assume

    0<a<=1/4,       b>=3/4.                            (4)

Every actual leaf direction e_j then has nonpositive y component.
For a D leaf a positive y component would require the north side
axis and actual radial point (0,a), with a=r>1/2, impossible.

For an S leaf the original radial support point is d e_j, where

    d=sqrt(R^2-1/4)-1>9/10.

A positive y component puts this point on the top side: either the
radial north point (0,a) or a top vertex. Every such point has norm
at most sqrt(r^2+a^2), with

    r^2+a^2<73/144<9/16<d^2.

This excludes every tilted and side-axis positive-y S alternative.

There is no additional horizontal genuine leaf. A horizontal S leaf
would require r=d or s=d, whereas r,s<2/3<d. A west D leaf requires
s=r, contrary to (1). An east D leaf would be the very same occupied
square as L_1. Thus every distinct additional leaf has strictly
negative y direction. This is the complete leaf-owner argument of
D_LEAF_BOUNDARY_FAN_DIRECT_LEAVES_EXCLUSION.md, Section 3; it is
independent of the internal-spoke set.

## 4. The exterior H arc misses the quarter disk strictly

Write alpha_j>0 for the actual radial leaf magnitudes. The full
unchanged H force equation is

    sum_(i in I) mu_i n_i + sum_(j=1)^m alpha_j e_j=0.       (5)

There is a positive-y spoke. Otherwise the y part of (5) and Section 3
force all spokes horizontal and m=1. The first normal in (2) can
then only have lift 0, pi or 2pi. If it has lift 0, its application
is (r,y) with y>0, so det(p_1,n_1)=-y<0, contradicting (3).
If it has lift pi, write p_1=(-s,y). Its physical boundary neighbor
gives s^2+y^2>=r^2, so |y|>1/4 by (1). Since y<=a<=1/4, this
means y<-1/4 and det(p_1,n_1)=y<0, again a contradiction.
If its lift is 2pi, every spoke is east, which cannot balance the
east leaf in (5). These are all horizontal possibilities, with no
assumption that two consecutive actual spoke neighbors touch.

Consequently theta_1<pi. The first east normal is already excluded
by (3). A northwest H vertex has squared norm

    s^2+a^2<r^2,

so cannot belong to a physical boundary body. Therefore p_1 is
either the northeast vertex or a point (x,a) of the top side with
the north normal. In the latter case

    x^2>=r^2-a^2>s^2,       x>s>1/3.                  (6)

The northeast vertex also has x=r>1/3. Its actual origin moment
is strictly positive by (3), without a concurrence argument.

The last endpoint cannot lie on that same northeast/top part. A
north side normal there has moment x>1/3 by (6). If both endpoint
applications are the northeast vertex, their moments are

    f(theta)=r sin(theta)-a cos(theta), 0<=theta<=pi/2.

This function is strictly increasing, since
f'(theta)=r cos(theta)+a sin(theta)>0. The ordering (2) and the
first sign in (3) would give f(theta_k)>0, contradicting the last
sign in (3). If the first endpoint is already on the top-side axis,
normal order cannot return to the smaller-angle northeast cone.
The upper-right side has lift 0 and is likewise already past the
cut. The northwest corner remains impossible by its norm.

Thus the last endpoint is on the left side below height -1/4, or
on the bottom/lower-right portion. For a left endpoint the strict
height bound is the same s^2+y^2>=r^2 calculation used above.
The entire complementary arc E now consists of some lower-left
side with y<-1/4, some bottom side with y=-b<=-3/4, the right side
with x=r>1/2, and an eastward top segment with x>=x_1>1/3.
Some of these pieces may be absent. Every piece has distance
strictly greater than 1/4 from O. Reflection gives the full case
b<=1/4 as well. Every actual owner, side-axis endpoint and weak
normal-order coincidence was included.

## 5. The occupied closing pocket has the same distance margin

The geometric pocket assembly of
D_LEAF_BOUNDARY_FAN_COMPLETE_EXCLUSION.md, Section 5, now applies
without change. Only its proved arc lemma and O in int(H) are used;
its complete-spoke force equations are not reused.

For completeness, replace p_1,p_k only for the barrier construction
by the gap-facing extremes of their actual H intersections. This
takes a subarc of E. Each endpoint intersection is connected and
avoids the real leaf point, so the retained subarc still contains
(r,0) in its relative interior and has distinct endpoints. Join
these extremes through the open interiors of their respective
boundary units to circle corners facing the closing gap. Together
with this H subarc and the closing circle arc, these disjoint
occupied paths make an actual Jordan boundary J. This construction
also works for k=2, when the two endpoint units physically touch:
their access paths have disjoint open interiors.

The H arc misses the closed quarter disk by Section 4; the endpoint
unit portions have norm at least r>1/2; and the circle portion is
at radius R. Thus J has a strict distance margin. Along a side
point of its nontrivial H arc, int(H) lies on the side opposite the
exterior pocket. The whole int(H) is connected and avoids J. Since
O lies there, J has winding zero about O. Winding is constant on
the connected closed quarter disk, which avoids J, so the disk is
outside the pocket. Compactness gives the same statement for a
slightly larger disk. Every whole unit confined to this pocket
therefore has distance strictly greater than 1/4. The actual leaves
and extra zero-weight physical contacts may subdivide it, but cannot
enlarge it through the occupied barrier.

## 6. The complete face cover leaves eight long interior arcs

Attach the actual B path to the containing circle through the B
interiors. The complete face cover consists of the following:

* Between two consecutive actual hub spokes, the bounded triangle
  or four-cycle. A triangle has unit capacity zero by
  CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md. A four-cycle has its
  three B members physically on the circle and has capacity zero
  by FOUR_CYCLE_THREE_BOUNDARY_HOLE_EMPTY.md. The radius window
  excludes its sole possible equality radius R^2=5/2.
* The exterior pocket of each consecutive pair B_i,B_(i+1), all
  of capacity zero by the boundary-pair theorem in the first source.
* The closing hub pocket of Section 5.

This is the same occupied-path face localization as for the full
fan, with the actual triangular or quadrilateral inner faces used
in place of its all-triangle list. A remaining unit's connected
open interior avoids the occupied paths. At a weak junction first
take a compact concentric inner square of that unit, route through
sufficiently small compatible neighborhoods, and take closure.
Thus its whole original closed square is assigned to one actual
face side, including every shared interval and weak subdivision.
Every one of the 8-k-m remaining physical units must be in the
closing pocket. The k+m physical boundary units have norm at
least r>1/2 throughout. Consequently exactly

    (8-k-m)+k+m=8

distinct original units have distance strictly greater than 1/4.
The actual H remains as the ninth unit throughout.

For any such convex square T, its nearest point z to O gives

    (z/|z|).x >= |z|>1/4 for every x in T.

The uniform force-free cap theorem
GENERAL_SIDE_CHANNEL_CAP_INNER_ARC.md, Section 1, now assigns each
T a connected open-interior arc of angular length strictly greater
than pi/4 on the same radius-5/4 circle. Pairwise disjoint square
interiors make these eight arcs disjoint. Their angular measures
sum to more than 2pi, the final contradiction. This also supplies
the direct k+m=8 and a,b>1/4 exits used above.

## 7. Exact original caller and the remaining gates

For the house rooted at hub A, use H=A and the actual ordered path

    B_1=T, B_2=D, B_3=C, B_4=B,       I={1,2,4}.

These are precisely the original edges AT,AD,AB,TD,DC,CB. The load
set TDCB makes all four path units physical boundary units. The
actual degrees are A4,T2,D3,C2,B2,L1; D is never assigned degree
two and no AC spoke is created. The inner faces are the actual
triangle ATD and actual four-cycle ADCB, the latter with its three
boundary bodies D,C,B. Set m=1 and retain all three arbitrary
completion squares. This proves the entire original gate

    M6.B5L.HOUSE.HUB.LTDCB.D.

It includes the full original D-root transverse slider, every
circle mask and zero weight, every owner and shared-side mean,
all radius endpoints after the stated same-nine lower-bound join,
and the complete three-extra completion domain. Its S alternative
and the other house load orbits remain separate obligations.

The same theorem gives another complete route for a C4 at a root
with at least one genuine D leaf and any additional genuine direct
leaves, when its other three bodies are physical boundary: take
k=3 and I={1,3}. In the original six-body same-root C4 table, the
SD and DD BCD alternatives were already closed by
ORIGIN_ROOT_C4_PRESSURE_AND_BOUQUET_CLOSURE.md. They are not new
gate closures here. The theorem also includes the accepted full
fan families, without retiring their earlier proofs or dependencies.

Arbitrary bridge arms, distinct leaf roots, absent physical boundary
loads, and gaps of three or more between actual spokes are outside
this theorem. No force deletion, numerical pose, new arithmetic
certificate, Lean compilation, CI or shared-checklist mutation is
used or performed.
