# A genuine D leaf excludes every complete boundary fan at its root

Date: October 26, 2026.

**Status: accepted complete hand proof after the full-source reviews
REVIEW_D_LEAF_BOUNDARY_FAN_AND_DIRECT_LEAVES_ROOT_2026_10_26.md and
REVIEW_D_LEAF_BOUNDARY_FAN_AND_DIRECT_LEAVES_HEXAGON_2026_10_26.md.**
This source changes no original checklist or ledger. It proves a uniform
nine-square completion obstruction, including the entire remaining D-leaf
alternative at the hub of the five-body fan.

## 1. Original component and retained scope

Keep the original nine interior-disjoint unit squares in the circle
centered at O, the common compatible physical stress, and

    79/40 <= R <= sqrt(1105)/16.

Suppose one complete positive component consists of the distinct actual
bodies H,L,B_1,...,B_k, where 2<=k<=7, with positive edges

    HL; H B_i (1<=i<=k); B_i B_(i+1) (1<=i<k).

The actual L is a genuine degree-one D leaf. Every B_i physically touches
the circle. Its total circle weight may be zero. Keep all physical corners,
individual zero weights, true positive degrees, original normals and means,
coincident applications, and every additional zero-weight physical contact.
The 7-k other physical units remain arbitrary and present, whether stressed
in another component or not.

**Theorem.** This complete component has no nine-square completion.

The accepted same-nine theorem NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md
excludes R<=2, with its declared arithmetic dependencies retained. It
suffices to work on 2<R<=sqrt(1105)/16. No inherited certificate is
retired here and no new arithmetic certificate is introduced.

If k=7, the seven actual B_i and the distinct genuine leaf are already
eight physical boundary units. By (2) below and the force-free eight-arc
argument in Section6, these eight units alone are impossible. Thus the
remaining embedding argument may assume k<=6. The physical boundary
graph's possible seven-cycle exception is never excluded by assumption.

## 2. The unchanged D root and strict geometric margins

RADIAL_BRIDGE_AND_LEAF_REDUCTION.md, Theorem6.1 and Corollary6.2,
with the compatible original point-normal selection, give the full chart

    r=R-sqrt(2), s=1-r,
    H=[-s,r] times [-b,a],       a,b>0, a+b=1,
    p_HL=(r,0),                n_HL=e_x.

In particular O is in the open interior of the actual H, which is
physically circle-clear. The actual leaf force has magnitude lambda>0.
We will use only

    2-sqrt(2)<r<2/3,       1/3<s<sqrt(2)-1<r,
    r^2-s^2=2r-1>3-2sqrt(2)>1/16.                    (1)

For the upper bound on r, use R<133/64 and sqrt(2)>140/99;
2/3-(133/64-140/99)=17/6336>0. The first strict comparison
follows from (133/64)^2-1105/256=9/4096>0 and the second
from 2-(140/99)^2=2/9801>0. Finally sqrt(2)<47/32 gives
3-2sqrt(2)>1/16. All quantities squared in these comparisons are
positive.

Every point x of each actual boundary body B_i and of L has

    |x| >= R-sqrt(2)=r>1/2.                            (2)

Indeed choose any physical circle corner z on the same square and use
|x|>=|z|-|z-x| and the unit-square diameter. No positive weight at the
chosen corner is required.

## 3. Physical order and the full hub equations

Let p_i,n_i,mu_i be the unchanged H--B_i application, outward unit
normal and positive magnitude. The full H force and origin-moment
equations are

    lambda e_x + sum_i mu_i n_i=0,
    sum_i mu_i det(p_i,n_i)=0.                         (3)

The actual leaf has zero origin moment. Every spoke is retained in (3).
This is not a force equation obtained by deleting the leaf.

The compatible plane embedding puts the B path in its strict circle
order. The fan's bounded faces are H B_i B_(i+1), and its exterior
face is H,B_1,...,B_k,H. The genuine boundary leaf is exterior, so its
H attachment lies in the complementary H boundary arc between the
endpoint spokes, outside the intervening triangular sectors.

No other physical unit can share (r,0). H occupies the left tangent
half-plane there, and the D leaf the right quadrant symmetric about
e_x. The two remaining tangent sectors each have angle pi/4, smaller
than the tangent cone of any unit square. Thus every p_i differs
from the actual leaf point.

Cut the H boundary at (r,0), traverse counterclockwise, and reverse
the B labels if necessary. The p_i occur in the order p_1,...,p_k.
Their original normals have ordered angular lifts

    0<=theta_1<=...<=theta_k<=2pi,                     (4)

with angle0 on the upper part of the right side and angle2pi on
its lower part. This is the physical normal-order argument of
CHORDED_HEXAGON_FAN_COMPLETE_EXCLUSION.md, Section1, with the real
leaf fixing the cut. Distinct support points have the usual convex
normal order. At a coincident vertex the disjoint inward tangent
sectors of the B bodies, and therefore their permitted common normals,
have the same physical order. The original strict convention handles
free point contacts; corner-valued side means retain their actual side
axes. No normal or mean is selected again.

Write E for the whole complementary H arc from p_k to p_1 through
(r,0). Its endpoints are distinct. For k>=3, equality would make
B_1 and B_k physically touch and close a forbidden physical boundary
cycle. For k=2, if p_1=p_2=p, equation(3) gives p_y=0. The positive
normal sum makes p maximize -e_x on H, so p=(-s,0), contrary to
|p|>=r>s. This also handles all actual endpoint coincidences.

## 4. Every point of the exterior H arc is beyond radius one quarter

Suppose first some n_i has nonzero vertical component. The vertical
part of (3) then forces both signs. The ordered lifts (4) imply

    theta_1 in [0,pi),       theta_k in (pi,2pi].       (5)

Thus p_1 is on the top side or upper part of the right side; p_k
is on the bottom side or lower part of the right side. The arc E
consists of a part of the right side and possibly eastward portions
of the top and bottom sides. Its right part has x=r>1/2.

For a top endpoint p=(x,a), if a>1/4 the entire top side is far
enough. If a<=1/4, (1)--(2) give

    x^2>=r^2-a^2>s^2.

Since -s<=x<=r, necessarily x>s>1/3. Its entire eastward top
segment has first coordinate at least x>1/3. The reflected argument
handles the bottom segment. Therefore E misses the closed quarter
disk strictly in every case of (5), including side-axis endpoints.

Now suppose all n_i are horizontal. Consecutive B bodies cannot
have opposite horizontal normals: one would lie in x>=r and the
other in x<=-s, separated by the positive gap r+s=1, contradicting
their actual physical contact. Thus the connected path has only one
sign. All-east is incompatible with the horizontal equation(3), so
all n_i=-e_x.

Every p_i is then on x=-s and obeys

    |(p_i)_y|>=sqrt(r^2-s^2)>1/4.                     (6)

The full unchanged moment equation is sum_i mu_i(p_i)_y=0, so
both height signs occur. Boundary order down the left side makes
(p_1)_y>1/4 and (p_k)_y<-1/4. The complementary arc travels up
from p_1, across the top, down the right, across the bottom and
up to p_k. Its left and horizontal portions have absolute height
greater than1/4, and its right portion has x=r>1/2.

This proves the **arc lemma**: the whole actual E has distance
strictly greater than1/4 from O. Its proof uses the entire root
equation and no degree-two equation at any internal path body.

## 5. The occupied exterior hub pocket misses the same disk

Use the occupied-crosscut construction of
CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md and
CHORDED_HEXAGON_FAN_COMPLETE_EXCLUSION.md, Section2. For geometry
only, replace each endpoint p_i by the extreme a_i of its actual
H--B_i intersection facing E. Keep p_i unchanged in (3). This
takes a subarc of E; its distance margin survives. This subarc still
contains the actual leaf point (r,0) in its relative interior: no
endpoint unit can contain that point, and its connected H contact
interval cannot pass across it. The two gap-facing extremes therefore
remain distinct and the retained subarc is nontrivial. This includes
k=2, where the endpoint bodies themselves physically touch.

Join a_1,a_k through the open interiors of their actual endpoint
units to physical circle corners facing the closing circle gap.
Each path meets H only at its a_i, and the two paths have disjoint
open interiors. Together with the H subarc and the corresponding
closing circle arc they give an actual occupied Jordan boundary J.
The chosen closing gap contains the real boundary leaf; the actual
B path lies on the other circle arc. This construction does not use
an endpoint concurrence or suppose that such a point lies in a unit.

The H portion misses the closed quarter disk by Section4. The
endpoint-body portions do so by (2), and the circle portion lies
on radius R. Thus J has a strictly positive distance margin from
the closed quarter disk.

The hub pocket is the side of J locally exterior to H along its
H arc. The whole int(H) is connected and avoids J. At a side-interior
point of the nontrivial H subarc, int(H) is precisely on the side
opposite this exterior pocket. The origin, being in int(H), is
therefore outside the pocket. Equivalently the winding number of
its occupied boundary at O is zero. The existence of such a side
point follows from the distinct arc endpoints, and handles subarcs
passing through vertices as well.

Winding is constant on the connected closed quarter disk because
that disk avoids J. The entire disk is outside the pocket. Compactness
and the strict boundary margin permit a slightly larger concentric
disk with the same property. Hence every whole extra confined to
this pocket has distance strictly greater than1/4 from O.

The genuine leaf or other zero-weight physical contacts can subdivide
this free pocket; they cannot enlarge it through its occupied boundary.
Every such subdivision is retained.

## 6. All remaining units are in that pocket, giving eight long arcs

Attach the actual fan to the containing circle by disjoint occupied
access paths through each B_i. The face cover is exactly its k-1
triangular faces, the k-1 exterior pockets of consecutive boundary
pairs, and the one closing hub pocket through H. The first two
types have unit capacity zero by the complete contact-triangle and
boundary-pair pocket theorems of CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md.

Each extra's connected open interior avoids the occupied paths, so
lies on one face side. At a weak junction take a compact concentric
inner square of the extra, choose sufficiently small compatible
routing neighborhoods and then take closure. The same physical
winding argument therefore assigns its whole closed square. This
is the complete fan face cover of the five-spoke theorem, with
arbitrary k; no other interior face or free component is omitted.

All 7-k other original physical units must consequently be in the
hub pocket, and have distance greater than1/4 by Section5. The k
actual boundary path bodies and the real leaf have that same property
by (2). Thus there are exactly

    (7-k)+k+1=8

distinct actual units with distance greater than1/4. H is the sole
remaining unit and remains physically present throughout.

To apply the force-free inner-arc theorem, let z be the nearest point
to O of any one of these convex squares T. Convexity and the minimum
of |z+t(x-z)|^2 at t=0+ give

    (z/|z|).x >= |z|>1/4       for every x in T.

GENERAL_SIDE_CHANNEL_CAP_INNER_ARC.md, Section1, therefore gives
each T one connected open-interior arc on radius5/4 of length
strictly greater than pi/4. Their interiors are pairwise disjoint,
so the eight arcs are disjoint. Their total angular measure would
exceed2pi, a contradiction. This proves the full theorem.

## 7. Exact original gate consequence and limits

For a genuine leaf at the hub of the original five-body fan, the
complete necessary cover forces all four path bodies loaded. Taking
k=4 covers the full original D-root slider, all actual degree-three
internal forces, physical masks, individual zero weights, original
owners and means, and all three arbitrary extras. The whole gate

    M6.B5L.FAN.HUB.L1234.D

is ready for closure after review. Combined with the already accepted
S alternative in S_LEAF_CONNECTED_BOUNDARY_NEIGHBORS.md, it gives
the whole original rooted-type parent

    M6.B5L.FAN.HUB.

The same uniform theorem supplies an alternative route for the already
closed D-leaf triangle and hub diamond. No old certificate is declared
retired without its separate caller audit. Endpoint/inner fan roots
do not have the present complete component and retain their distinct
original force equations. Other rooted types, coarse C1.5.b1,
the unrestricted inequality, original equality classification,
older prerequisite audit and Lean integration remain open.

No numerical pose, new scalar certificate, Lean compilation, CI,
force deletion or shared-ledger mutation is used or performed here.
