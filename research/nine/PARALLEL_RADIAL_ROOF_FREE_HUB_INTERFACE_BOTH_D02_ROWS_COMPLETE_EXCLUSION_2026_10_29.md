# A parallel roof has no free hub interface in either remaining D02 row

Date: October 29, 2026 UTC. Author: shared_terminal continuation.

**Status: complete proposed hand proof and literal original feature join,
submitted for separate full independent review.** This excludes the entire
parallel-roof / free-AD feature of original D02.L135 and D02.L1345.
The complete already reviewed aligned-hub theorem covers an aligned hub;
the new proof below covers the whole complementary both-tilted domain.
Every actual shared return, original side mean, positive magnitude,
physical circle mask and individual zero coefficient remains.

The new whole-star geometry makes each hub pocket have capacity one and
makes one of those two pockets empty. It also separates the entire actual
B and C by a vertical gap greater than one. Thus a genuine unloaded N
cannot be a side transmitter, leaving only its already excluded diagonal
exterior pocket. The same joint pocket bound closes the loaded-N row.
The complementary owned-AD and nonparallel-roof features remain separate.

## 1. Exact original statement and complete selected entry

Retain all nine actual closed unit squares with pairwise disjoint open
interiors in the same circle about O. The original radius satisfies

    2<=R<=sqrt(1105)/16,
    Qstar=1105/256,
    d=sqrt(R^2-1/4)-1<61/60.

The actual original component is the six-cycle and its positive chord,
with the roles

    A=0, V=1, D=2, C=3, N=4, B=5;
    AV, VD, DC, CN, NB, BA, AD.

A,D are truly unloaded of degree three. V,B,C are genuinely loaded
of degree two. N is truly unloaded of degree two in L135 and genuinely
loaded of degree two in L1345. All three remaining actual squares are
retained as arbitrary completion units.

Suppose the two original roof-normal lines at V are parallel and the
original AD normal is free at its two actual vertices. The complete
loaded-parallel-full-star theorem at f0e7b44a derives, from the whole
original V2 including its initial masks and opposite-sign possibilities,

    V=[d,d+1] x [-1/2,1/2],
    AV and DV both point East toward V,
    both original V circle weights are equal and positive.

No roof mean is changed. If either hub is aligned to V, the complete
5089e790 source already excludes the feature in both original rows.
Hence keep the entire remaining both-tilted feature.

The complete distinct-application/owner theorem at ce5219a2 applies
to both actual unloaded3 hubs. It proves their three original
applications distinct, including endpoint means of a shared exterior
return, and forces both AB and DC to have positive physical length
when AD is free. The theorem is applied to the already selected common
certificate; no normal is reselected after extraction.

The proof below retains those two genuine shared contacts and all their
actual original means. It does not incorrectly apply a three-singleton
selector after either shared contact has been established.

## 2. The complete free-vertex geometry is a symmetric two-hub chart

Let P_A,P_D be the original roof applications. Each is its tilted
hub's unique maximum-East vertex, of x coordinate d. They cannot
coincide: the direction West is strictly inside both actual inward
vertex quadrants there, so a short segment in that direction would
lie in both open interiors.

The free AD point q is an actual vertex of each hub. It cannot be
either roof vertex, by the complete distinctness theorem. It also
cannot be the opposite minimum-East vertex of either hub. At that
vertex its original outward AD normal has negative x component, so
the real other hub's strict minimum-support span is less than one;
its maximum x would be less than

    d-(c+s)+1<d,

where c,s>0 are the tilted hub's two horizontal inward components
and c^2+s^2=1. This contradicts its actual roof support d.

Thus q is adjacent to P_A in A and to P_D in D. Their two edge
vectors from the roof points have the same negative horizontal
component. Being unit vectors, they have vertical components of equal
absolute value. If the vertical signs agreed, P_A and P_D would
coincide. Hence the signs are opposite. Reflect the entire data if
necessary so P_A is the upper roof point. The exact physical chart is

    w=(l,s), u=(-s,l), wD=(l,-s), uD=(-s,-l),
    l,s>0, l^2+s^2=1,
    A=q+[0,1]w+[0,1]u,
    D=q+[0,1]wD+[0,1]uD,
    P_A=q+w, P_D=q+wD,
    q_x=d-l.                                           (1)

The original roof points lie in the relative interior of V's inner
side. At a V endpoint the actual point-only vertex/vertex normal
would be a V axis, contrary to the retained strict singleton convention.
Consequently their vertical difference 2*s is strictly less than one:

    0<s<1/2, l>sqrt(3)/2>173/200.                       (2)

This covers the entire free vertex cone and every original tilted hub
frame. No angle subdomain was imposed.

## 3. Full A3, D3 and V2 determine both genuine shared means

At q the actual A-to-D normal is strictly outward from A and strictly
inward into D. Let mu,nu>0 be the original roof magnitudes and retain
the original AD force rho*n, rho>0. The actual shared AB normal is
one of A's side axes. Projection of mu*East+rho*n onto u is strictly
negative, because East.u=-s and n.u<0. Therefore the only possible
shared AB outward axis is +u. Reflection gives +uD for DC.

Write their original positive magnitudes as P_B,P_C. Summing the full
A3 and D3 vectors gives

    (mu+nu)*East+P_B*u+P_C*uD=0.

The vertical equation gives P_B=P_C=:P, and the horizontal equation
then gives

    P=(mu+nu)/(2*s),
    rho*n=((nu-mu)/2,-(mu+nu)*l/(2*s)).                 (3)

This is the exact original AD force, not a replacement force at a new
application. Its moment remains at the actual q.

Retain the two actual shared-side means in their complete form

    S_B=q+u+t_B*w,
    S_C=q+uD+t_C*wD,
    0<=t_B,t_C<=1.

Taking the whole A3 and D3 moments about the actual q gives

    t_B=mu*s/P=2*mu*s^2/(mu+nu),
    t_C=nu*s/P=2*nu*s^2/(mu+nu).                        (4)

In particular both original means are strictly between zero and
2*s^2<1/2 in their respective hub side coordinates. They still may
be endpoints of the actual overlap with B or C; no such endpoint is
discarded.

The complete original V2 torque is
mu*(q_y+s)+nu*(q_y-s)=0. Therefore

    q_y=s*(nu-mu)/(mu+nu), -s<q_y<s,
    t_B=s*(s-q_y), t_C=s*(s+q_y).                       (5)

The actual B is parallel to A, lies beyond its maximum-u side, and
has absolute own-u interval [H_B,H_B+1]. Similarly C has own-uD
interval [H_C,H_C+1], where

    H_B=1-s*d+l*(s+q_y),
    H_C=1-s*d+l*(s-q_y),
    H0=(H_B+H_C)/2=1+s*(l-d).                          (6)

Their unchanged shared means have the same absolute tangential
coordinate in their respective actual frames:

    S_B.w=S_C.wD=K0:=l*d-1+2*s^2.                      (7)

All tangential physical slides of B,C remain arbitrary subject to their
actual containment, nonoverlap and original shared-mean membership.

## 4. Whole actual endpoint bounds and positive tangential centers

Initially H_B,H_C>1-s*d>59/120>0 by (2),(5),(6). Thus the farther
own-normal side of B, respectively C, is its outer side. Its two
endpoints have tangential coordinates differing by one, at least one
of absolute value at least 1/2. Circle containment gives

    (H_B+1)^2+1/4<=R^2=(d+1)^2+1/4,
    H_B<=d,

and likewise H_C<=d. In particular H0<=d, so

    d>=(1+l*s)/(1+s)>191/200.                           (8)

For the strict final bound, write the middle expression as
1-(1-l)*s/(1+s), use 1-l<27/200 and s/(1+s)<1/3.

The lower bound for d in (8) implies K0>0. Indeed

    (1+s)*K0
      >=l-1+2*s^2+s^3
       =s^2*(2+s-1/(1+l))>0.                           (9)

Consider the genuine loaded B2 with its two original neighbors A,N.
In the nonparallel or one-application alternative of the complete
boundary-free loaded-two theorem, its positive radial point lies on
the original AB line and has unchanged w coordinate K0>0. Hence its
full circle resultant has positive w component. If B has one physical
circle corner, its tangential center coordinate is therefore positive.
If B has two physical circle corners, its tangential center coordinate
is zero: its own-u center is H_B+1/2>0, so the tied coordinate can
only be w.

In the distinct-application parallel alternative, that same theorem
gives radial S with its axis u, hence again tangential center zero.
A coincident-application parallel case would give a circle resultant
parallel to u and a positive radial point of w coordinate K0, which
is impossible; it is not omitted from the cover. Thus every original
B mask and force row has

    center_B.w>=0, min_B w>=-1/2.                       (10)

The identical full C2 argument gives center_C.wD>=0 and min_C wD>=-1/2.
It does not assume N is unloaded or boundary. A physically present
second circle corner with zero coefficient remains in the physical-two
case. Both full B2/C2 stars remain intact.

Several convenient strict whole-domain bounds now follow from (2),(6):

    H0>1109/1200,
    H_B,H_C>=2*H0-d>499/600>83/100.                     (11)

For the first, l-d>173/200-61/60=-91/600 and s<1/2.
For the second use the other endpoint's upper bound H_C<=d or H_B<=d.

Every B circle corner has own-u coordinate H_B+1; every C circle
corner has own-uD coordinate H_C+1. Their tangential coordinates
have absolute value strictly less than one, because

    Qstar-(183/100)^2<1.                               (12)

At a unique physical corner that tangential coordinate is positive;
at two physical corners the two coordinates are +/-1/2. In particular
every such tangential coordinate is at least -1/2.

## 5. A whole vertical gap excludes every side-normal N transmitter

The actual whole endpoint rectangles and (10) give

    min_B y>=-s/2+l*H_B,
    max_C y<=s/2-l*H_C.

Consequently their entire strict vertical separation is

    min_B y-max_C y
      >=l*(H_B+H_C)-s
       >(173/200)*(1109/600)-1/2
        =131857/120000>1.                              (13)

This is a separation of all points of both actual squares, not just
their centers or selected applications. Its reserve above one is
11857/120000.

In L135, N is genuinely unloaded of true degree two. Its full force
and torque give exactly the side-normal or diagonal transmitter
alternatives of the physical stress theorem. In the side-normal row
its two unchanged applications, one in B and one in C, differ by
the unit normal vector and have Euclidean distance exactly one.
Their vertical difference exceeds one by (13), impossible.

Thus the complete original side-normal N row is excluded without
choosing a normal direction or shortening either endpoint star. The
actual N remains, and its whole diagonal alternative is retained for
the final exterior-pocket join.

## 6. Both whole original hub pockets have capacity at most one

We first establish the upper V--A--B pocket; reflection gives the
lower C--D--V pocket with exactly the same complete argument.

Use the fixed world vector v=(8,15). Its coefficients in A's actual
frame are

    v.w=8*l+15*s>0, v.u=15*l-8*s>0.

By (10),(11), the whole B has

    min_B v.z
      >=-(8*l+15*s)/2+H_B*(15*l-8*s)
       >(169/20)*(173/200)-707/100
        =957/4000>0.                                  (14)

Here the expression is increasing in H_B; insert 83/100 first,
then l>173/200 and s<1/2. The whole V has

    min_V v.z=8*d-15/2>7/50>0.                         (15)

Every actual circle corner of C is on the other side. In C's actual
frame it is z*wD+(H_C+1)*uD, with |z|<1 by (12). Since
|8*l-15*s|<8, 8*s+15*l>15*(173/200) and H_C+1>183/100,

    v.Z_C<8-(15*173/200)*(183/100)<0.                   (16)

Thus every original positive C circle marker is strictly outside the
positive-v semicircle, while all B and V markers are strictly inside.

Let R_A=q+w+u be the actual outer A corner. Use the occupied strand
from the actual upper V circle corner through P_A, then along the
two A edges P_A--R_A--S_B, and inside B to the actual B circle
marker for that original gap. The circle endpoint at V is its upper
physical corner, whose original coefficient is positive. The entire
strand is in v.z>0: P_A belongs to V, R_A=P_A+u increases v.z,
S_B belongs to B, and the intervening segments are convex.

The original exterior circle arc between those consecutive loaded
bodies cannot contain C's positive circle marker. The arc that leaves
the positive-v semicircle would contain its entire complementary
semicircle, including that C marker. Hence the actual V--A--B gap
uses the arc inside v.z>0. This identifies the whole original gap;
no smaller favorable subarc is substituted.

The complete occupied strand is also strictly outside radius 1/4.
On P_A--R_A its world x coordinate is at least
d-s>91/200>1/4. On R_A--S_B its own-u coordinate is H_B>83/100.
The whole B and V have the same respective strict clearances. The
circle arc has radius R>=2.

These occupied paths may replace center/contact paths for this
geometric winding argument while keeping all original applications
and circle markers fixed: each deformation stays inside its actual
convex body. Every extra's open interior avoids all closed occupied
bodies, so its winding is unchanged. This also handles an original
mean at a shared-overlap endpoint, or an occupied path that follows
part of an actual shared segment. A weak or repeated boundary portion
adds no place for a whole extra to cross.

The new closed path lies strictly in v.z>0 and strictly outside the
quarter disk. The entire quarter disk belongs to the origin's
zero-winding component; compactness gives a positive clearance margin.
Therefore every whole extra assigned to this original pocket has
dist(O,E)>1/4 and is wholly in v.z>0.

Set r=5/4 and let Lambda be the sharp quarter-clear unit arc constant
from bca528af. Every actual contained unit at distance greater than
1/4 has one connected open r-circle arc of length at least Lambda,
and Lambda>pi/4. The whole actual B and V have this clearance and
lie in the same positive-v half-plane. If the pocket contained two
extras, those two extras, B and V would give four disjoint actual
circle arcs inside one semicircle, of total length at least

    4*Lambda>pi.

This is impossible. The whole upper pocket has capacity at most one.
Reflecting all data proves the same full lower-pocket bound.

## 7. A force-free quadrant lemma for a high occupied corner

We record the geometric argument used for emptiness. Let E be any actual
unit contained in the same radius-R disk, R^2<=Qstar, and suppose

    9/10<H<=d<K, K>1,
    E has no point in the open quadrant {X<K,Y<H}.

Then the entire actual E satisfies

    min_E Y>=H.                                       (17)

First, every contained unit has min_E n.z<=d for every unit direction
n. For its center c, the farthest corner gives
R^2>=|c|^2+|c|+1/2, hence |c|<=d+1/2. Its own support
halfwidth in any direction is at least 1/2, proving the claim.

Separation of E from the open quadrant has a separating axis which
is East, North, or an actual E side axis with nonnegative components.
One elementary finite-axis justification is to truncate the quadrant
to rectangles [-L,K] x [-L,H]. The square/rectangle separating-axis
theorem uses only their side axes. Along an unbounded sequence of L,
one of those finitely many directions recurs; its separating orientation
must have nonnegative components, since otherwise its quadrant support
would diverge. The same axis separates from the full open quadrant.
Weak touching is retained throughout.

East separation is impossible, because it would give min_E X>=K>d.
North separation is exactly (17). Consider therefore a strictly
Northeast actual inward E axis n=(c0,s0), c0,s0>0, with c0^2+s0^2=1.
Put t0=(-s0,c0). Write its full actual square as

    E=Z+[0,1]n+[0,1]t0,

where Z is the endpoint of its minimum-n side with smaller Y.
It is the actual minimum-Y vertex. If (17) failed, Z_Y<H, and
avoidance of the open quadrant would give Z_X>=K.

The separating support and the preceding bound give

    n.Z>=c0*K+s0*H, c0*K+s0*H<=d<K.

These imply s0*K>c0*H. Indeed c0*H>=s0*K would give
H*s0>=K*s0^2/c0>K*(1-c0), hence c0*K+s0*H>K.
Consequently

    t0.Z=-s0*Z_X+c0*Z_Y<-s0*K+c0*H<0.

The actual far vertex Z+n belongs to E. Its squared norm is therefore
strictly greater than

    (c0*K+s0*H+1)^2+(s0*K-c0*H)^2
      =K^2+H^2+1+2*(c0*K+s0*H)
      >K^2+(H+1)^2
      >1+(19/10)^2=461/100>Qstar.

The penultimate comparison uses K>H>0 and c0+s0>1. This contradicts
containment, proving (17) for every actual E frame. The final fixed
radius reserve is 1879/6400. No orientation endpoint or side mean
was omitted by this finite-axis cover.

## 8. One whole original hub pocket is empty

Suppose q_y>=0. In A's actual (w,u) coordinates define its outer
corner coordinates

    K=1+q.w=l*d+s^2+s*q_y,
    H=1+q.u=H_B=1-s*d+l*(s+q_y).                       (18)

The actual endpoint bound and (11) give H<=d and
H>=H0>1109/1200>9/10. Furthermore

    K-d=(1-l)*(1+l-d)+s*q_y>0,

because d<61/60<1+l. From (8),

    K>=l*(1+l*s)/(1+s)+s^2
       =(l+s+s^2)/(1+s)>1,                             (19)

whose last numerator surplus is l*(1-l)>0. Thus all the quadrant
lemma's scalar hypotheses hold.

We now prove its whole-unit routing premise for every original upper
pocket extra, rather than assume it from a center position. The occupied
A edge strand P_A--R_A--S_B lies on the two boundary lines of the
open quadrant

    Q0={w-coordinate<K, u-coordinate<H}.

The B spoke lies in u>=H. The straight occupied V spoke from P_A
to its actual upper circle corner lies in w>=K. In fact either
physical V corner has w coordinate greater than K, since the difference
is l-s^2-s*q_y+/-s/2>173/200-1/2-1/4>0.
These straight paths lie in the actual convex B and V and leave all
force application points unchanged.

Every actual C circle corner is inside Q0. To check this for all
physical masks, write it as z*wD+(H_C+1)*uD. Set k=l^2-s^2>1/2.
By (10),(12), -1/2<=z<1 and H_C+1>183/100. Its A coordinates are

    w-coordinate=k*z-2*l*s*(H_C+1)<1<K,
    u-coordinate=-2*l*s*z-k*(H_C+1)
       <=l*s-k*(H_C+1)<1/2-(1/2)*(183/100)<0<H.

On the containing circle, the complement of Q0 is the union of the
two caps w>=K and u>=H. It is one connected arc, because K,H>0
and their actual A corner (K,H) is inside the circle. The circle arc
between the B and V markers which leaves this connected cap union
contains the whole complementary Q0 arc, including C's positive
circle marker. Therefore the original consecutive B--A--V exterior
arc is wholly outside Q0.

The complete occupied loop for that original pocket is outside Q0.
The set Q0 is connected and unbounded and contains O, so its winding
with respect to this loop is zero. The occupied-body homotopy from
Section 6 preserves every extra's nonzero pocket winding, including
shared-overlap endpoints and weak junctions. Hence each whole such
extra E avoids Q0. An E boundary point in the open Q0 would also
give nearby interior points there, so the statement is for its entire
closed unit.

The quadrant lemma now forces min_E u>=H. The actual B already has
min_B u=H. Both B and E would therefore have their entire r=5/4
arcs in the cap u>=H. Since H>9/10,

    H/r>18/25>1/sqrt(2),

so that cap has angular length strictly less than pi/2. Both units
have distance greater than 1/4 and therefore arcs of length at least
Lambda>pi/4. Their disjoint arcs cannot fit in that cap. Thus the
whole upper original pocket is empty when q_y>=0.

Reflection proves the whole lower pocket empty when q_y<=0. At
q_y=0 both arguments apply. Combined with Section 6, the two
original hub pockets together have capacity at most one in every
actual force-ratio and physical-mask case.

## 9. Original outer ordering, whole-extra allocation and final joins

Use the original planar physical incidence graph, keeping its real
shared contact nodes and original circle markers. The rim order is
V--A--B--N--C--D--V, with the positive chord AD. The original
outer loaded-body order is V,B,C in L135 and V,B,N,C in L1345,
up to the whole-data reflection already used. These are the original
consecutive-load gaps of that embedding. No chord is deleted.

The strict half-plane and quadrant proofs above identify the original
V--A--B and C--D--V gaps: each uses the original endpoint markers,
and the complementary circle arc contains the other original positive
load C or B. Thus they concern the whole actual exterior pockets,
including every physical endpoint mask, not a chosen pair of small
regions. Every loop deformation stays in its actual occupied squares
and fixes the original contact applications and circle markers.

The complete chorded-hexagon central theorem at 0b787eae gives capacity
one for the entire central free union. It retains the genuine empty
triangle A--V--D and the complementary pentagon through B,N,C. A
whole extra cannot cross any closed occupied body or incidence strand.
At weak junctions, label a compact inner square by its actual face,
use sufficiently small compatible routings, then exhaust its open
interior. Taking closures keeps the whole unit on that same face side.
Additional zero-weight physical contacts only subdivide these regions.

Faces between two circle markers of the same physical two-corner body
also supply no extra units. Their cap is beyond that body's outer
radial side, whose support is d+1>d; any contained unit has minimum
support at most d by Section 7. This includes the two positive V
markers. Individual zero coefficients do not introduce an uncounted
physical region.

Therefore every one of the three original completion units is assigned
to the central union, one of the two whole hub pockets, or the remaining
B-to-C exterior route through the actual N.

### 9.1. Genuinely loaded N: original D02.L1345

B,N,C are physically boundary units. The real BN and NC contacts
therefore give empty original direct boundary-contact pockets by the
complete theorem b61b0dec, with all original means and masks retained.
No unloaded-transmission equation is used at N; its full original
circle force, two pair forces and torque remain.

The central union has capacity one and the two hub pockets together
have capacity at most one. Every other original exterior region is
empty. At most two whole extras can fit, contradicting the three
original extras. This excludes the entire stated feature in L1345.

### 9.2. Genuinely unloaded N: original D02.L135

Section 5 has already excluded the complete side-normal alternative
using the actual applications' unit separation. The genuine N must
therefore be a diagonal transmitter. Apply the full original-spoke
diagonal-pocket theorem at the explicit recovered path

    recovered_variants/parallel_diagonal_2026_10_29/FULL_PARALLEL_RETURN_STARS_DIAGONAL_CHANNEL_EXTERIOR_POCKET_EMPTY.md
    SHA256 60aafee1c86633dd2a384d703425d9b60369f0b522c7ef0f85fe5eac4472b078.

The actual channel is B--N--C=5--4--3. Its endpoints are genuinely
loaded true2 bodies. Their entire nonchannel force groups each consist
of the single original BA or CD force, here with the actual shared-side
mean (4). The original component has exactly three positive loads V,B,C;
the endpoints are consecutive along this actual exterior route. The
complete original force balance, selected normal conventions, compatible
diagonal avoidance and physical embedding remain.

That full theorem covers nonparallel finite proper concurrence,
coincident applications, the radial parallel endpoint, both physical
circle masks, individual zero weights and every actual shared mean.
Its whole original-spoke repair and analytic cap conclusion therefore
make the entire actual B--N--C diagonal exterior pocket empty here.
The explicitly recovered cap variants and analytic replacements are
resolved by the bundle manifest; no older root basename is substituted.

The central union again has capacity one, and both hub pockets together
have capacity at most one. All remaining exterior regions are empty.
The same contradiction to three whole completion units excludes the
entire stated feature in L135.

## 10. Exact inputs, arithmetic and review boundary

| Complete operative source | SHA256 | Exact use |
| --- | --- | --- |
| LOADED_PARALLEL_FULL_STAR_WITH_DISTINCT_NEIGHBORS_FORCES_RADIAL_S_2026_10_29.md | f0e7b44a8d7e0eff5654384bf20bb5a99c3809d57a92bbb16afba6ee7ac1c96c | Entire original parallel V2 entry, all masks and signs |
| PARALLEL_ROOF_TILTED_HUB_DISTINCT_APPLICATIONS_AND_FULL_RETURN_OWNER_COVER_2026_10_29.md | ce5219a2ee26f86a57a7e237582858f64f6b05646b600be52e73de7b2f43ab6a | Both actual true3 hubs; free AD forces both genuine shared returns |
| PARALLEL_RADIAL_ROOF_WITH_ANY_ALIGNED_HUB_COMPLETE_D02_FEATURE_EXCLUSION_2026_10_29.md | 5089e790d324a645db72b85d9ecdf54a1e1d90f638d7a4ac4b48f6e4dca1bb37 | Only the complementary aligned-hub branch in the complete free-AD union |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Full original forces, torques, actual means, strict convention and genuine N2 width dichotomy |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Exclusion of the actual opposite AD vertex by the whole other-hub span |
| LOADED_TWO_APPLICATION_FULL_STAR_BOUNDARY_FREE_CONCURRENCE_DICHOTOMY.md | 3808b2b767a9e15c7270b50c4fbbb434ae0d69fe42c567d4da01f7d167f7fa78 | Whole actual loaded B2/C2 proper, one-application and parallel cases; no neighbor-boundary premise |
| SHARP_QUARTER_CLEAR_RADIUS_FIVE_QUARTERS_ARC_AND_INTERVAL_CAPACITY.md | bca528af5320cc8314839eb0d53cf6f15ec381ac42d5bd353f62a27a47101f67 | Whole force-free connected arc bound Lambda>pi/4 for every actual quarter-clear unit |
| CHORDED_HEXAGON_CENTRAL_CAPACITY_ONE.md | 0b787eae6efe36d2ca6c40dbb079d3262192125fffe58026bacbfd657d1a9a34 | Whole original central free union, with the actual positive chord retained |
| CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md | b61b0dec7ded00984c687e353fd3f3bfb5a5a7ade45d87d69aaeade09f23d80b | Whole original direct boundary-contact pockets and physical corner order |
| recovered_variants/parallel_diagonal_2026_10_29/FULL_PARALLEL_RETURN_STARS_DIAGONAL_CHANNEL_EXTERIOR_POCKET_EMPTY.md | 60aafee1c86633dd2a384d703425d9b60369f0b522c7ef0f85fe5eac4472b078 | Entire original L135 diagonal N pocket, all endpoint stars, masks and original spokes |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | Actual physical embedding and retained original incidence/weak-contact routing |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Exact original D02 roles, full stars/load masks, circle order and all three extras |

The exact preceding independent owner-cover review is
bbc80f3996d8d6b78e56ccc04d6ceeb422672d02b4bf0b9d9556c10407b59827.
The complete aligned-hub source has separate independent review
d25e0351365b74506b82830292ea194346033106506f7912023e285080ac961f.
The recovered diagonal source's complete independent review is
3c616db0e9073525471d84f979c08f6c16f8dc24e392e899430a532c447d22f8.
Their exact source bytes and scopes remain unchanged.

The new actual symmetric chart, full shared means, loaded-endpoint
center signs, whole vertical separation, both full pocket capacities,
quadrant lemma and all original allocation joins require separate full
independent review. The core arc proofs use whole actual units, not
center-only assignments, and no numerical pose or finite packing
certificate is an input.

Every original square, force, selected normal, physical contact, actual
application, shared mean, physical circle corner and individual zero
coefficient remains. No original fine or parent flag is changed by this
source alone. No Lean/Lake run, CI/workflow, remote mutation, merge or
authoritative metadata edit was used.
