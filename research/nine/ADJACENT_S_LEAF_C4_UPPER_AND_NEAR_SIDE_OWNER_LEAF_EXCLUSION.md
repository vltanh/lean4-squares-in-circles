# Upper and near-side genuine leaves at the owned root of the adjacent-S C4

Date: October 27, 2026.

**Status: complete hand local exclusions and complete further one-owner
feature reduction, submitted for full root and separate independent
review.** Sections 1--4 export their exact local scopes to callers with
parallel root frames as well. Section 5 supplies the additional bound
needed in the one-owner caller. No whole high LCD.SS family, fine gate
or coarse cell is claimed closed.

Keep all nine original units and the exact compatible selected component

    AB,BC,CD,DA,AL,BM,
    A3,B3,C2,D2,L1,M1.

The actual leaves L,M are S, the actual roots A,B are clear, and C,D
are positively loaded physical boundary units. Work in

    d=sqrt(R^2-1/4)-1=1+epsilon,
    0<epsilon<1/60,       R^2<=1105/256.

Suppose A owns the original AB normal. Normalize it to East, and
reflect vertically so the unchanged directed cycle moment is positive.
Then the original real chart and application are

    A=[h-1,h] times [a,a+1],
    P_AB=(h,-k),       k>0,       -epsilon<=h<=epsilon.       (1)

The support bound is the accepted common-domain theorem. Every actual
side-mean endpoint is allowed in Sections 1--4. B lies wholly in x>=h
and retains its real S leaf. No parallel B frame or small k is assumed.

## 1. The original circular order and its orientation

The four physical boundary bodies have counterclockwise circular order

    L, M, C, D.                                             (2)

This holds for their centers and for every choice of their circle
corners. Here order means increasing lifts, not a prescribed short
arc between nonadjacent bodies.

Retain the compatible arbitrarily small physical routing and fixed
center-to-circle spokes of PHYSICAL_BODY_GRAPH_UNCROSSING.md,
Sections 5--6. The selected C4 is a Jordan cycle. Both genuine
boundary leaves attach on its exterior side: otherwise their bridges
and disjoint circle spokes could not reach the containing circle.
The exterior face walk therefore marks L,M,C,D or its reversal.
A thin regular neighborhood of the routed graph has an outer Jordan
boundary with that same marked order. The remaining disjoint spoke
pieces connect it to the containing circle and preserve order by
Jordan separation. This is the full argument of Section 5 of
OPPOSITE_C4_TWO_S_LEAVES_COMPLETE_EXCLUSION.md, with the present
adjacent-leaf exterior face walk. All original junctions and side
means remain.

The directed CD moment equals the positive AB moment mu*k.
Lemma 1.1 of FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md therefore puts C
followed by D in counterclockwise minor-circle order. The actual
angular-neighbor theorem makes that minor center arc empty of other
boundary centers. Thus it is the consecutive C,D pair in the marked
order, fixing the reversal in (2). The corner/center order theorem
in CIRCLE_CONTACT_ANGULAR_ORDER.md gives the same order for every
actual corner choice and for the centers. A radial S center has its
actual genuine leaf direction.

Let phi_L,phi_M,theta_C,theta_D be increasing center-angle lifts in
(2). For any actual D circle corner with the corresponding lift phi_z,
the strict 40-degree center separation and strict 15-degree corner
bound give

    theta_C>phi_M+2*pi/9,
    theta_D>theta_C+2*pi/9,
    phi_z>theta_D-pi/12>phi_M+13*pi/36.                    (3)

No corner weight is used.

## 2. The upper-left A leaf is impossible for every B frame and mask

Suppose the real leaf application is the strict upper-left vertex

    d*e_L=(-X,v),       X=1-h,
    X^2+v^2=d^2,       v>0.

The original support bound gives

    X>=1-epsilon>59/60,
    0<v<=2*sqrt(epsilon)<13/50,
    3*pi/4<phi_L<pi.                                    (4)

In the actual West/North frame this is precisely the shallow tilted
S chart U=X,V=v. The complete arbitrary-degree physical theorem
SHALLOW_TILTED_S_ROOT_BOUNDARY_NEIGHBORS_ONE_SIDE.md applies to D.
It says in world coordinates that every original D circle corner z
satisfies (v,X) dot z<0, equivalently det(e_L,z)>0. Its lifted angle
in (2) must therefore satisfy

    phi_L<phi_z<phi_L+pi<2*pi.                           (5)

The next translate of this open semicircle starts beyond phi_L+2*pi
and cannot contain the corner between M and the next L in (2).

The genuine M midpoint belongs to B, so d*(e_M)_x>=h>=-epsilon.
If (e_M)_y>=0, its ordinary angle is in [0,7*pi/12), because
epsilon/d<1/60<sin(pi/12). By (4), its increasing lift after L is
at least 2*pi, contrary to (5) and (2). If (e_M)_y<0, its lift
after L instead satisfies phi_M>17*pi/12. Equations (3) and (5)
then give

    7*pi/4<16*pi/9<phi_z<2*pi.

Thus z_x>R/sqrt(2). Every original AD point Q belongs to A and has
Q_x<=h<=epsilon. The two actual D points would satisfy

    |z-Q|>R/sqrt(2)-epsilon
            >29/20-1/60=43/30>sqrt(2).                  (6)

Here 17/8>(29/20)^2 and (43/30)^2>2 give the strict rational reserves.
This contradicts the actual diameter of D.

The whole upper-left feature is excluded without B alignment, a
nonparallel root-pair hypothesis, a unique circle mask or a small k.
Every physical circle corner and all zero weights remain. Only the
original common nonzero cycle moment fixes the order.

## 3. A unique-corner owned boundary tip has a radial cap

Let T be an actual positively loaded degree-two unit with a unique
physical circle corner Z, and with another actual boundary neighbor.
At its first contact retain the original point Q and normal n directed
into T. Assume T owns n, and put

    u=Q dot n>0.

Then its actual radius satisfies

    R<=|Q|+|Q|/u.                                       (7)

Indeed its n interval is exactly [u,u+1]. Since u>0, each maximum-n
corner has larger norm than the corresponding minimum-n corner.
Therefore Z dot n=u+1. Retain the full degree-two equations:
Lemma 2.1 of TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md gives their
positive proper radial concurrence

    q=Q+rho*n=lambda*Z,       rho>=0,       lambda>0.

Its n component gives lambda>=u/(u+1). In an orthogonal tangent
direction t, its unchanged t component is lambda*(Z dot t)=Q dot t.
Consequently

    |Z dot t|<=(u+1)*|Q dot t|/u,
    R<=(u+1)*sqrt(1+(Q dot t)^2/u^2)
       =|Q|+|Q|/u.

This retains the original other contact mean and a zero proper-distance
endpoint. The unique physical corner and the actual boundary neighbor
are essential; an individual zero in a two-corner mask is not substituted
for uniqueness.

## 4. Near-side downward A leaves are impossible when k<167/500

Suppose C,D each have a unique physical corner, both root nonleaf
pairs are nonparallel, and

    k<167/500.                                          (8)

Use the same compatible certificate of
ADJACENT_S_LEAF_C4_ALL_NONPARALLEL_PAIRS_SIDE_OWNER_SELECTION.md.
It makes every actual cycle normal owned by a side of an endpoint.

Suppose A's genuine leaf is its strict lower-right vertex or owned
South side. Write its actual point as

    d*e_L=(eta,-v),
    v>1,       0<=eta<=h<=epsilon,
    a0=v-1 in (0,epsilon],       X=1-h.

For the strict vertex eta=h>0 and v=sqrt(d^2-h^2). For the owned
side eta=0,v=d; h>=0 because that real side contains x=0.
A's top is -a0, and its original AB mean has k>=a0.

The full A3 force equation forces its AD normal strictly Northwest:
n=(-a,b), a,b>0, a^2+b^2=1. Its actual point is Q=(-X,-a0).
This is a strict A vertex, so the owner supplied by the selection
theorem is D. If the original AD magnitude is nu and the leaf
magnitude is alpha, the full A3 equations give exactly

    alpha*v/d=nu*b,
    mu=nu*(a-b*eta/v),
    a*(k-a0)=b*(X+k*eta/v).                             (9)

The right side is positive, so k>a0 even if the original AB mean
was allowed at that endpoint. No strict-mean premise was added.

For the unsigned angle delta between Q and n, (9) gives

    tan(delta)
      =k*(X+a0*eta/v)
          /[X^2+a0^2+k*(X*eta/v-a0)].                   (10)

The denominator is positive by the following bound. If eta=h then
X+a0*eta/v=1-h/v<=1; if eta=0 it is X<=1. Hence (8) gives

    denominator >=(59/60)^2-(167/500)(1/60)>0,
    tan(delta)<7/20.

The last comparison has exact reserve

    (7/20)*[(59/60)^2-(167/500)(1/60)]-167/500
        =1117/450000>0.

Furthermore

    |Q|^2<=1+epsilon^2<(1001/1000)^2,
    |Q|/(Q dot n)=sqrt(1+tan(delta)^2)<53/50.              (11)

The first reserve at epsilon=1/60 is 15509/9000000. The second
uses 1+(7/20)^2=449/400<(53/50)^2.

The real D is a unique-corner loaded D2 whose other neighbor C is
physical boundary. Apply (7) at the unchanged owned AD contact:

    R<1001/1000+53/50=2061/1000<sqrt(17)/2.

The last squared reserve is 2279/1000000. This contradicts the
strict-high radius and excludes both near-side downward leaf types.

The local calculation (9)--(11) requires actual D ownership and (8),
but no B tilt, AB singleton, C-D mean or B-D contact. A caller that
already proves the original D-owned normal can use it without the
separate all-cycle selection. It retains the actual A3 and D2 degrees.

## 5. The full one-owner caller supplies (8) in both B leaf types

Return to exactly one side owner of AB. The complete feature source
ADJACENT_S_LEAF_C4_ONE_OWNED_ROOT_LEAF_REDUCTION.md leaves the
actual frame f=(c,s), j=(s,-c), c,s>0, c^2+s^2=1, and two B leaf types.
For its strict lower adjacent leaf, |P_AB|^2<241/3600 already gives
k<167/500.

For its owned far-j leaf, the unchanged chart in (j,f) coordinates is

    B=[epsilon,d] times [-w,T],       T=1-w,       0<=w<=1,
    n_BA=(-s,-c),       d*e_M=(d,0),
    h=epsilon*s-w*c,       k=epsilon*c+w*s.               (12)

For the proposed near-side downward A leaf, h>=0, so

    w*c<=epsilon*s.                                    (13)

Write the original B-to-C force as nu*m, its mean as Q, and its
genuine leaf force as beta*e_j. The full f equation is
nu*m_f=mu*c>0. Thus the complete BC support cover is North,
strict Northwest or strict Northeast. The exact means must be
kept separate in the original moment about P_AB:

* For owned North, Q=(epsilon+ell,T), 0<=ell<=1.
  The true equations give c*ell=w*s, hence w<=c/s.

* At strict Northeast, Q=(d,T). The true equations give
  nu*T*m_j=mu*(c-w*s). Since T>=0 and m_j>0, again w<=c/s.

* At strict Northwest, Q=(epsilon,T), m=(-a,b), a,b>0.
  Its original equations give nu*T*a=mu*w*s and nu*b=mu*c.

In either of the first two complete features, (13) implies w^2<=epsilon.
Thus k^2<=epsilon^2+w^2<61/3600, sufficient for (8), with the entire
North mean retained.

For Northwest, physical boundary status gives T>0, and its full
equation gives w>0 and

    b/a=(c/s)*T/w.                                     (14)

Both actual leaf directions now have nonzero negative world vertical
components. The unique/unique all-cycle-owner selection applies, so
C owns this strict BC normal. If w>=1/3, (13) gives c/s<1/20 and
T<=2/3. Equation (14) then gives b/a<1/10<2/17 and a+b<19/17.
The real unit has its full actual side-mean chart

    C=Q+[0,1]m+[-z,1-z]t,
    t=(b,a),       0<=z<=1.

Every actual corner Z therefore satisfies

    |Z|^2<=epsilon^2+T^2+2+2(a+b)(epsilon+T)
       <1/3600+4/9+2+2*(19/17)*(1/60+2/3)
        =243097/61200<17/4.                            (15)

The last reserve is 17003/61200. This contradicts the physical
boundary status of C. Thus w<1/3, and (12) gives

    k^2<=epsilon^2+w^2<401/3600<(167/500)^2,             (16)

with reserve 47/281250. This proves (8) in the remaining whole type.
Only actual C ownership and containment entered (15); its circle
weight and other equation were not changed.

## 6. Exhaustive remaining genuine-leaf features at A

An East owned leaf would require h=d. A North owned leaf would put
all A points above y=epsilon. Both contradict (1). A strict upper-right
leaf has y=sqrt(d^2-h^2)>1, whose distance in height from (h,-k)
exceeds the unit side length. Section 2 excludes the upper-left leaf.
Sections 4--5 exclude the lower-right and South-owned features in the
complete unique/unique one-owner caller.

These four vertices and four axes are exhaustive. The remaining A
types are precisely:

* A strict lower-left genuine application (-X,-v), with
  X=1-h, X^2+v^2=d^2, h> -epsilon, and 0<k<v<13/50.
  The strict k<v uses the actual relative-interior A-side contact
  proved in the original one-owner feature source.

* An owned West leaf, with h=-epsilon and the original y interval
  containing zero. Its full A3 equation makes AD horizontal.
  A West neighbor beyond the same far support would be the real
  radial S leaf itself, by the sharp contained-unit support equality
  case. Thus the actual AD normal is East. If its original mean is
  (h,y_D), its full moment is nu*y_D=mu*k>0.
  Boundary status gives y_D>647/1000; the shared actual A side gives
  k+y_D<=1, so k<353/1000. No D alignment is inferred.

These two A features, paired with the two original B features, still
require their whole exits. The proof assumes neither a grid nor the
physical hypotheses of a completion theorem. The two-corner physical
masks and the separate parallel-root domain remain at their exact
scopes. All nine units, full forces, original means and zero weights
are retained. No false triangle, normal reselection after extraction,
numerical pose, compilation, CI, remote action or metadata edit is used.
