# Adjacent hub vertices owned by the two boundary tips have exterior-pocket capacity at most one

Date: October 28, 2026 UTC. Author: cycles continuation.

**Status: complete proposed uniform hand theorem, submitted for full
root and independent review.** The new argument uses two whole-domain
arc estimates, the full actual endpoint equations, and the original
occupied crosscut. It proves a capacity bound for an entire endpoint
owner feature. No original graph/load row is declared closed.

## 1. Full original setting and conclusion

Put Q=1105/256, and work in 2<R<=sqrt(Q). Keep the same actual
packing, circle origin, independent unit frames, physical masks,
positive forces, original application means, and all completing
squares. Suppose one whole positive component has the form

    H, B_1,...,B_k, 3<=k<=6;
    B_i B_(i+1), 1<=i<k;
    H B_1, H B_k, and any subset of H B_i for 1<i<k.

H is unloaded; every B_i has positive total circle load. The two
endpoints V=B_1 and T=B_k have their true positive degree two.
All internal bodies keep their actual degrees and all their
original forces. The actual exterior order is
H,B_1,...,B_k,H.

Assume both physical H-endpoint intersections are singleton
points in the relative interiors of sides of their respective
boundary tips V,T, and that these points are adjacent actual
vertices of H. Keep all internal spoke owners, free normals,
side means, physical circle masks, and individual zero weights.

**Theorem.** The actual closing exterior pocket through H between
T and V has unit capacity at most one.

The theorem does not require spokes to all internal B_i.
It does not assert anything about central faces by itself.
For the original D02.L01345 family, Section 10 joins it to
the complete central and direct-pair pocket allocation and
excludes this entire adjacent-tip-owned endpoint feature.

## 2. Actual top-side chart and both complete endpoint masks

Each endpoint normal is strict in its H vertex cone: an axis
normal with the tip point in a relative side interior would
give positive shared length, contrary to the singleton premise.
The short occupied arc between the adjacent vertices would
place every H force in the same closed upper half-plane.
The full H force balance rules it out.

Rotate and reflect the unchanged physical configuration so the
outer H arc is the top side, with

    P_L=(x-1/2,h)=(-X_L,h),
    P_R=(x+1/2,h)=(X_R,h),
    X_L+X_R=1.

Section 5 of GENERAL_SINGLE_HUB_BOUNDARY_PATH_POCKET.md,
using all original H moments and the two genuine endpoint
equations, gives

    h>0, |x|<1,
    det(P_L,n_L)>0, det(P_R,n_R)<0.                 (1)

Its complete outer-pocket theorem also applies. In particular
every whole extra in this pocket has distance strictly greater
than 1/4 from O. The moment signs in (1) retain every original
boundary-edge mean and every endpoint physical circle mask.

We give the left endpoint; reflection gives the right one.
Write

    P=(-X,h), n=(-b,a), k=Jn=(-a,-b),
    a,b>0, a^2+b^2=1,
    V=P+[0,1]n+[-sigma,1-sigma]k, 0<sigma<1,
    N=P.n=bX+a*h, K=-P.k=b*h-a*X>0.                (2)

Because X> -1/2 and h>0,

    N> -1/2.                                      (3)

The genuine all-mask degree-two properness lemma applies:
V's other positive neighbor B_2 physically touches the circle.
It gives the actual concurrence

    q=P+ell*n, ell>=0,

as a positive multiple of the full circle resultant. Thus
that resultant has strictly negative k component, since
q.k=-K<0. The own n-center coordinate N+1/2 is strictly
positive by (3). Consequently the physical far corner is

    Z=(N+1)n-Z_0*k, Z_0=K+sigma>=1/2,
    R^2=(N+1)^2+Z_0^2,
    c_V=(N+1/2)n-(Z_0-1/2)k.                       (4)

This covers the unique mask and the entire physical two-corner
mask Z_0=1/2, including an individual zero coefficient. In
the latter case the negative-k circle corner has positive
weight; both physical corners remain.

The negative-k corner in (4) is the gap-facing physical
circle corner. Its coordinates also give

    (c_V)_y=a*(N+1/2)+b*(Z_0-1/2)>0,
    Z_y=h+a+sigma*b>h.                             (5)

The reflected endpoint has the identical strict height
properties. No assumption that either X_L or X_R is positive
has been made.

## 3. The actual occupied crosscut puts the whole pocket above h

Choose the gap-facing physical corners Z_L,Z_R from (4).
The original endpoint and port order, with the positive
global balance of the original boundary resultants, gives
their closing minor circle arc in the upper half-plane.
This is the occupied-crosscut and closing-lift argument
in Section 2 of the general single-hub pocket theorem,
with its vector v=(0,1). Here the resultants themselves
have positive y components because q_y=h+ell*a>0.

The gap-facing negative-k corner is the clockwise extreme
at the left endpoint, and its reflection is the
counterclockwise extreme at the right endpoint. Thus the
chosen closing circle arc is the one between these actual
gap-facing corners. Each corner has height greater than h
by (5), and the whole upper minor circle arc has height at
least the smaller endpoint height. It therefore lies above h.

Replace only the barrier path inside V by P_L--Z_L,
and inside T by P_R--Z_R. Replace the two center/contact
segments inside H by its top side P_L--P_R. These
homotopies stay in the unchanged actual closed units and
avoid the interior of every extra. No application or mean
in any equation is moved.

The resulting occupied crosscut is simple: V,T are
closed-disjoint nonconsecutive boundary path bodies;
each segment leaves H only at its singleton endpoint;
and its open parts lie in their respective units.
Together with the actual closing circle arc, it is a
Jordan boundary. All of it has y>=h, and its intersection
with y=h is exactly the segment P_L--P_R.

Every original extra in the closing pocket has the same
nonzero winding about this boundary, because the preceding
homotopy avoids its open interior. Taking closures shows
that its whole square lies in the bounded Jordan region's
closure. In particular

    every such whole extra lies in {y>=h}.          (6)

Further weak physical contacts can subdivide this region
but cannot move an extra through the occupied crosscut.

If the pocket contains even one extra, its vertical
projection width is at least one. Thus

    h<=R-1<13/12<5/4.                              (7)

We use (7) only while excluding the presence of two extras.

## 4. Two exact arc estimates on the same radius-5/4 circle

Put

    r=5/4, beta=arctan(5/16), chi=arctan(16/15).

### 4.1. Every boundary unit has a closed centered beta half-arc

Every actual boundary-unit center has radius u with

    r<u<91/60=:M.

The lower inequality follows from
u>=R-1/sqrt(2)>2-3/4=r. The upper follows from
u^2+u+1/2<=Q and the exact positive reserve
M^2+M+1/2-Q=31/57600.

Now cos(beta)=16/sqrt(281)>477/500, with positive
squared reserve 64351/70250000. Since
u^2+r^2-2ur*cos(beta) increases with u>r,
the distance squared from the center to any point
of the entire closed centered r-circle arc
of half-angle beta is less than

    M^2+r^2-2Mr*(477/500)
      =1/4-161/36000 <1/4.                         (8)

The entire closed arc is therefore in the actual
open radius-1/2 incircle, hence in the square's
open interior. All physical boundary masks are
included; no circle-force direction replaces the
actual center direction.

### 4.2. A sharper complete quarter-clear arc below R=41/20

Let E be any actual unit contained in D_(41/20)
with dist(O,E)>1/4. Its open interior meets
|z|=r in one connected arc of length

    strictly greater than chi.                    (9)

Here is a complete proof of the strengthened constant.
Choose signs and order of E's actual own axes and write

    E=[A,a] x [B,b], A=a-1, B=b-1,
    a>=b>=1/2, q=a^2+b^2<=1681/400.

First suppose a>r. Then

    1/4<A<1, -1/2<=B<1/2,
    A^2+B^2<5/4<r^2.

Put s=sin(chi)=16/sqrt(481) and
c=cos(chi)=15/sqrt(481). We have 7/10<s<3/4.
For fixed q the expression

    E_0=A^2+B^2+2sAB

is the convex quadratic

    (1-s)q+s*(a+b)^2-2(1+s)*(a+b)+2(1+s).

Enlarge to the complete fixed-q interval a>=b>=1/2.
At b=1/2, with A_0=sqrt(q-1/4)-1 in (1/4,1),

    E_0<A_0^2+1/4-(7/10)A_0<=11/20.

At a=b=v, enlarge to 3/4<=v<=29/20.
The upper bound follows from
(29/20)^2-1681/800=1/800>0. Hence

    E_0=2(1+s)(v-1)^2<567/800<r^2*c^2,

where the last exact reserve is 8523/384800.
Convexity proves E_0<r^2*c^2 throughout the original
inner-face domain.

Write

    alpha=arccos(A/r),
    zeta=arcsin(B/r),
    eta=arcsin(min(b/r,1)).

The exact closed inner-circle intersection is
[zeta,min(alpha,eta)]. The inequality just proved
is equivalent to

    (A+sB)^2<c^2*(r^2-B^2),

and implies A<r*cos(zeta+chi), irrespective of
the sign before squaring. Since
0<zeta+chi<pi/2, it follows that alpha-zeta>chi.

The other possible interval length is a unit-strip
length. For b<=r it is at least 2arcsin(2/5)>chi.
The strict comparison follows from

    cos(chi)>17/25=cos(2arcsin(2/5)),
    225/481-(17/25)^2=1616/300625>0.

For b>r, eta=pi/2 and |zeta|<pi/6 give an even
larger length. Thus the full open-interior arc is
connected and has length greater than chi.

Suppose instead a<=r. Central clearance forces

    0<B<=A<=1/4, k_0^2=A^2+B^2>1/16.

The exact closed-circle interval is

    [max(arccos(a/r),arcsin(B/r)),
     min(arccos(A/r),arcsin(b/r))].

Its two opposite-face differences have the same
strict strip bound above. The inner-inner difference
is at least pi/2-2arcsin(1/5), whose sine is
23/25>sin(chi).

For the outer-outer difference, fix k_0^2 and vary
B=sqrt(k_0^2-A^2) from the diagonal to the actual
ordered pair. The derivative has the sign of

    (A-B)*[(A+B-1/4)^2
             +(k_0^2-1/16)*(A+B+1)]>=0.

This is the same complete positive-term derivative
comparison as in the full-Q cap source; continuity
retains a=r or b=r. Its minimum is therefore
strictly above

    L_0=2arcsin((4+1/sqrt(2))/5)-pi/2.

Both L_0 and chi belong to (0,pi/2), and

    sin(L_0)=8(1+sqrt(2))/25
       >96/125>3/4>sin(chi).

Thus all four candidate interval lengths exceed chi.
This completes every outer-face and transition case.

Finally |c_E|>3/4 from its nearest-point supporting
cap and the unit halfwidth, while |c_E|<91/60 from
containment. Consequently |r-|c_E||<1/2, so the
radial center point lies in the actual incircle and
in the unique open arc just proved. This completes
the entire proof of (9).

For R>=41/20 we use the already accepted full-Q
cap theorem: every quarter-clear unit has a connected
open radius-r arc of length strictly greater than
pi/4. Both estimates concern the same actual r circle.

## 5. An outside endpoint port cannot turn its center ray into the pocket

This geometric fact prevents a hidden escape through
the bottom of the cap-circle interval. Work under (7),
and consider the actual left endpoint chart (2).

Suppose |P|>=r. Since X> -1/2, if X<=0 then

    |P|^2<1/4+(13/12)^2=205/144<25/16=r^2,

a contradiction. Therefore X>0 and N=bX+a*h>0.

The exact center determinant is

    det(P,c_V)=K/2+(1/2-sigma)*N.                   (10)

If it were negative, then
sigma>1/2+K/(2N). Since sigma<1, this implies K<N.
As N^2+K^2=|P|^2>=25/16,

    N>5/(4sqrt(2))>7/8, sigma>1/2.

The actual far-corner equation (4) would then give

    R^2
      =|P|^2+2N+1+2K*sigma+sigma^2
      >25/16+7/4+5/4
      =73/16>Q,                                   (11)

whose final reserve is 63/256. This is impossible.
Thus det(P,c_V)>=0.

Both P and c_V have positive height; P is in the
upper-left quadrant. Equation (10) therefore means
the center direction is no farther into the closing
gap than the direction of P. In particular

    if |P_L|>=r, its radial center point on |z|=r
    has height at most h and lies on the left side;
    if |P_R|>=r, its reflected radial center point
    has height at most h and lies on the right side. (12)

Equality |P|=r and a zero determinant remain allowed.
No concurrence point is being used as a physical
barrier in this argument.

## 6. Complete routing of each whole extra arc into one endpoint gap

We give the angular-order and crosscut details.

The two actual endpoint centers have positive heights
by (5). Write their upper-half-plane angles as
theta_L,theta_R. They have the same left/right order
as the gap-facing outer circle corners:

    0<theta_R<theta_L<pi.                           (13)

One direct justification, without assuming radial
visibility of the pocket, is as follows. By (8), the
actual point r*c/|c| is inside each endpoint square.
Join it by a straight segment inside that square to
its gap-facing circle corner Z. The segment stays in
the upper open half-plane. It also stays strictly
outside the radius-r circle except at its initial
point: for any actual far circle corner,

    Z.c/|c|=|c|+(|c.e_1|+|c.e_2|)/(2|c|)
            >=|c|+1/2>r.

Every positive convex combination therefore has
projection on c/|c| greater than r. The segment
meets the outer circle only at Z by strict convexity.
The two segments lie in closed-disjoint V,T, so
are disjoint crosscuts of the upper half-annulus.
Two disjoint crosscuts between its inner and outer
semicircles preserve endpoint order (close either
one with the corresponding boundary arcs and use
the Jordan separation theorem). The outer corner
order from Section 3 proves (13).

Put theta_h=arcsin(h/r), which belongs to (0,pi/2)
by (7), and let

    I=(theta_h,pi-theta_h).

This is precisely the angular interval on the r
circle above y=h. Every point of the open-interior
arc of any whole pocket extra lies in I by (6).

Each endpoint square has distance at least
R-sqrt(2)>1/4 from O. The full-Q cap theorem gives
its one connected closed-circle interval and
corresponding open-interior interval, containing
its radial center point. Its whole angular shadow
lies in a strict semicircle because it is convex
and has positive distance from O. Consequently
its intersection with the upper semicircle, or
with I, is connected. The two endpoint intervals
are disjoint at every open-interior point; in
particular neither can contain the other's radial
center point.

First prove that no pocket extra's open-interior
arc point can have angle smaller than theta_R.
If theta_R<=theta_h, this is automatic. Suppose
theta_R>theta_h. Then

    (P_R)_x<sqrt(r^2-h^2).                          (14)

Otherwise P_R would be an outside right port,
and (12) would give theta_R<=theta_h. Thus the
right endpoint of I on y=h is strictly to the
right of the whole segment P_L--P_R. By the
actual Jordan crosscut of Section 3, it and an
initial part of I are on the exterior side of
the pocket.

On the interval from theta_h toward theta_R,
the closed T-circle interval, if present, is
a terminal interval because it is connected and
contains theta_R. The V-circle interval cannot
meet that earlier interval: it is connected
toward its center at theta_L>theta_R, and would
then contain the radial center point of T.
This would contradict disjoint interiors.

Before reaching the closed T interval, there is
therefore no point of the occupied Jordan boundary:
U is below I, the outer circle has radius R>r,
and the remaining crosscut portions lie in V,T.
The circle stays outside the Jordan region there.
Points on the T interval cannot belong to any
extra's open interior. This proves the required
lower angular bound. This reasoning also covers
theta_R at or beyond the left endpoint of I:
the connected T interval is then a terminal
part of I, and no earlier part can enter the
pocket.

Reflecting the same argument proves the upper
bound by theta_L. Thus every entire extra
open-interior arc lies in

    (theta_R,theta_L).

The whole closed centered beta arcs from (8)
are in the endpoint open interiors. Disjointness
therefore strengthens this to the one actual
free interval

    (theta_R+beta,theta_L-beta).                    (15)

This is a routing statement for the complete
actual extra arcs. It is not inferred from
center directions alone or from an auxiliary
concurrence point. Original weak contacts and
side endpoints can subdivide the pocket but
cannot cross the occupied boundary used above.

## 7. A uniform endpoint-coordinate inequality

Suppose the closing center gap
Gamma=theta_L-theta_R is greater than pi/2.
Then the centers straddle the vertical axis.
Write

    theta_L=pi-delta_L, theta_R=delta_R,
    delta_L,delta_R>=0,
    delta_L+delta_R=pi-Gamma.

For the left tip put a=sin(phi), b=cos(phi).
Equations (4) give

    0<=phi<=delta,
    N+1/2=u*cos(delta-phi),
    Z_0-1/2=u*sin(delta-phi).

These formulas remain valid when N is negative;
only N+1/2>0 is required, and was proved in (3).
Let

    u_0=sqrt(R^2-1/4)-1/2, d=u_0-1/2.

The actual corner equation gives
R^2=u^2+u*(cos(v)+sin(v))+1/2 for v=delta-phi.
Comparing with R^2=u_0^2+u_0+1/2 gives

    u>=u_0-(1/2)*sin(v).

The inequality follows by subtraction:
(u_0-u)(u_0+u+1)=u*(cos(v)+sin(v)-1),
where u_0>=u and u_0+u+1>2u.
The endpoint v=0 is included.

Since K<=Z_0, the exact port coordinate satisfies

    X=bN-aK>=bN-aZ_0
      >=u_0*cos(delta)
        -(1/2)*sqrt(1+2sin(delta)cos(delta)+sin(delta)^2).

If tan(delta)<=28/17, then

    sqrt(1+2sc+s^2)<=c+(9/7)s,

where s=sin(delta), c=cos(delta). Both compared
quantities are nonnegative, and their squared
difference is s*(28c-17s)/49>=0. Hence

    X>=d*cos(delta)-(9/14)*sin(delta).               (16)

The reflected right endpoint has exactly the same
bound. All physical endpoint masks and original
means have remained in the derivation.

## 8. The actual unit side is too short for two exterior extras

Assume two whole extras occupy the pocket.

### 8.1. The entire high-radius interval R>=41/20

Each extra contributes an arc longer than pi/4.
By (15), their disjoint complete arcs require

    Gamma>pi/2+2beta,
    delta_L+delta_R<alpha_H:=pi/2-2beta.

The exact values are

    cos(alpha_H)=160/281,
    sin(alpha_H)=231/281,
    tan(alpha_H)=231/160<28/17.

Also d>49/50: at R=41/20 the squared reserve
against d+1=99/50 is 321/10000.

Put g(t)=d*cos(t)-(9/14)*sin(t). On [0,alpha_H]
it is strictly decreasing and positive. Positivity
at the right endpoint follows already from d>49/50
and the exact value

    (49/50)*(160/281)-(9/14)*(231/281)=83/2810>0.

Thus g''=-g<0 throughout. At a fixed sum of two
arguments, concavity puts the smallest sum of g
at an endpoint pair. Strict decrease and (16)
therefore give

    1=X_L+X_R
      >=g(delta_L)+g(delta_R)
      >g(0)+g(alpha_H)
      >(49/50)*(1+160/281)-(9/14)*(231/281)
      =1+67/7025,

a contradiction.

### 8.2. The entire low-radius interval 2<R<=41/20

Section 4.2 gives each extra an arc longer than chi.
The same actual interval (15) requires

    Gamma>2(beta+chi),
    delta_L+delta_R<alpha_L:=pi-2(beta+chi).

Here beta+chi is in (pi/4,pi/2). Exact angle
addition gives

    cos(alpha_L)=83961/135161,
    sin(alpha_L)=105920/135161,
    tan(alpha_L)<28/17.

The last reserve is 550268/1427337.
Also d>187/200, using R>2 and
15/4-(387/200)^2=231/40000.

For the same g(t), positivity at alpha_L follows
from the exact reserve

    (187/200)*(83961/135161)
       -(9/14)*(105920/135161)
       =14576949/189225400>0.

The identical concavity and strict decrease
argument now gives

    1=X_L+X_R
      >g(0)+g(alpha_L)
      >(187/200)*(1+83961/135161)
          -(9/14)*(105920/135161)
      =1+1138649/94612700,

again impossible.

The two closed radius subintervals overlap at
41/20 and cover the full original interval.
They are scalar radius ranges, not samples
of positions or square orientations. This
proves capacity at most one for the whole
endpoint-owner feature.

## 9. Full physical scope

The proof uses the complete original H balance,
the two true endpoint equations, degree-free
boundary-contact moment signs, and actual
physical port and circle order. It does not
treat any internal loaded body as degree two.

The two physical endpoint masks, individual
zero corner coefficients, all inner means,
all extra squares, and every original positive
spoke remain. No endpoint is normalized to a
different actual square or force line. The
auxiliary barriers are homotopies only inside
the existing closed bodies.

No original adjacent-vertex owner hypothesis
is supplied by this theorem. Endpoints owned
by H, free vertex contacts, positive shared
endpoint intersections, and opposite H
vertices need their separate valid exits.

## 10. Literal original D02.L01345 feature join

Use the original rim 0--1--2--3--4--5--0 and
the unchanged positive chord02, with loads
{0,1,3,4,5}. Put

    H=2, V=1, T=3,
    boundary path 1,0,5,4,3.

The actual degrees remain H3,V2,0_3,5_2,4_2,T2.
All three arbitrary completion squares remain,
as do every original force, normal, mean and
physical circle mask. The same-nine analytic
entry gives R>2.

If the two endpoint intersections H-V and H-T
are singleton tip-owned side-interior contacts
at adjacent actual H vertices, every theorem
premise above is literal.

The full positive-chord central-capacity theorem
puts at most one extra in the entire bounded
free union. Every exterior pocket along one of
the actual boundary-path contacts
1--0,0--5,5--4,4--3 is empty by the complete
touching-boundary-pair pocket theorem.
The sole remaining exterior pocket is the
actual closing pocket through H, and the
present theorem gives it capacity at most one.

Thus all three original extras would have to
fit in total capacity at most two. This
excludes the whole stated original endpoint
feature, retaining the positive chord and
all actual higher-degree forces. Other endpoint
features of D02.L01345 are not declared closed.

## 11. Exact operative sources

| Source | SHA-256 | Operative input |
| --- | --- | --- |
| GENERAL_SINGLE_HUB_BOUNDARY_PATH_POCKET.md | 958bb122342783a824d023c221ccc2c93a68300b00b0ffc3496c25ad394aec84 | Full actual endpoint moments, adjacent-vertex h>0 and |x|<1, physical closing crosscut/order, and whole-pocket strict quarter clearance |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 | Lemma 2.1 only: full actual loaded degree-two properness with a physical boundary neighbor, every mask and mean |
| GENERAL_SIDE_CHANNEL_CAP_INNER_ARC.md | f76d76ef2feccc80098fb6d10d6316af4e393d3ae34d4953846dd27b80c137cb | Full-Q radius-5/4 connected arc >pi/4, and the printed outer-face derivative identity used in the stronger low-radius proof |
| CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md | b61b0dec7ded00984c687e353fd3f3bfb5a5a7ade45d87d69aaeade09f23d80b | Physical circle-corner order and complete direct-boundary-pair exterior-pocket emptiness |
| CHORDED_HEXAGON_CENTRAL_CAPACITY_ONE.md | 0b787eae6efe36d2ca6c40dbb079d3262192125fffe58026bacbfd657d1a9a34 | Entire bounded free union has capacity at most one, with the original chord retained |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Literal original D02 graph, load mask and true degrees |
| LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md | 3b3f40af8f62beee8a55b8d4c8d26398097362d88e91d32116885b4ceea96e90 | Same original nine-unit R>2 entry |

All new geometry and inequalities are printed above.
Exact rational calculations were used only to verify
algebraic transcriptions. No sampled pose, angle mesh,
computational exclusion packet, Lean compilation, CI,
workflow, ledger change, commit, or remote write is
part of this manuscript.

