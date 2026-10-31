# The whole shared-West D-only physical-two feature has a hand exclusion

Date: October 31, 2026 UTC.

**Status: complete original-feature hand proof.** In D02.L135,
the entire physical-two West/strict feature with A-owned strict
roof, physically shared DV, and D-only AD is impossible. The proof
retains all nine original squares, the full A3/D3/V2/B2/C2/N2 stars,
every physical circle corner and individual zero coefficient, the
whole shared DV mean, the chord AD, and every actual side offset.

The earlier generated 217149-node placement/channel cover is not
an input. The hand proof excludes the diagonal feature and all
endpoint radial masks, proves the actual upper hub pocket empty,
and combines the remaining physical regions with the actual central
strip occupied by N. No original coarse row is declared closed by
this one-feature theorem.

## 1. Entire unchanged entry and complete hand dependencies

Keep the original positive component

    A--V--D--C--N--B--A, with the original chord AD,
    A,D unloaded true3; V,B,C loaded true2; N unloaded true2.

All three additional physical squares remain in the same disk.
Use the unchanged shared-West chart and original means

    V=[d,d+1] x [-1/2,1/2],
    P=(d,1/2), Q=(d,1/2-j), 1/2<j<=1,
    h=(c,-s), e=(s,c), c=cos(alpha), s=sin(alpha),
    0<ell<1, y=1-ell,
    W=P-ell*e,
    A=P-[0,1]*h+[-ell,y]*e,
    D=[d-1,d] x [-1/2-ell*c,1/2-ell*c],
    K=P-h+y*e, L=(d-1,-1/2-ell*c).

The original full DV mean also satisfies j>=ell*c. Retain

    F=c-s, Sigma=c+s,
    m=mu/gamma=F/y, n=nu/gamma,
    B0=d*s+c/2, A0=1-ell*s,
    n*(j-1/2)=m*B0,
    n*(1-j+ell*c)=A0,
    p=sqrt(1+2*m*s+m^2), q=sqrt(1+n^2),
    b=(-m*c,1+m*s)/p, a=(n,1)/q,
    w=J*b, z=J*a.

The complete hand physical-mask and return entry is
`PHYSICAL_TWO_SHARED_WEST_D_OWNED_HAND_DIAGONAL_EXCLUSION_AND_SIDE_CONE_2026_10_31.md`.
Its three hand mask inputs exclude free DC, physical-two C, and
physical-two B. Its complete diagonal argument excludes every
original diagonal N. Consequently every remaining original feature
has the strict side form

    pi/4<delta_B,delta_C<pi/2,
    Theta=delta_B+delta_C<3*pi/4,
    T=K+beta_B*w, U=L+beta_C*z,
    T-U=u, |u|=1, 0<beta_B,beta_C<1,
    Z_B=K+b-(1-beta_B)*w,
    Z_C=L-a-(1-beta_C)*z,
    |Z_B|=|Z_C|=R,                                (1)

with the literal full circle forces

    kappa_B*Z_B=gamma*p*b+xi*u,
    kappa_C*Z_C=-gamma*q*a-xi*u,
    kappa_B,kappa_C,xi>0.

Both physical circle corners in (1) are unique. The exact same-side
full-star theorem gives

    Z_B.b>-Z_B.w>1/2,
    -Z_C.a>-Z_C.z>1/2.                            (2)

The whole-chart scalar hand theorem
`PHYSICAL_TWO_SHARED_WEST_D_OWNED_HAND_ROOF_ANGLE_AND_COORDINATE_BOUNDS_2026_10_31.md`
gives

    0<alpha<pi/6, y>11/25,
    M=(m+s)/c>1,
    b=(-M*h+e)/sqrt(1+M^2),
    x=M*y=1-ell*tan(alpha) in (0,1), x+y>1.       (3)

Its same-nine hand radius input is the current analytic route
`NINE_RADIUS_TWO_MEASURE_FIVE_POINT_REDUCTION.md`, Sections 1--3,
and `NINE_RADIUS_TWO_MEASURE_ANALYTIC_FIXED_VALUES.md`, Sections
2--6, accepted in `ANALYTIC_CERTIFICATE_CHECKPOINT_2026_10_27.md`,
Section 3. The printed analytic comparisons assign mass at least
one to every actual open unit under a radial measure of total mass
8997/1000<9. No historical generated boxes are used. Thus

    2<R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1, 14/15<d<61/60.             (4)

The applications of (4) below retain all nine units; it is not a
radius claim for an isolated six-unit core.

## 2. Full endpoint torques establish the two physical hub crosscuts

Put

    A_B=K.b, X_B=-K.w, r_B=1-beta_B,
    A_C=-L.a, X_C=-L.z, r_C=1-beta_C.

Both A_B and A_C are strictly positive. Indeed (2), the circle
equation and R>2 imply

    Z_B.b>R/sqrt(2)>1,
    -Z_C.a>R/sqrt(2)>1,

and A_B=Z_B.b-1, A_C=-Z_C.a-1.

Taking the complete B torque about its unchanged K gives exactly

    kappa_B*(X_B-r_B*A_B)=xi*beta_B*cos(delta_B)>0. (5)

For the actual center c_B,

    det(K,c_B)=X_B/2+(beta_B-1/2)*A_B
                  >beta_B*A_B/2>0.               (6)

In particular X_B>0. Reflection of the whole C chart across the
ordinary horizontal axis gives the identical complete identity

    kappa_C*(X_C-r_C*A_C)=xi*beta_C*cos(delta_C)>0, (7)

and strict reflected center order. These are full original B2,C2
torques; no circle atom or additional positive edge is suppressed.

### 2.1. The upper A crosscut

Let R_A=P+y*e. Its roof satisfies

    det(P,R_A)=y*(d*c-s/2)>0,
    det(R_A,K)=B0+y>0.

The first bracket is positive by alpha<pi/6 and (4). Every point
of P--R_A--K has ordinary height at least 1/2. The original
b direction has b_X<0,b_Y>0 and w_Y<0. Thus every point of

    K -- K-r_B*w -- Z_B

has height greater than 1/2. Also (c_B)_Y>K_Y-1/2>0, so (6)
places the entire roof in the increasing upper angular range

    0<arg(P)<arg(R_A)<arg(K)<theta_B<pi,
    theta_B=arg(c_B).                            (8)

The actual occupied upper crosscut is therefore

    Z_+=(d+1,1/2) -- P -- R_A -- K
                              -- K-r_B*w -- Z_B.  (9)

Its containing-circle closing interval is the protected upper V/B
gap through A. The actual C circle corner has height less than
-1/2, as seen in the next subsection, so it is outside that upper
interval. The full positive circular order V--B--C fixes this same
gap in the original compatible embedding.

### 2.2. The shared-West lower D crosscut

Use the actual point P_D^0=(d,-1/2), the lower inner V corner.
It belongs to the unchanged shared DV segment. The actual lower
D roof is

    P_D^0 -- R_D^0=(d,-1/2-ell*c) -- L.

Every point is at height at most -1/2. Choosing this occupied
route instead of the center/contact path through Q is a geometric
homotopy inside the same closed V,D union and their shared segment.
It does not change Q in any force or torque equation. Every actual
extra interior avoids that union, so its winding label is unchanged.

Let S0 be reflection across the ordinary horizontal axis. The
reflected exact chart is

    P_D=(d,1/2), R_D=(d,1/2+ell*c),
    K_D=S0(L)=(d-1,1/2+ell*c),
    b_D=-S0(a)=(-n,1)/q,
    w_D=S0(z)=(-1,-n)/q=J*b_D.

The reflected actual C is

    K_D+[0,1]*b_D+[-r_C,beta_C]*w_D.

Its incoming channel is -S0(u), at the same angle delta_C from
b_D, and (7) is its full genuine-port torque. The actual reflected
center therefore lies strictly after K_D in upper polar angle.
Also

    det(P_D,R_D)=d*ell*c>0,
    det(R_D,K_D)=1/2+ell*c>0.

Here b_D,Y>0 and w_D,Y<0 for every n>0; no n>1 hypothesis
is needed. This gives the reflected counterpart of (8) and a
whole occupied crosscut above height 1/2. Before reflection its
original endpoint is Z_C, and the whole crosscut and its protected
lower V/C closing interval lie below height -1/2.

The selected upper and lower loops use only original occupied
pieces and the protected containing-circle arcs. Every whole
additional square assigned to the upper or lower hub pocket lies,
respectively, in Y>=1/2 or Y<=-1/2. Further physical circle
contacts of zero-loaded units may subdivide those pockets; they
cannot enlarge their union or let an extra interior cross a loop.

## 3. Literal comparison-circle routing and lower-pocket capacity one

Fix r=5/4 and psi=asin(2/5). The force-free theorem
`UNIFORM_INNER_CIRCLE_ARC_FAMILY_AND_SMALL_CENTRAL_DISK_EXCLUSION.md`
applies to every whole hub-pocket extra, since its distance from O
is at least 1/2>1/4. It gives one connected open r-circle arc
strictly longer than pi/4. Every boundary endpoint also has strict
clearance R-sqrt(2)>1/4. Its closed r-circle intersection is
one connected arc containing its radial-center point in its open
interior.

For completeness, the quantitative center bounds used in the
existing hub-pocket proof apply unchanged to both present endpoint
charts. With sigma=1/sqrt(2), every physical boundary center has

    2-sigma<|c_E|<91/60.

The lower bound follows from its actual circle corner; the upper
bound follows from |c_E|^2+|c_E|+1/2<=1105/256. Its polynomial
at 91/60 exceeds 1105/256 by 31/57600. Both actual reflected
ports have horizontal coordinate greater than -1/15:

    K_X=d-c+y*s>d-1>-1/15,
    (K_D)_X=d-1>-1/15.

Their centers are at distance at most sigma from those ports.
The exact comparison

    (1/15+sigma)/(2-sigma)<3/5

therefore gives cos(theta)>-3/5 for either upper center angle.
Since sin(5*pi/24)>3/5, it follows that

    theta_B, theta_C'<17*pi/24.                  (10)

Here theta_C' is the reflected C angle from Section 2.2.
Moreover each endpoint contains the entire closed r-circle
interval of half-width pi/12 centered at its own center direction
strictly inside its open incircle. Indeed cos(pi/12)>24/25 and
the convex quadratic

    rho^2-(12/5)*rho+25/16

has endpoint values 1/8 and 401/1800 on
5/4<=rho<=91/60, both below 1/4. These are the exact same
scalar checks as Sections 4--5 of
`TWO_STRICT_REGULAR_PERPENDICULAR_BOTH_HUB_POCKETS_HALF_CLEAR_AND_CAPACITY_ONE_2026_10_31.md`;
their hypotheses have all been checked here without transferring
that source's different D geometry.

The actual winding argument of its Section 6 now gives, for the
whole upper extra arc and the reflected whole lower extra arc,

    I_upper subset (psi,theta_B-pi/12),
    S0(I_lower) subset (psi,theta_C'-pi/12).      (11)

Here is the geometric check for this transfer. Both actual roofs
have polar arguments before their endpoint centers by (8) and its
reflected version. The closed endpoint r-circle arc is connected,
contains that center direction, and misses (0,-r): every point of
either reflected endpoint has height greater than -1/2. A free
r-circle point after the center angle can consequently escape by
increasing its angle to (0,-r), then following the downward ray,
without crossing the actual occupied loop. Its winding would be
zero, so it is not in the pocket. The occupied centered interval
then removes the last pi/12 before the center direction. V's exact
r-circle intersection is [-psi,psi], which removes all earlier
positive angles. This proves (11) without assuming radial visibility.

Since psi>pi/8, the two intervals in (11) both have length less
than pi/2 by (10). Two whole extra units would contribute disjoint
open arcs each longer than pi/4 to the same interval. Thus each
whole hub pocket has capacity at most one. In particular the actual
lower D pocket has capacity one.

## 4. The entire upper A pocket is in fact empty

All hypotheses used in the complete upper-pocket geometric proof

`TWO_STRICT_REGULAR_PERPENDICULAR_UPPER_HUB_POCKET_EMPTY_HAND_EXCLUSION_2026_10_31.md`

are now literal for the present A,V,B triple. In that proof replace
only its scalar symbol m by M from (3). The actual entries are

    P_h=d*c-s/2, B0=d*s+c/2,
    M>1, y>11/25, H_top=B0+y>47/50,
    R_A=P+y*e, K=R_A-h,
    b=(-M*h+e)/sqrt(1+M^2),
    0<beta_B<1, |Z_B|=R,
    Z_B.b>-Z_B.w>1/2,
    the actual crosscut (9), and the full routing (11).

The actual x=M*y also lies in (0,1) and x+y>1 by (3),
so any invocation there of the stronger support-cap moment bound
is justified as well. That proof uses no D,C,N equation or
regular perpendicular hub identity once these entries and routing
are available. Its exact two-face comparison is the independent
hand companion
`TWO_STRICT_REGULAR_PERPENDICULAR_UPPER_HUB_TWO_FACE_ARC_GAP_HAND_LEMMA_2026_10_31.md`.

To make the full geometric scope explicit: the actual early crosscut
Z_+--P--R_A meets the r-circle at psi and at
phi_R=acos(P_h/r)-alpha, with psi<phi_R<pi/4. The unchanged
P is inside that circle and R_A is outside. If H_top<=7/6,
A contains the whole closed r-circle arc from phi_R to
phi_top=asin(H_top/r)-alpha. The exact two-face lemma places
the point phi_top+pi/4 strictly inside B, checking both possible
gap-facing B faces; the full same-side order above supplies the
remaining two faces. The connected occupied B arc and (11) then
leave each free flank of length less than pi/4.

If H_top>=7/6, every actual crosscut segment after R_A has
e-coordinate at least H_top. Its r-circle intersections lie in
the single cap e>=H_top of angular length at most
2*acos(14/15)<pi/4, or there are none. Outside that cap the
only loop crossings are the two early crossings psi,phi_R,
with opposite entering/leaving signs and strictly increasing
polar angle along the interior subpath. The lower reference ray
has winding zero. Therefore every remaining bounded-pocket
r-circle component is either the short interval (psi,phi_R)
or a component of that short cap. This is exactly the original
winding proof, using the physically verified crosscut (9).

Thus in either full roof range every connected free component
has angular length at most pi/4, whereas any whole upper-pocket
extra has one open arc strictly longer than pi/4. The upper A
hub pocket is empty.

## 5. The original N port line and both slider endpoints

Put j_N=J*u. The full original N2 gives its actual side chart

    h0=T.j_N=U.j_N,
    N=[a_N,a_N+1]*u+[h0-tau,h0+1-tau]*j_N,
    0<=tau<=1.                                  (12)

No transverse offset is chosen. From (5), X_B>0. The complete
B origin torque then gives

    gamma*p*X_B=xi*h0,

so h0>0 in this unchanged orientation. Both endpoints physically
touch the circle. The complete force-free theorem
`FORCE_FREE_BOUNDARY_SIDE_CHANNEL_CENTER_HEIGHT_AND_PORT_MARGIN.md`
therefore gives

    h0>3/10.                                    (13)

It also supplies the strict signs of the two actual normal port
coordinates; no assumption that O is already between them is made.

The selected central contact pentagon has clockwise boundary

    W -> L -> U -> T -> K -> W.                  (14)

The actual K,L satisfy

    K.j_N=h0-beta_B*cos(delta_B)<h0,
    L.j_N=h0-beta_C*cos(delta_C)<h0.

For W, its exact vector from L is

    W-L=(A0,1),
    (W-L).a=(n*A0+1)/q,
    (W-L).z=(n-A0)/q.

The original full D equation with j<=1 gives n*ell*c<=A0,
and therefore n*ell*s<A0. Consequently

    n-A0<n*A0<n*A0+1.

Since sin(delta_C)>cos(delta_C)>0,

    (W-L).j_N
      =[-(n*A0+1)*sin(delta_C)
                         +(n-A0)*cos(delta_C)]/q<0.

Thus W,L,K all lie strictly below the port line j_N=h0.
The open edge UT meets no other selected pentagon edge, and
its central bounded-side label is the side j_N<h0. This
checks the actual local label even at tau=1, when UT is a
whole boundary side of N, as well as at tau=0.

The exact generic strip lemma
`ACTUAL_SIDE_CHANNEL_STRIP_CUT_AND_OCCUPIED_POCKET_AREA_BUDGET_2026_10_31.md`,
Sections 1--2, now applies literally: the entire open rectangle
inside N between heights h0-tau and h0 is an occupied central
cut of area tau. Its connected interior meets no edge belonging
to the other closed original units, so it retains the verified
bounded-side winding label throughout. No strip area is moved or
counted twice.

## 6. Exact pre-strip central area and the joint N-pocket exclusion

The actual inward A and D triangle cuts in the same pentagon are

    triangle(W,K,P-h-ell*e), area 1/2,
    triangle(W,L,(d-1,1/2-ell*c)), area A0/2.       (15)

Their interiors lie in their respective original squares. Their
signs are fixed by the clockwise edges K->W and W->L: the
third vertices are on the right, central side of those chords.
Each connected triangle interior meets no other selected edge,
so the same physical winding argument includes its full area in
the central region. The two cuts and the N strip lie in three
distinct actual unit interiors and are pairwise disjoint.

Let A_poly be the nonnegative area of (14). Its exact shoelace
identity, using T-U=u, is

    2*A_poly=2*c-ell*s*Sigma+S_area,
    S_area=beta_B*cos(delta_B)+beta_C*cos(delta_C)
                              +beta_B*beta_C*sin(Theta).

For example its triangle term is
-det(K-W,W-L)=2*c-ell*s*Sigma; substituting
Delta+beta_B*w-beta_C*z=u in the remaining determinant terms
gives the displayed S_area. Subtracting only (15), before charging
any N area, leaves the exact constant

    C0=2*(c-1)-ell*s*(Sigma-1)<0.

The whole pre-strip free area consequently obeys

    A_pre=A_poly-(1+A0)/2
          =(C0+S_area)/2
           <(1+sqrt(2))/2<5/4.                  (16)

Here both cosines are below 1/sqrt(2), both beta coordinates
are below one, and sin(Theta)<=1. The whole central free union
has area at most A_pre-tau, by Sections 5--6. In particular it
has capacity at most one even without an occupied exterior N pocket.

Suppose now that the actual exterior N pocket contains an additional
whole unit. The complete force-free theorem
`FORCE_FREE_OCCUPIED_SIDE_CHANNEL_ONE_FORTIETH_PROXIMITY.md`
gives dist(O,N)<1/40. Its actual upper-gap entry is provided by
`FORCE_FREE_BOUNDARY_SIDE_CHANNEL_OUTER_POCKET_CAPACITY_ONE.md`,
Sections 1 and 8: V,B,C are the three original positive boundary
units, the actual C--N--B gap is protected by their unchanged
component resultant order, and h0>0 is already proved in (13).
The original chord AD, every extra, and all additional physical
circle contacts remain. No endpoint degree is reduced by this
force-free invocation.

Every actual point of N has j_N-coordinate at least h0-tau.
Thus the point of norm less than 1/40 gives

    tau>h0-1/40>11/40.

Combining this with (16), the actual central free area is less
than 5/4-11/40=39/40<1. Therefore an additional central unit
and an additional unit in the N exterior pocket cannot coexist.
The same complete side-channel source gives capacity one for the
whole actual N exterior pocket.

## 7. All physical completing regions are counted

The retained simple positive rim, its original chord AD, and the
actual exterior circle spokes at V,B,C place every completing
connected open unit interior in one of the following actual regions.
This is the unchanged center/contact embedding and winding
partition; no edge is deleted to manufacture a cycle.

| Original region | Complete hand bound here |
| --- | --- |
| Central A--V--D triangle | No whole unit, by the physical three-ring hole theorem |
| Central A--D--C--N--B pentagon | Capacity one by (16) |
| Exterior upper A hub pocket | Empty by Section 4 |
| Exterior lower D hub pocket | Capacity one by Section 3 |
| Exterior C--N--B side pocket | Capacity one, and cannot coexist with a central unit, by Section 6 |

For the central triangle, `CONTACT_RING_HOLE_AREA.md` bounds a
physical three-ring's free union below one; its shared DV edge and
original mean are included in that physical contact-ring theorem.
The complete simple-cycle separation source
`SIMPLE_POSITIVE_CYCLES_SEPARATE_ALL_CENTRAL_AND_EXTERIOR_COMPLETION_SQUARES_2026_10_30.md`
keeps the actual chord when applying this partition.

V has two physical circle corners. The separate cap between its
outer side and their short containing-circle arc has width
R-(d+1)<1, so it cannot contain a whole unit. A connected extra
interior cannot cross that occupied outer side to straddle the cap
and a counted pocket. Hence choosing the original upper or lower
V spoke, including either zero-coefficient endpoint, changes no
whole-unit count. B and C are already physically unique.
Additional physical circle contacts of the unloaded hubs or N
only subdivide the same parent regions. They create no omitted
region in which a connected extra can cross an occupied loop.

All weak contacts and tangent r-circle intersections are retained:
compact subsets of an extra interior have positive distance from
the closed core loop, retain its original winding label in the
physical routing limit, and exhaust that interior. The strip's
endpoint label was checked explicitly in Section 5. The upper
empty-pocket theorem treats both roof ranges, both B circle faces,
and tangencies; it does not discard a weak free component. These
are physical routing limits, not changes of original forces or means.

By the table, only the D pocket and one of the central or N pockets
can be occupied. They accommodate at most two completing unit
squares. The unchanged original component has six distinct units
and requires three additional physical units in a nine-square
packing. This contradiction excludes the entire stated feature.

## 8. Scope

Every original shared-West D-only L135 configuration was included
before the diagonal and radial mask exclusions. The remaining side
feature has now been excluded with its complete geometry and
completion, so the old generated placement/channel cover is fully
replaced for this one original owner/roof feature. This does not
transfer an unloaded N equation to the different loaded-N L1345
row, and does not by itself close all other D02.L135 owner features.

No numerical pose exclusion, generated proof tree, external checker,
new common selection, replacement contact mean, Lean/Lake build,
or CI is a premise or operation of this hand argument.
