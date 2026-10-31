# Both hub pockets are half-clear and have capacity one in the complete regular side chart

Date: October 31, 2026 UTC. Author: regular-perpendicular continuation,
with the exact center-angle estimates supplied by the root continuation.

**Status: complete hand theorem, submitted for separate review.** In the
entire regular A-owned perpendicular side-channel alternative, both actual
hub pockets are half-clear and each contains at most one additional unit
square. This covers both remaining C masks, including the physical radial
mask with either individual circle coefficient zero, and the exact
transverse B-side contact with its full original mean. All original forces,
physical circle corners, applications, means, and zero-weight contact
subdivisions are retained. Both pocket conclusions hold simultaneously.
No conclusion that either pocket is empty is asserted.

## 1. Literal entry and unchanged notation

Use the complete entry and notation of

`TWO_STRICT_REGULAR_PERPENDICULAR_SIDE_MASK_AND_ANGLE_COVER_2026_10_31.md`

and the whole strict-transverse sector exclusion in Section 5 of

`TWO_STRICT_REGULAR_PERPENDICULAR_C_RADIAL_ANGULAR_AND_ORDER_MASK_HAND_EXCLUSION_2026_10_31.md`.

In particular the actual positive rim is A--V--D--C--N--B--A with the
original chord AD. The three completing squares, if present, are retained.
The whole nine-square lower-radius theorem gives R>2. We also have

    R^2 <= Q0=1105/256,
    R^2=(d+1)^2+1/4,
    14/15<d<61/60.                                     (1)

For the lower bound on d, note that

    15/4-(29/15)^2=11/900>0.

Thus R>2 implies d>sqrt(15)/2-1>14/15. The upper bound is the
same exact original radius-window consequence already proved in the
owner-side radial-mask exclusion source.

Retain

    P=(d,1/2), Q=(d,-1/2),
    h=(c,-s), e=(s,c), k=(C,S), v=(-S,C),
    c=cos(alpha), s=sin(alpha), C=cos(beta), S=sin(beta),
    alpha,beta>0, alpha+beta<pi/4,
    K=P-h+y*e, L=Q-k-t*v,
    0<y,t<1,
    b=(-m*h+e)/p, a=(n*k+e)/q,
    w=Jrot(b), z=Jrot(a),
    m>0, n>0, p=sqrt(m^2+1), q>0,
    x=m*y in (0,1), x+y>1.                            (2)

The complete original hub and V equations also give the unchanged moment

    M=p*det(K,b)=q*det(L,a).                           (2a)

The existing whole physical-mask and angular-sector theorems give

    pi/4<delta_B<=pi/2, 0<delta_C<pi/2,
    0<beta_B<1,
    B=K+[0,1]*b+[-(1-beta_B),beta_B]*w,
    T=K+tau*b+beta_B*w,
    u=T-U, |u|=1,
    Z_B=K+b-(1-beta_B)*w,
    |Z_B|=R.                                         (3)

If delta_B<pi/2, the actual strict support has tau=0. If
delta_B=pi/2, retain its entire original exposed-side mean
0<=tau<=1. B has exactly one physical circle corner. There are
exactly two remaining C alternatives:

* C is physically unique. Then pi/4<delta_C<pi/2,
  0<beta_C<1, and

      C=L+[-1,0]*a+[-(1-beta_C),beta_C]*z,
      U=L+beta_C*z,
      Z_C=L-a-(1-beta_C)*z, |Z_C|=R.                 (3a)

* C is physically radial along -a. Its full actual position is

      C=[-d-1,-d]*a+[-1/2,1/2]*z,
      L.a=-d, -1/2<L.z<1/2.                         (3b)

  Both physical circle corners and both individual nonnegative
  coefficients remain present. For the lower pocket choose its actual
  lower corner

      Z_C^-=-(d+1)*a-(1/2)*z.                       (3c)

  The effect of a different original spoke choice is dealt with in
  Sections 3 and 7; no coefficient is changed.

Here delta_B is the clockwise angle from b to u, and delta_C is the
clockwise angle from u to a. Their actual full circle forces satisfy

    kappa_B*Z_B=p*b+ell*u,
    G_C=-q*a-ell*u,
    kappa_B,ell>0,                                   (4)

with the original full torque equations. Only in (3a) do we write
G_C=kappa_C*Z_C with kappa_C>0. In (3b), G_C stays the
full original two-corner resultant. The owner-side mask theorem
also proved, throughout the whole regular chart,

    A_B=K.b>0, A_C=-L.a>0.                           (5)

Every use of a unique-corner coefficient below is of that literal full
resultant. No second physical corner with a zero coefficient is discarded.

## 2. The whole-family support cap and original torques fix the center order

### 2.1. B's actual containment fixes both global axis signs

Put gamma=arctan(m)-alpha. Then -pi/4<gamma<pi/2 and

    b=(-sin(gamma),cos(gamma)),
    w=(-cos(gamma),-sin(gamma)).

Since K lies on B's actual minimum-b side, its two far-side
vertices have b-coordinate K.b+1 and w-coordinates differing by
one. Their containment and K.b>0 give K.b<=d. Also

    (m+y)^2-p^2=2*x+y^2-1>(1-y)^2>0,

so m+y>p. The exact support projection is

    K.b=-d*sin(gamma)+(1/2)*cos(gamma)+(m+y)/p.

Consequently

    d*(1+sin(gamma))>1+(1/2)*cos(gamma).               (5a)

If gamma<=0, the left side is less than 61/60, whereas the
right side is greater than 1+1/(2*sqrt(2))>61/60. Thus

    0<gamma<pi/2, b_Y>0, w_Y<0.                      (5b)

This argument holds throughout the complete chart. In particular it
does not require the two-unique consequence m>1.

We also need positivity of the actual moment at C. The same support
cap gives the useful stronger global inequality

    -K.w>1/2.                                        (5c)

Here is its complete short check. Set

    d_*=[cos(gamma)/2+(m+y)/p]/[1+sin(gamma)],
    t_gamma=cos(gamma)/(1+sin(gamma)).

The cap says d>=d_*, and cos(gamma)>0. Since
gamma<arctan(m), the decreasing half-angle function gives
t_gamma>p-m. The exact other projection therefore yields

    -K.w=d*cos(gamma)+sin(gamma)/2-(1-x)/p
       >=1/2+[(m+y)*t_gamma-(1-x)]/p
       >1/2+m+y-p>1/2.                              (5d)

The penultimate equality used in the lower bound is

    (m+y)*(p-m)-(1-x)=p*(m+y-p),

with x=m*y. Thus (2a) gives M>0 in both masks, using only
the unchanged actual support cap and original hub/V moment identity.

### 2.2. B's full torque includes its exact transverse-side mean

Put

    X_B=-K.w, r_B=1-beta_B.

Taking the full B torque about the actual point K gives exactly

    kappa_B*(X_B-r_B*A_B)
       =ell*[tau*sin(delta_B)+beta_B*cos(delta_B)]
       >=0.                                           (6)

For example, in the positively oriented frame (b,w), the two actual
points are

    K=(A_B,-X_B), Z_B=(A_B+1,-X_B-r_B),

so det(K,Z_B)=X_B-r_B*A_B. The identity in (6) follows directly
from u=cos(delta_B)*b-sin(delta_B)*w and the force at T. The
contact force at K contributes zero torque about K.

Let c_B be the actual center of B. Its exact formula is

    c_B=K+(1/2)*b+(beta_B-1/2)*w.

Consequently (5)--(6) imply

    det(K,c_B)=X_B/2+(beta_B-1/2)*A_B
       >= beta_B*A_B/2>0.                             (7)

If delta_B<pi/2 then (6) is strict. At the exact tie it may be
zero when tau=0; the strict center-order conclusion (7) still holds.
Thus no endpoint-valued original transverse mean is lost.

### 2.3. C's center order, with its complete physical-mask cover

For C, reflect the whole plane across the ordinary horizontal axis.
Write the reflection as S0 and set

    K'=S0(L), b'=-S0(a), w'=S0(z)=Jrot(b').

In the physically unique alternative (3a), the reflected unchanged
C square has the identical side form

    C'=K'+[0,1]*b'+[-(1-beta_C),beta_C]*w'.

Its own port coordinates are K'.b'=A_C>0 and K'.w'=-X_C,
where X_C=-L.z. The full C torque about L gives

    kappa_C*(X_C-(1-beta_C)*A_C)
       =ell*beta_C*cos(delta_C)>0.                     (8)

Thus its reflected actual center c_C'=S0(c_C) satisfies

    det(K',c_C')>beta_C*A_C/2>0.                       (9)

In the physically radial alternative (3b), write

    X_C=-L.z=M/q>0.

The strict original port also gives X_C<1/2. Its reflected port
and center have the exact coordinates

    K'=d*b'-X_C*w', c_C'=(d+1/2)*b'.

They therefore satisfy directly

    det(K',c_C')=(d+1/2)*X_C>0.                       (9a)

This physical calculation needs no division by an individual C circle
coefficient. In particular the lower argument does not assume
X_C>1/2, which would be false in the radial mask. Equations
(6)--(9a) retain the full genuine ports and every original mean.

## 3. Both hub roofs precede their endpoint centers in polar order

The upper A roof is the actual chain

    P -- R_A=P+y*e -- K=R_A-h.

Every point is in Y>=1/2, with strict inequality away from P. Moreover

    det(P,R_A)=y*(d*c-s/2)>0,
    det(R_A,K)=d*s+c/2+y>0.                            (10)

The first bracket is positive because d>1/2 and c>s>0. All three
points have positive ordinary height. Therefore their upper-half-plane
polar arguments obey

    0<arg(P)<arg(R_A)<arg(K).                         (11)

The actual B frame obeys b_Y>0 and w_Y<0 by (5b).
Hence

    (c_B)_Y>K_Y-1/2>0.

Together with (7), this proves, on the same upper angular lift,

    arg(K)<theta_B:=arg(c_B)<pi.                     (12)

Every point of each straight roof segment is a positive affine
combination of its endpoints. Since the endpoints have positive height
and increasing arguments, its argument lies between theirs. Thus every
point on the entire A roof has argument strictly between 0 and theta_B.

For the reflected D roof, use

    Q'=S0(Q)=(d,1/2),
    R_D'=Q'+t*(S,C), K'=R_D'-(C,-S).

The exact reflected determinants are

    det(Q',R_D')=t*(d*C-S/2)>0,
    det(R_D',K')=d*S+C/2+t>0.                          (13)

Both reflected frame signs are the same: b'_Y=a_Y>0 and
w'_Y=-a_X<0. Equations (9) or (9a), together with (13), give the
identical conclusion:
the entire reflected D roof has arguments strictly between 0 and
theta_C':=arg(c_C')<pi.

The remaining actual upper B chain is

    K -- K-(1-beta_B)*w -- Z_B.

Both segments strictly increase ordinary height by (5b), so its entire
chain is in Y>1/2. The unique-C lower chain is

    L -- L-(1-beta_C)*z -- Z_C,

and both segments strictly decrease height, because a_Y,z_Y>0.
The radial-C lower chain is instead

    L -- -d*a-(1/2)*z -- Z_C^-.

It too strictly decreases height, because 0<X_C<1/2 and
a_Y,z_Y>0. Thus in either mask the chosen lower circle corner
has height less than -1/2.

The full actual upper crosscut consists of the V top side from
Z_+=(d+1,1/2) to P, the A roof, and the displayed B chain.
Every point of this occupied crosscut has height at least 1/2.
The actual protected upper closing circle interval between its two
endpoints also has height at least 1/2: both endpoints are on the
upper semicircle, and sine has no smaller interior minimum there.
This is the original V/B gap through A in the compatible exterior
order V--A--B--N--C--D--V. The chosen lower C spoke and V's
lower corner lie outside that interval. The complementary interval
is not the closing gap of this face.

The reflected construction gives the lower D pocket, using V's
lower corner and the selected actual lower C corner. Any additional
physical circle contact of A or D is retained and may subdivide its
loop. No physical circle-clearance is inferred from zero load.
As in the original half-clearance proof, the crosscut deformation
from actual center/contact routes stays inside the same occupied
V,A,B or V,D,C union. It preserves winding about every extra
interior point. Each occupied loop lies entirely in its stated
closed half-plane, so every bounded free side, including all
subdivisions, lies there as well. We obtain throughout both masks

    every whole upper-pocket extra lies in Y>=1/2,
    every whole lower-pocket extra lies in Y<=-1/2.    (13a)

For radial C, replacing a different original physical spoke corner
by (3c) changes this construction only inside C or in the cap
between its actual outer side and the short containing-circle arc.
Within the original containing disk, that cap is a separate component
of the complement of the closed C: its outer side joins the two
physical circle corners. Its
width in the a direction is R-(d+1)<1, so it contains no
whole unit. A connected extra interior cannot cross that occupied
side to straddle the cap and the main pocket. Therefore this
geometric choice retains every whole actual extra, including when
the selected corner has zero individual circle coefficient. The
identical argument applies to V's two physical corner choices.

## 4. A single exact center-angle bound covers both endpoints

Write sigma=1/sqrt(2). Any actual unit center c_E in D_R satisfies

    |c_E|>=R-sigma>2-sigma

if the unit has a physical circle corner. Every contained unit also
satisfies

    |c_E|^2+|c_E|+1/2 <= Q0,
    |c_E|<91/60.                                      (14)

For the first inequality, the farthest own corner gives
|c_E|^2+|x_E|+|y_E|+1/2<=Q0 in its own frame, and
|x_E|+|y_E|>=|c_E|. The polynomial at 91/60 exceeds Q0 by
31/57600, which proves the second inequality. These are force-free
center bounds for the unchanged unit.

Both actual ports have

    K_X=d-c+y*s>d-1>-1/15,
    L_X=d-C+t*S>d-1>-1/15.                           (15)

The distance from a side port to its actual center is at most sigma.
It follows that the centers c_B and c_C' both have horizontal
coordinate greater than -1/15-sigma and norm greater than 2-sigma.
If that horizontal coordinate is nonnegative, its normalized coordinate
is already greater than -3/5. If it is negative, the same conclusion
follows from

    (1/15+sigma)/(2-sigma)<3/5,

which is equivalent to sigma<17/24 and holds by squaring:

    (17/24)^2-1/2=1/576>0.

Therefore, for either of the upper angles theta_B,theta_C',

    cos(theta)>-3/5.                                  (16)

The exact trigonometric comparison

    cos(5*pi/12)=(sqrt(6)-sqrt(2))/4<11/40

uses sqrt(6)<5/2 and sqrt(2)>7/5. It implies

    sin(5*pi/24)^2>29/80>9/25,
    sin(5*pi/24)>3/5.

Since each angle in (16) belongs to (0,pi), monotonicity of cosine
now gives the strict common bound

    theta_B,theta_C'<17*pi/24.                       (17)

## 5. Each endpoint occupies a closed 30-degree centered arc

Fix the single comparison circle

    |z|=r, r=5/4.

Each boundary center in (14) has radius

    5/4<|c_E|<91/60,

because 2-sigma>5/4. The closed angular interval of half-width
pi/12 centered at its radial direction lies strictly inside its actual
open incircle. To verify this throughout the entire radius interval,
write rho_E=|c_E| and take any angular displacement |phi|<=pi/12.
The exact squared distance from the center is

    rho_E^2+25/16-(5/2)*rho_E*cos(phi)
       < rho_E^2-(12/5)*rho_E+25/16.                  (18)

Here cos(pi/12)=(sqrt(6)+sqrt(2))/4>24/25, using
sqrt(6)>61/25 and sqrt(2)>7/5. The quadratic on the right
is convex. Its values at the two endpoints 5/4 and 91/60 are
respectively

    1/8 and 401/1800,

both strictly less than 1/4. This proves the claimed open-incircle
containment for every point of the closed centered angular interval.
In particular B occupies the entire interval

    [theta_B-pi/12,theta_B+pi/12]                      (19)

on the r-circle, and the reflected C occupies the analogous interval
centered at theta_C'. These are actual occupied points, not arcs of a
comparison or moved square.

The force-free strict-clearance inner-circle theorem also applies to
each endpoint: its distance from O is at least R-sqrt(2)>2-sqrt(2)
and hence exceeds 1/4. Its full closed r-circle intersection is one
connected closed arc, and the radial-center point is in its open
interior. These are precisely the closed-intersection and radial-center
conclusions in Sections 4--7 of

`UNIFORM_INNER_CIRCLE_ARC_FAMILY_AND_SMALL_CENTRAL_DISK_EXCLUSION.md`

at r=5/4. That source includes the required strict interval
r_-<5/4<r_+ and excludes the disconnected tangent-side residue at
this clearance.

## 6. Route every whole extra arc into one short actual interval

Let E be an actual extra in the upper A hub pocket. Equation (13a)
puts E in Y>=1/2. In particular
dist(O,E)>=1/2>1/4. The same force-free inner-circle theorem says

    I_E=int(E) intersect {|z|=5/4}

is one connected open arc of angular length strictly greater than
pi/4. Every point of I_E has argument in (0,pi) and avoids the
entire closed V,A,B union. Different actual extra interiors give
disjoint such arcs.

We prove the full routing statement

    I_E subset (psi,theta_B-pi/12),
    psi=asin(2/5).                                     (20)

The actual occupied crosscut defining this pocket is

    Z_+ -- P -- R_A -- K -- K-(1-beta_B)*w -- Z_B,
    Z_+=(d+1,1/2),                                    (21)

closed by its original protected upper circle interval. The V and B
parts of (21) lie in their unchanged closed units; the middle A roof
has all arguments between 0 and theta_B by Section 3. The outer
circle has radius R>r.

First suppose z in I_E had arg(z)=theta_B. The radial-center point
at that angle belongs to int(B), a contradiction. If instead
theta_B<arg(z)<pi, consider the r-circle path of increasing angle
from z to (0,-r), followed by the downward vertical ray to infinity.
It avoids the B part of (21): B's closed r-circle intersection is
connected and contains theta_B, and it does not contain (0,-r).
Indeed every point of B has ordinary height greater than -1/2,
because K_Y>1/2, b_Y>0, w_Y<0, and 0<beta_B<1.
On the angular lift (-pi/2,3*pi/2), the B intersection is therefore
one interval containing theta_B. A free point of larger angle is past
its upper endpoint and stays free of B along this escape path.

The path avoids V as well. V's full r-circle intersection is exactly
the interval [-psi,psi]: at its two end angles the horizontal
coordinate is sqrt(21)/4, which is greater than 9/8>61/60>d,
and throughout that interval the horizontal coordinate is less than
r<d+1. Its radial center angle is zero. Since the radial-center point
of B is in int(B) and avoids closed V, we have theta_B>psi.
Thus the entire increasing-angle escape path starting past theta_B
misses V.

The A roof is avoided by its strict angular range from Section 3.
All parts of the ray below (0,-r) avoid (21) and the closing upper
circle interval, whose ordinary heights are at least 1/2. The path
therefore reaches infinity without meeting the actual occupied loop.
Its initial point has winding number zero, contrary to its belonging
to the pocket's bounded side. We have proved arg(z)<theta_B.

Every such point avoids B, including its occupied centered interval
(19), so in fact arg(z)<theta_B-pi/12. It also avoids V and
has positive angle, which gives arg(z)>psi. This proves (20) for
every point of the entire actual arc, without assuming radial visibility
of the free pocket or moving a physical square.

The same proof in the reflected lower chart applies to the entire
D pocket. Sections 2--3 supply the reflected center order, and its
actual protected circle interval is the reflected lower interval from
Section 3. In the unique alternative, the reflected endpoint has
ordinary height greater than -1/2 by the same side-coordinate
argument used for B. In the radial alternative it is
C'=[d,d+1]*b'+[-1/2,1/2]*w'; its lower height is greater
than -1/2 because b'_Y>0 and |w'_Y|<1. Thus every whole
lower-pocket extra arc, after reflection, lies in

    (psi,theta_C'-pi/12).                              (22)

## 7. Exact capacity and all weak routing endpoints

Finally

    psi=asin(2/5)>pi/8.

Indeed sin(pi/8)^2=(2-sqrt(2))/4<4/25 follows from
sqrt(2)>34/25, whose positive squared reserve is 94/625.
Combining this with (17), both intervals (20),(22) have length
strictly less than

    17*pi/24-pi/8-pi/12=pi/2.                         (23)

Two extra units in either pocket would contribute disjoint open
r-circle arcs, each longer than pi/4, to that same interval.
Their combined angular length would exceed pi/2, contradicting
(23). Thus each entire actual hub pocket has capacity at most one.

The proof counts actual connected open interiors. Additional physical
circle contacts of unloaded hubs, contact-segment endpoints elsewhere,
and zero-weight contacts may subdivide a pocket but cannot allow an
extra interior to cross the occupied loop. Section 3 fixes the actual
protected upper and lower intervals and the
occupied crosscut deformation from the original physical embedding.
For a weak junction use a compact subset of an extra interior; it has
positive distance from the closed occupied loop and keeps its winding
label in the physical Jordan-routing limit. The escape path above
tests that same label. Closure then returns the entire original square.

If the original V routing convention, or the original radial-C
convention, uses its other physical corner, the difference is inside
that square or in its separate outer cap. The latter has width
R-(d+1)<1 and contains no whole unit by the connected-interior
argument in Section 3. Thus no original individual circle-coefficient
endpoint changes the count.
The argument remains valid with all additional circle-contact
subdivisions retained, and the two capacities hold simultaneously.

## 8. Scope and direct hand inputs

The result applies throughout the complete original regular perpendicular
side family, simultaneously in both remaining C physical masks and at
the exact B transverse-side mean. It uses the actual six-unit component only
for its full hub and V equations, endpoint torques, and original
protected pocket embedding. The other original units remain in the
common disk, which is essential when invoking R>2.

The direct inputs are:

* `NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md`: the accepted analytic
  nine-unit theorem R>2, used only in (1) and the center-radius bounds.
* `TWO_STRICT_REGULAR_PERPENDICULAR_OWNER_EXTERIOR_RADIAL_MASK_EXCLUSION_2026_10_31.md`:
  the whole original bounds (1) and the positive endpoint own-coordinate
  projections (5).
* `TWO_STRICT_REGULAR_PERPENDICULAR_SIDE_MASK_AND_ANGLE_COVER_2026_10_31.md`:
  the complete physical-mask cover, initial angular restrictions,
  actual ports and circle resultants in (3)--(4).
* `TWO_STRICT_REGULAR_PERPENDICULAR_C_RADIAL_ANGULAR_AND_ORDER_MASK_HAND_EXCLUSION_2026_10_31.md`:
  only its complete exclusion of the strict delta_B>pi/2 sector
  and its exclusion of the parallel u=a case in the radial C mask.
  The beta>alpha restriction is not needed for this capacity proof.
* `TWO_STRICT_REGULAR_TWO_UNIQUE_FORCE_RATIO_AND_HALF_CLEAR_HUB_POCKETS_2026_10_31.md`:
  the original two-unique occupied-chain and protected weak-winding
  construction, now printed with both radial-mask and side-mean
  extensions in Section 3. Its stronger two-unique force ratio m>1
  is not used in this broader theorem.
* `UNIFORM_INNER_CIRCLE_ARC_FAMILY_AND_SMALL_CENTRAL_DISK_EXCLUSION.md`:
  only the complete force-free r=5/4 strict-clearance arc theorem,
  including connected closed endpoint arcs and radial-center points.

No central-hole emptiness, side-channel-pocket emptiness, or joint
allocation bound is inferred from these two capacities. They alone do
not close the remaining regular side family or either original D02 row.
All new comparisons and the full interval-routing proof are printed
above. No numerical pose exclusion, angle mesh, external computational
certificate, normal reselection, mean replacement, Lean/Lake build,
or CI is used.
