# Two radial terminals and two shifted columns leave room for at most two further units

Date: October 28, 2026 UTC. Author: tc_finish_v2 continuation.

**Status: complete proposed force-free whole-slider capacity theorem,
frozen for separate full independent and root review.** The theorem
counts every additional actual unit at every orientation. It does
not assume that an extra lies in a sector merely because its center
does. Only actual occupied circle arcs and a completely inaccessible
bounded hole are used.

The parameters vary over a continuous interval. In particular the
theorem does not require the special circle equation of the older
distinct-S wall. The two right-column units may have an actual gap,
and all closed endpoints of their displayed slider ranges remain.

## 1. Entire physical six-unit family

Let

    1/11<x<1/10,
    epsilon=x^2, d=1+epsilon, U=1-epsilon, V=2*x,
    R^2=(d+1)^2+1/4,
    rho=9/8, Q=1105/256.

The exact useful bounds are

    0<epsilon<1/100,
    99/100<U<1, 1<d<101/100,
    2/11<V<1/5,
    R^2<42901/10000<Q.                              (1)

The last squared-radius reserve is Q-42901/10000=4209/160000.
The point (-U,V) has norm d, because U^2+V^2=d^2.
Let e=(-U,V)/d and f=Je. Suppose the actual contained packing
has the following six distinct interior-disjoint unit squares:

    A=[-U,epsilon] times [V-1,V],
    T=[-U,epsilon] times [V-2,V-1],
    B=[epsilon,d] times [z,z+1],
    D=[epsilon,d] times [t-1,t],
    C=[d,d+1] times [-1/2,1/2],
    L=d*e+[0,1]e+[-1/2,1/2]f,                      (2)

where the entire original physical slider range is

    -1/2<=t<=z<=V.                                  (3)

No graph edge, force, degree, circle weight or prescribed frame of
any additional unit is a premise. C,L are real occupied radial
units; they need not be genuine positive graph leaves for this
physical capacity statement.

**Theorem 1.** At most two further actual unit squares, at arbitrary
orientations and with arbitrary physical contacts, can be added
inside the same circle. Hence no nine-unit packing contains (2)--(3).

Containment and nonoverlap of the six prescribed actual units are
explicit hypotheses. No claim that all scalar choices in (1)--(3)
realize a physical packing is needed.

## 2. The only filled hole is completely inaccessible to a unit

The left pair is the entire actual rectangle

    K_L=A union T=[-U,epsilon] times [V-2,V].          (4)

If t<z, the right-column gap is the open rectangle

    H=(epsilon,d) times (t,z).                       (5)

Every point of its boundary is in an actual prescribed unit. Its
lower edge is in D, upper edge in B, left edge in A, and right edge
in C. To check the last two whole edges, (1),(3) give

    [t,z] subset [-1/2,V] subset [V-1,V],
    [t,z] subset [-1/2,1/2].                         (6)

All corner endpoints are therefore retained. The hole height is

    z-t<=V+1/2<7/10<1.                              (7)

The open interior of any further actual unit E avoids the closed
union of the six original units. Indeed a point of a closed unit
in int(E) would force nearby open-interior overlap. If int(E)
entered H, connectedness of the convex open square int(E), together
with the occupied whole boundary of H, would confine it entirely to
H. But a unit square has vertical projection width at least one,
whereas H has height strictly less than one by (7). This is
impossible.

Consequently int(E) avoids the entire closed filled rectangle

    K_R=[epsilon,d] times [t-1,z+1].                 (8)

Boundary points of the gap are already occupied. A closed E point
inside the open gap would also give nearby E interior points in H,
so the closed-point version needed for distance estimates holds too.
When t=z, there is no hole and (8) is simply the actual B union D.

For the arc budget it suffices to retain the smaller blocked
rectangle

    K_0=[epsilon,d] times [z-1,z+1] subset K_R.       (9)

Neither (8) nor (9) is assigned a force, a degree or an application.
They are blocked sets for the capacity argument, obtained by proving
that an actual unit cannot enter the only added hole. No physical
unit has been moved or substituted.

## 3. Every further actual unit has one connected arc longer than forty degrees

The blocked union K_L union K_0 contains the whole closed origin
disk of radius V. On the left part x<=epsilon this follows from
U>V, V-2<-V and the exact upper height V in (4). On the right
part x>=epsilon, its x range reaches d>V, and

    z-1<=V-1<-V,
    z+1>=1/2>V.                                     (10)

Thus an actual further unit has distance at least V from O.
For the closed-point endpoint, a proposed E point strictly inside
D_V has nearby E interior points there. Those points must either
enter an actual prescribed unit's interior or the inaccessible hole
(5); the finitely many seams cannot contain an open neighborhood.
Both possibilities have already been excluded.

Since V>2/11>1/8, the complete theorem
FORTY_DEGREE_NINE_EIGHTHS_ARC_OUTSIDE_ONE_EIGHTH.md applies to E.
Its intersection with the radius-rho circle in its open interior is
one connected open arc of length strictly greater than

    delta=2*pi/9.                                    (11)

Every such arc avoids all closed arcs occupied by the real units
C,L and the blocked rectangles K_L,K_0. Distinct actual further
units have disjoint open arcs. Their actual orientations, boundary
status and zero-force contacts are unrestricted.

## 4. Exact arcs of the two real radial units and the left column

Define angles in (0,pi/2) by

    a=acos(d/rho), b=acos(U/rho), c=acos(epsilon/rho),
    phi=atan(V/U), alpha=asin(4/9).                 (12)

The radial inner face is the active circle constraint for C,L.
Indeed x>1/11 implies d>122/121 and

    (122/121)^2>65/64=rho^2-1/4,

with positive cross-multiplied reserve 911. Therefore

    sqrt(rho^2-d^2)<1/2,
    a<alpha.

Their entire closed radius-rho circle intersections are exactly

    C: [-a,a] about the East direction,
    L: [pi-phi-a,pi-phi+a].                         (13)

The outer radial face is inactive because rho<d+1. Within either
displayed arc the transverse coordinate has absolute value less
than 1/2, as just proved. Outside its inner-face interval the radial
support fails. Thus (13) is an exact physical arc statement,
including both closed endpoints.

For K_L, a nonnegative-y point has squared norm at most
U^2+V^2=d^2<rho^2, so it cannot lie on this inner circle. Its
lower height V-2 is below -rho by (1). The entire closed circle
intersection of K_L is consequently the one lower arc

    [pi+b,2*pi-c].                                  (14)

This follows by letting its actual x coordinate range from -U to
epsilon on the lower semicircle. The top and bottom rectangle
edges impose no additional cut there.

## 5. Exact arcs of the blocked right rectangle and all remaining gaps

Write

    eta_+=min(c, asin(min(1,(z+1)/rho))),
    eta_-=min(c, asin(min(1,(1-z)/rho))).             (15)

Both arguments before the clipping are positive. Equations (1),(3)
give eta_+,eta_->=alpha>a, so their intervals below are nonempty.
The complete closed circle intersection of K_0 is

    upper [a,eta_+], lower [-eta_-,-a].              (16)

Indeed epsilon<=x<=d is exactly a<=|theta|<=c in the right
semicircle. The upper arc is cut only by y<=z+1, and the lower
arc only by y>=z-1. Formula (15) retains both possible inactive
height constraints and every equality endpoint.

Together C and K_0 block the one whole East interval
[-eta_-,eta_+]. Combining (13)--(16) leaves exactly three possible
open angular gaps, with lengths

    G_top=pi-phi-a-eta_+,
    G_side=b+phi-a,
    G_bottom=c-eta_-.                               (17)

Their physical order follows from the actual blocked intervals.
Any vanishing gap causes no difficulty. No unlisted complementary
interval is omitted, including the circle wrap around East.

First the side gap is shorter than forty degrees. The bounds (1)
give rho*U>d^2, so cos(phi)=U/d>d/rho=cos(a) and phi<a.
Also U/rho>22/25>sqrt(3)/2, so b<pi/6. Therefore

    G_side<b<pi/6<delta.                             (18)

No further actual unit's connected arc (11) can lie in that gap.

## 6. One whole-slider comparison bounds the other two gaps together

Put M=sqrt(rho^2-epsilon^2), so 1<M<rho and
c=asin(M/rho). We prove

    eta_++eta_->=c+alpha                             (19)

throughout the entire closed z interval in (3).

If z>=M-1, then eta_+=c. Since 1-z>=1-V>4/5>1/2,
the other angle satisfies eta_->=alpha. If z<=1-M, then
eta_-=c, while z+1>=1/2 gives eta_+>=alpha. Both clipped
height cases, including their thresholds, therefore satisfy (19).

In the complete remaining interval |z|<=M-1, neither angle is
clipped. Convexity of asin on [0,1) gives

    eta_++eta_-
      =asin((1+z)/rho)+asin((1-z)/rho)
      >=2*asin(8/9)>pi/2+alpha>c+alpha.             (20)

For the strict middle comparison, put beta=asin(8/9). Then
pi/4<beta<pi/2, and the angle 2*beta-pi/2 belongs to (0,pi/2).
Its sine is

    -cos(2*beta)=47/81>4/9=sin(alpha).

Strict monotonicity of sine on that interval proves (20).
Thus (19) is a whole-interval hand inequality, not an angular mesh.

We next prove the single exact comparison

    phi+a+alpha>pi/3.                               (21)

The parameters give V/d>200/1111>9/50. Also

    rho^2-(101/100)^2-(49/100)^2=217/40000>0,

so sqrt(rho^2-d^2)>49/100. Therefore

    cos(phi+a)
       =U/rho-(V/d)*sqrt(rho^2-d^2)/rho
       <8/9-49/625=4559/5625.                      (22)

On the other hand

    cos(pi/3-alpha)=sqrt(65)/18+2*sqrt(3)/9
                  >4/9+10/27=22/27,
    22/27-4559/5625=73/16875>0.                    (23)

We used sqrt(65)>8 and sqrt(3)>5/3. Both compared angles lie
in (0,pi): alpha<pi/6 and phi<a<pi/2 suffice. Cosine is
strictly decreasing there, so (22)--(23) prove (21).

Combining (17),(19),(21) yields

    G_top+G_bottom
       =pi-phi-a+c-(eta_++eta_-)
       <=pi-phi-a-alpha<2*pi/3=3*delta.             (24)

This bound is simultaneous over the entire actual two-slider range
-1/2<=t<=z<=V. The gap t<z was dealt with physically in Section 2;
no chosen replacement mean or center location entered (19)--(24).

## 7. Entire completion count and precise scope

Every further unit gives one connected open arc longer than delta
by Section 3. The actual blocked intervals force that entire arc
into one of the three complementary gaps (17). The side gap holds
none by (18). If three further units existed, their pairwise
disjoint arcs would all lie in the union of the top and bottom gaps
and have combined length strictly greater than 3*delta. This
contradicts the strictly smaller total available length (24).

Thus at most two further actual units exist, proving Theorem 1.
The proof routes the actual arcs, not a surrogate center sector.
It never infers the location of an entire unit from one point or
its center. All extra orientations, contacts and masks remain.

The sole imported analytic theorem is

| Source | SHA256 | Literal operative use |
| --- | --- | --- |
| FORTY_DEGREE_NINE_EIGHTHS_ARC_OUTSIDE_ONE_EIGHTH.md | 5c0da36441613ccf2e3ce75a669ca1b212589788442e56b007a33a32d5131517 | Entire connected open arc of length >40 degrees for every actual contained unit with strict distance >1/8, all orientations and boundary endpoints |

That complete source was read before this construction. The hole
argument, actual interval formulas and all new trigonometric bounds
are proved in full above. The older fixed-radius distinct-S wall
motivated the geometry but is not an operative capacity input.

No positive graph is modified, no force is used or removed, and no
particular three completion units are presumed boundary or loaded.
No original family or flag closes automatically without a literal
caller proving the whole actual six-unit geometry (2)--(3). No
computational certificate, sampled pose, angle mesh, Lean/Lake,
CI, metadata edit, staging, commit or remote action is used.
Separate full independent and root review are required for adoption.
