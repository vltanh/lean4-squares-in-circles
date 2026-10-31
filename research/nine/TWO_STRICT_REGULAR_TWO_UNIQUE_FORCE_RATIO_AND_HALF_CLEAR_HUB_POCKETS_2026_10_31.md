# The two-unique regular side chart has m>1 and two half-clear hub pockets

Date: October 31, 2026 UTC. Author: regular-perpendicular continuation.

**Status: complete hand force-ratio and whole-pocket clearance theorem,
submitted for separate review.** In the complete two-unique side-channel
alternative, the full original V torque forces m>1. Consequently the
entire upper A hub pocket lies above y=1/2, and the entire lower D hub
pocket lies below y=-1/2, with the actual protected circle arcs and
whole-square routing retained. The clearance conclusion is independent
of how many completing units occupy a pocket. No pocket capacity zero
or one is asserted solely from this clearance.

## 1. The entire actual entry

Retain the full regular A-owned perpendicular chart and both-unique
side alternative of

`TWO_STRICT_REGULAR_PERPENDICULAR_SIDE_MASK_AND_ANGLE_COVER_2026_10_31.md`.

All original units, positive forces, true degrees, applications, physical
circle masks, individual coefficients and means remain unchanged. Use
the same origin and notation:

    V=[d,d+1] x [-1/2,1/2],
    P=(d,1/2), Q=(d,-1/2),
    h=(c,-s), e=(s,c), k=(C,S), v=(-S,C),
    c=cos(alpha), s=sin(alpha), C=cos(beta), S=sin(beta),
    alpha,beta>0, theta=alpha+beta<pi/4,
    H=sin(theta), J=cos(theta), F=J-H, Sigma=H+J,
    0<rho<1,
    x=1+s-H*rho in (0,1),
    y=1-c+J*rho in (0,1),
    m=x/y, n=F/(1-rho),
    p=sqrt(m^2+1), q=sqrt(n^2+2*n*H+1),
    b=(-m*h+e)/p, a=(n*k+e)/q,
    w=Jrot(b), z=Jrot(a),
    K=P-h+y*e, L=Q-k+(rho-1)*v.                 (1)

The original radius interval gives

    9/10<d<61/60.                               (2)

The exact rational reserves are printed in the owner-side radial-mask
exclusion source; no strict radius endpoint is lost here.

The complete unchanged V torque is

    m*B0=n*D0,
    B0=d*s+c/2, D0=d*S+C/2.                    (3)

Both V physical circle coefficients remain original and nonnegative.
B and C each have one physical circle corner. Their original side
channel direction lies strictly between b and a with both incoming
angles in (pi/4,pi/2). In particular the exterior-axis angle Theta
is obtuse, so

    b.a=(1+n*H-m*n*J)/(p*q)<0.                 (4)

The actual owned-side coordinates and physical corners are

    0<beta_B,beta_C<1,
    Z_B=K+b-(1-beta_B)*w,
    Z_C=L-a-(1-beta_C)*z,
    |Z_B|=|Z_C|=R.                              (5)

The entire selected positive component, for the literal original
caller, is the unchanged rim A--V--D--C--N--B--A with chord AD.
The compatible physical embedding and protected circle-spoke order
are retained. No chord is removed to manufacture a simple-cycle
stress premise.

## 2. The full V torque forces m>1 throughout the obtuse-axis sector

**Theorem 2.1.** Equations (1)--(4) imply

    m>1, x>y, x>1/2.                            (6)

*Proof.* Suppose m<=1. The obtuse inequality (4) gives

    n*(m*J-H)>1.

Since m*J-H<=J-H=F, it follows that n*F>1. The full torque (3)
therefore yields

    1<n*F=m*F*B0/D0<=F*B0/D0,
    F*B0>D0.                                   (7)

The actual trigonometric identities are

    C-F*c=H*(s+c),
    S-F*s=H*(s+c)-2*J*s.

Consequently (7) is exactly

    2*d*J*s>(d+1/2)*H*(s+c).                   (8)

All factors being divided by below are positive. Put

    u=tan(alpha)>0, A=2*d/(d+1/2).

Equation (8) gives

    tan(theta)<A*u/(1+u).

Since theta>alpha, the left side exceeds u. Thus u<A-1. The
function u/(1+u) is strictly increasing for u>0, so a second use
of the displayed inequality gives

    tan(theta)<A-1=(d-1/2)/(d+1/2)
       <31/91<2/5.                              (9)

In this entire small-angle domain, the increasing sine and the
increasing function sin(theta)+cos(theta), together with the
decreasing function cos(theta)-sin(theta), give

    s<sin(theta)<2/sqrt(29)<2/5,
    Sigma<7/sqrt(29)<4/3,
    F>3/sqrt(29)>1/2.                            (10)

The two nontrivial rational comparisons follow respectively from
441<464 and 36>29. No sampled angle is used.

But m=x/y<=1 gives x<=y, and the exact identity

    x-y=c+s-Sigma*rho

therefore gives

    rho>1/Sigma>3/4.

Here c+s>1 makes the first inequality strict, even if m=1.
Together with (10), this implies

    n=F/(1-rho)>2.                              (11)

On the other hand, (2),(10) give

    B0< (61/60)*(2/5)+1/2=68/75<1,
    D0>(C+S)/2>1/2,

where d>1/2 was used in the second line. The very same full torque
(3), with m<=1, gives n=m*B0/D0<2, contradicting (11).
Thus m>1 and x>y. Finally the original chart has

    x+y=2+s-c+F*rho>1;

combining this with x>y gives x>1/2. QED.

This theorem used the full V2 and hub reductions and the actual obtuse
exterior-axis condition. It did not use an equation at a completing
unit, impose equal V circle coefficients, or change an original mean.

## 3. Both actual outer occupied chains are half-clear

The actual A square is

    A=P+[-1,0]*h+[-(1-y),y]*e.

Its outer boundary arc from AV to AB is exactly

    P -- P+y*e -- K.                             (12)

Along the first segment the ordinary y coordinate increases because
e_y=c>0; along the second it increases because (-h)_y=s>0.
Thus the whole arc is in y>=1/2, and only P has height 1/2.

By Theorem 2.1 and alpha<pi/4,

    b_y=(c+m*s)/p>0,
    w_y=(s-m*c)/p<0.                            (13)

The actual outer B boundary arc from K toward its physical circle
corner in this pocket is

    K -- K-(1-beta_B)*w -- Z_B.                  (14)

The first segment increases ordinary y by (13), and the second
increases it by b_y>0. Hence the whole arc is above K_y>1/2.
In particular Z_B has ordinary height strictly greater than 1/2.

For D, put t=1-rho in (0,1). Its actual outer boundary arc from DV
to DC is

    Q -- Q-t*v -- L.                            (15)

Both segments decrease ordinary y, since v_y=C>0 and k_y=S>0.
The entire arc is in y<=-1/2, with equality only at Q.

Both ordinary components of a are positive:

    a_x=(n*C+s)/q>0, a_y=(n*S+c)/q>0,
    z_y=a_x>0.

The actual outer C boundary arc is

    L -- L-(1-beta_C)*z -- Z_C.                  (16)

Both segments decrease ordinary y. Thus the entire arc is below
L_y<-1/2, and Z_C has height strictly less than -1/2. This lower
chain computation retains the full C physical-corner equation and
does not need a fictitious reflected A3 equation.

## 4. The actual circle arcs and whole-pocket routing

Choose V's actual upper circle corner

    Z_+=(d+1,1/2)

for the upper A closing region and its actual lower circle corner

    Z_-=(d+1,-1/2)

for the lower D closing region. This is a geometric use of V's two
physical corners. It does not change which individual corner carries
which original force coefficient.

The upper occupied crosscut is the concatenation

    Z_+ -- P -- P+y*e -- K
        -- K-(1-beta_B)*w -- Z_B.                (17)

The first segment lies in the unchanged V; all remaining segments
are the actual arcs (12),(14). The physical third-support separation
at the full unloaded A3 makes B closed-disjoint from V and D, and
the original AV and AB contacts in this chart are the distinct
singletons P and K. Thus (17) is an occupied simple polygonal
crosscut. B retains its one physical circle corner. No physical
circle-clearance is inferred from A's zero circle load: any additional
physical circle contact of A is retained and may subdivide the closed
loop used below.

Both endpoints of (17) lie on the upper open semicircle. The closed
upper-circle interval between them has height at least 1/2: on
an angular interval contained in (0,pi), the sine has no interior
minimum below its endpoint values.

This is the actual protected circle interval for the A exterior
pocket. To check the choice rather than assume a complementary
arc, the original protected spoke at C ends at Z_C in y<-1/2,
and V's lower spoke ends at Z_-. The given compatible exterior
order is V--A--B--N--C--D--V. The consecutive V/B gap through A
therefore uses the upper interval, which contains neither the C
spoke nor the lower V endpoint. The complementary interval is
not the closing interval of this actual face. The crosscut
deformation from center/contact routing to (17) stays inside the
same closed V,A,B union, so it preserves winding about every extra
interior point.

The closed occupied loop consisting of (17) and that actual upper circle
interval has its entire boundary in y>=1/2. Every point below that
line can escape to infinity along a horizontal ray below the loop,
and thus has winding number zero. Every bounded free component on its
actual pocket side is consequently contained in the same closed
half-plane, including any subdivision at an additional physical
circle contact. Connected open interiors assign each whole actual
extra in the upper A pocket to that same bounded side; taking closure gives

    E subset {ordinary y>=1/2}.                  (18)

The lower computation is identical in its actual protected order,
using (15)--(16), Z_- and Z_C. Its complete boundary lies in
y<=-1/2 and the complementary protected interval contains the
upper B spoke. Every whole extra in the lower D pocket therefore
satisfies

    E subset {ordinary y<=-1/2}.                 (19)

Extra zero-weight contacts may subdivide either pocket, and a
shared contact elsewhere may have an endpoint-valued original
mean. They cannot let a connected extra interior cross an occupied
boundary. At weak graph junctions, apply the same winding argument
first to a compact subset of that interior before taking the usual
physical Jordan-routing limit. The compact subset stays a positive
distance from the closed occupied crosscut, so its side is stable;
closure gives (18)--(19) for the entire original unit. No force
application or original mean moves in this geometric routing.

If a routing convention uses V's other physical circle corner for
one of these pockets, the only additional free component is the cap
beyond V's actual outer side between Z_+ and Z_-. That cap has
horizontal width R-(d+1)<1 and cannot contain a whole unit, whose
width in every direction is at least one. The remaining change is
inside occupied V. Thus (18)--(19) still classify every whole
additional unit that can actually occur in the corresponding hub
pocket. No corner-coefficient endpoint is excluded by the choice.

## 5. Complete conclusion and precise limits

Every actual unit in either of the two hub pockets has distance at
least 1/2 from the original origin, and in particular strictly more
than 1/4. These are whole-unit statements, independent of orientation,
load, individual circle coefficient and further physical contacts.
They apply simultaneously throughout the complete both-unique regular
side alternative. The reflected choice of AD-owning hub gives the
same result with the entire data exchanged.

Together with the existing occupied-side-pocket proximity theorem,
this separates any near-origin completion obligation from these
two hub pockets without deleting the chord or any positive force.
It does not prove that either hub pocket is empty or has capacity
one. It does not exclude the whole remaining regular side family,
either original D02 row, or a nine-square completion on its own.

The force-ratio proof is the complete continuous calculation
(7)--(11). The pocket proof is the actual boundary-chain sign
calculation and protected winding in (12)--(19). No numerical pose
search, computer-assisted exclusion, replacement contact, shortened
star, new normal choice, Lean/Lake invocation or CI was used.
