# Shared-West D-only interfaces: a hand diagonal exclusion and complete side cone

Date: October 31, 2026 UTC.

**Status: complete hand return-mask reduction.** In the original
D02.L135 physical-two shared-West chart with A-owned strict roof and
D-only AD, the entire unloaded diagonal N alternative is impossible.
Every remaining side N has physically unique owned endpoints and
both actual endpoint angles strictly between pi/4 and pi/2. This
replaces the generated endpoint-mask and transverse-gap tests for
this chart. It does not by itself exclude the whole side feature.

## 1. Entire original chart and previously excluded physical masks

Retain all original nine units and full positive stars

    A:{V,D,B}, D:{V,A,C}, V:{A,D},
    B:{A,N}, C:{D,N}, N:{B,C}.

A,D,N are unloaded and V,B,C are loaded. Keep the original
common selection, every actual physical circle corner, every
individual nonnegative circle coefficient, and every original mean.
Use the unchanged chart

    V=[d,d+1] x [-1/2,1/2], P=(d,1/2),
    h=(c,-s), e=(s,c), c=cos(alpha), s=sin(alpha),
    0<alpha<pi/4, 0<ell<1, y=1-ell,
    W=P-ell*e,
    A=P-[0,1]*h+[-ell,y]*e,
    D=[d-1,d] x [-1/2-ell*c,1/2-ell*c],
    K=P-h+y*e,
    L=(d-1,-1/2-ell*c),
    Q=(d,1/2-j), 1/2<j<=1, j>=ell*c.

Q is the entire unchanged shared DV mean. Set

    F=c-s>0, Sigma=c+s,
    m=mu/gamma=F/y>0, n=nu/gamma>0,
    B0=d*s+c/2, A0=1-ell*s>0,
    p=sqrt(1+2*m*s+m^2), q=sqrt(1+n^2),
    b=(-m*c,1+m*s)/p,
    a=(n,1)/q, w=J*b, z=J*a.

The exact full A3/D3/V2 identities are

    m*y=F,
    n*(j-1/2)=m*B0,
    n*(1-j+ell*c)=A0.                         (1)

The already proved hand sources

* `PHYSICAL_TWO_SHARED_WEST_D_OWNED_FREE_EXTERIOR_HAND_EXCLUSION_2026_10_31.md`;
* `PHYSICAL_TWO_SHARED_WEST_D_OWNED_C_RADIAL_HAND_EXCLUSION_2026_10_31.md`;
* `PHYSICAL_TWO_WEST_STRICT_D_OWNED_B_RADIAL_HAND_EXCLUSION_2026_10_31.md`

show that the original AB and DC directions are owned by B and C
at genuine side-interior K and L, respectively, and that both B
and C have exactly one physical circle corner. The same-nine hand
R>2 input used in the C-mask source is retained. In particular
this is a physical uniqueness conclusion, including all original
zero-coefficient endpoints; it is not a choice of one circle atom.

The inward directions at the two external supports are b and -a.
The complete original endpoint forces, with the unchanged positive
N magnitude xi and actual unique circle corners Z_B,Z_C, read

    kappa_B*Z_B=gamma*p*b+xi*u,
    kappa_C*Z_C=-gamma*q*a-xi*u,
    kappa_B,kappa_C,xi>0.                       (2)

The original full torques at B,C,N remain in force.

## 2. An own-axis resultant cannot have a unique physical circle corner

For a contained unit square with positive total circle load and
exactly one physical circle corner Z, its circle resultant is a
positive multiple of Z. If that resultant is parallel to an actual
own axis f, then Z.Jf=0. Its adjacent actual vertex in the
transverse own direction has squared radius |Z|^2+1>R^2,
contradicting containment. Thus the full resultant of a physically
unique boundary square is never parallel to one of its own axes.

This fact includes either sign of f. A zero vector cannot occur:
the sole circle coefficient is positive and |Z|=R>0.

## 3. The entire diagonal N alternative is excluded

Suppose N were the original unloaded diagonal transmitter. Its
full N2 gives unchanged applications T,U and direction u with

    T-U=sqrt(2)*u.

The already selected incident-diagonal avoidance makes u an actual
own axis of both B and C at those diagonal contacts. Their whole
frames are therefore parallel. The external axes b and a belong
to these same frames and are nonparallel: b has negative ordinary
horizontal component and positive vertical component, whereas a
has both components positive. They cannot be positive or negative
multiples. Thus b and a are perpendicular and

    u in {b,-b,a,-a}.

If u=+b or -b, (2) makes the entire B circle resultant parallel
to its own b axis. If u=+a or -a, (2) makes the entire C
circle resultant parallel to its own a axis. Each case contradicts
Section 2 and the physical uniqueness from Section 1. This exhausts
all original diagonal directions, without a generated gap test.

## 4. The actual external support difference has a strict positive cone

Write Delta=K-L. Directly from the unchanged chart,

    Delta_x=1-c+y*s>0,
    Delta_y=1+c+s=1+Sigma>0.                    (3)

The directions a,b lie in the upper half-plane and span an angle
strictly between zero and pi. Because b_x<0, (3) gives
det(Delta,b)>0. The other cone determinant is

    q*det(a,Delta)=n*(1+Sigma)-(1-c+y*s).

Adding the last two identities in (1) gives

    n*(1/2+ell*c)=A0+m*B0>A0.

It is consequently enough to prove

    N(ell)=(1-ell*s)*(1+Sigma)
            -(1/2+ell*c)*(1-c+s-ell*s)>0.     (4)

Here alpha is fixed only in this scalar comparison. Direct expansion
gives

    N'(ell)=cos(2*alpha)-c-s/2-2*c*s+2*ell*c*s
             <=cos(2*alpha)-c-s/2<0.

Since 0<ell<1,

    N(ell)>N(1)
       =1/2+c/2+cos(2*alpha)-c*s>c/2>0.

The last inequality uses cos(2*alpha)>0 and c*s<1/2.
Thus both cone determinants are strict, and

    Delta=lambda*b+eta*a, lambda,eta>0.        (5)

Apply the complete unchanged loaded-endpoint cone theorem in
`LOADED_ENDPOINTS_FORCE_TRANSMITTER_CONE_AND_PHYSICAL_CORNER_CAP_2026_10_29.md`,
Section 2. It retains full B2,C2, both coincident-application
possibilities and the original N2. Formula (5) makes its premise
literal. A parallel endpoint would be physically radial, already
excluded. Hence the actual remaining side direction u lies in the
strict positive cone between b and a.

## 5. The full D mean gives a uniform aperture below 135 degrees

Let Theta be the clockwise angle from b to a, with 0<Theta<pi.
A direct dot and determinant calculation gives

    p*q*(cos(Theta)+sin(Theta))
                         =1+m*Sigma+n-m*n*F.   (6)

If m*F<=1, the right side is positive immediately. If m*F>1,
the full D equation in (1), with j<=1, gives

    n<=A0/(ell*c).

It is enough in this case to prove

    ell*c*(1+m*Sigma)-A0*(m*F-1)>0.

Multiply by the positive y and use m*y=F. The exact result is

    E(ell)=2*ell*c*cos(2*alpha)-ell+2*s*c-ell^2*F.

For fixed alpha this is a strictly concave quadratic in ell. Its
two endpoint values on [0,1] are

    E(0)=2*s*c>0,
    E(1)=F*(Sigma-1)*(Sigma+1+F)>0.

Thus E(ell)>0 for every original 0<ell<1. This proves that
the right side of (6) is positive throughout the chart. Since
0<Theta<pi,

    Theta<3*pi/4.                              (7)

No circle-force split or endpoint contact coordinate was bounded
independently to obtain (7); the original full shared mean supplied
the necessary D comparison.

## 6. The complete side remainder is strictly same-side and two-unique

Let delta_B,delta_C be the clockwise angles from b to u and from
u to a. The strict-cone conclusion gives

    delta_B,delta_C>0,
    delta_B+delta_C=Theta<3*pi/4.

If either angle were at most pi/4, the complete corresponding
true2 star would lie in the closed 45-degree cone about its owned
external axis. Its original genuine side-interior port supplies the
strict term in
`LOADED_FULL_STAR_CLOSED_SIDE_CONE_WITH_GENUINE_AXIS_PORT_FORCES_RADIAL_ALIGNMENT_2026_10_29.md`,
Theorem 2.1. That endpoint would be physically radial, contrary to
Section 1. Therefore both angles exceed pi/4; together with (7),
this gives the full strict cover

    pi/4<delta_B<pi/2,
    pi/4<delta_C<pi/2.                         (8)

All original parallel and transverse endpoint directions have now
been covered before any support mean is identified as a vertex.
The strict signs in (8) make the actual side applications exactly

    T=K+beta_B*w, U=L+beta_C*z,
    0<beta_B,beta_C<1,
    T-U=u, |u|=1.

The actual endpoint squares and their unique circle corners are

    B=K+[0,1]*b+[-(1-beta_B),beta_B]*w,
    Z_B=K+b-(1-beta_B)*w,
    C=L+[-1,0]*a+[-(1-beta_C),beta_C]*z,
    Z_C=L-a-(1-beta_C)*z.

The same complete source, Theorem 2.2 and Section 2.3, gives the
literal own-coordinate orders and original torque identities

    Z_B.b>-Z_B.w>1/2,
    -Z_C.a>-Z_C.z>1/2,
    gamma*p*(1-beta_B)
                    =xi*(sin(delta_B)-cos(delta_B)),
    gamma*q*(1-beta_C)
                    =xi*(sin(delta_C)-cos(delta_C)).

These formulas concern the original actual support points and
physical corners. They retain the whole original positive graph,
the chord AD, and all three completing units. They give a complete
hand entry for subsequent central-area and exterior-pocket arguments,
without claiming those arguments already completed here.
