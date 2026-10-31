# The regular perpendicular C-radial mask has a strict angular order

Date: October 31, 2026 UTC.

**Status: complete hand exclusion of an entire angular-order submask,
with additional exact restrictions on the complementary radial mask.**
In the original regular, both-roof-owned, A-owned perpendicular AD
chart, a physically two-circle-corner C is impossible whenever
`beta<=alpha`. The proof retains the complete original A3, D3 and V2
stars and needs no equation at B, C or N. In the original unloaded
side-N caller, it also excludes the whole strict sector
`delta_B>pi/2`. The exact transverse sector `delta_B=pi/2` and the
complementary C-radial angular order are not excluded here.

## 1. Unchanged chart and actual physical hypotheses

Use the original chart, contact meanings, and full radius interval of
`TWO_STRICT_REGULAR_PERPENDICULAR_OWNER_EXTERIOR_RADIAL_MASK_EXCLUSION_2026_10_31.md`:

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1, 9/10<d<61/60,
    P=(d,1/2), Q=(d,-1/2),
    h=(c,-s), e=(s,c), k=(C,S), v=(-S,C),
    c=cos(alpha), s=sin(alpha),
    C=cos(beta), S=sin(beta),
    alpha,beta>0, theta=alpha+beta<pi/4,
    H=sin(theta), J=cos(theta), F=J-H>0,
    0<rho<1, t=1-rho,
    x=1+s-H*rho in (0,1),
    y=1-c+J*rho in (0,1),
    m=x/y, n=F/t,
    p=sqrt(m^2+1), q=sqrt((n+H)^2+J^2),
    b=(-m*h+e)/p, a=((n+H)*k+J*v)/q,
    w=Jrot(b), z=Jrot(a),
    K=P-h+y*e, L=Q-k-t*v.                         (1)

The unchanged owner conclusions make K a genuine relative-interior
point of B's minimum-b side, and L a genuine relative-interior point
of C's maximum-a side. The axes are actual own axes. The full original
V torque is

    m*(d*s+c/2)=n*(d*S+C/2).                     (2)

All original forces, means, physical corners, individual nonnegative
circle coefficients, additional units and equations are retained. In
particular (2) is not a shortened V star.

The cited owner-side theorem already proves that B is physically
unique and that a physically two-corner C necessarily has the entire
position

    C=[-d-1,-d]*a+[-1/2,1/2]*z.                 (3)

Suppose throughout Sections 2--4 that this latter physical mask occurs.
Then, at the same original application L,

    L.a=-d, -1/2<L.z<1/2.                       (4)

Strictness is supplied by the inherited genuine side-interior contact;
it is independent of whether either circle coefficient vanishes.

## 2. Exact radial angular equations

Put

    eta=arctan(J/(n+H)), psi=beta+eta.

Because

    n+H-J=F/t-F=F*rho/t>0,

the exact interval is

    0<eta<pi/4.                                (5)

Moreover

    a=cos(eta)*k+sin(eta)*v,
    n=J*cot(eta)-H=cos(theta+eta)/sin(eta),
    t=(1-tan(theta))/(cot(eta)-tan(theta)).     (6)

All denominators in (6) are positive; in particular n>0. In the
actual global frame, a has angle psi, and 0<psi<pi/2. Taking the
original two projections of L gives

    d*(1+cos(psi))
       =cos(eta)+t*sin(eta)+(1/2)*sin(psi),     (7)

    L.z=-d*sin(psi)-(1/2)*cos(psi)
                   +sin(eta)-t*cos(eta).      (8)

Use (7) in the strict lower inequality L.z>-1/2. The identity
`sin(psi)/(1+cos(psi))=tan(psi/2)` gives exactly

    tan(psi/2)*(cos(eta)+t*sin(eta))
       <sin(eta)-t*cos(eta).                   (9)

The left side is positive, so the right side is positive. Division by
the positive factor `cos(eta)+t*sin(eta)` and the tangent subtraction
identity yield

    psi/2<eta-arctan(t),
    beta<eta-2*arctan(t).                      (10)

Both compared angles are in the interval where tangent is strictly
increasing; positivity in (9) also verifies
`eta-arctan(t)>0`. Thus there is no hidden tangent branch in (10).
Since beta>0, this gives the strict useful inequality

    t<tan(eta/2).                              (11)

## 3. Uniform angle and force-ratio bounds

For fixed eta and t, the right side of (7), divided by
`1+cos(psi)`, is strictly increasing in psi in the actual interval.
Indeed it equals

    (cos(eta)+t*sin(eta))/(1+cos(psi))
       +(1/2)*tan(psi/2),

and both terms strictly increase. By (10),
`psi<2*(eta-arctan(t))`. Put `a_eta=tan(eta)>0`. Substitution of
that strict upper endpoint gives

    d < [sqrt(1+a_eta^2)*(1+t^2)+a_eta-t]
                    /[2*(1+a_eta*t)]
      < [sqrt(1+a_eta^2)+a_eta]/2
       =(1+sin(eta))/(2*cos(eta)).              (12)

For completeness, the second strict inequality has a positive
denominator. After multiplication and cancellation, it is equivalent
to

    t<a_eta+sqrt(1+a_eta^2),

which follows from 0<t<1 and `a_eta+sqrt(1+a_eta^2)>1`.
The last expression in (12) strictly increases with eta. If
`eta<=pi/6`, it is at most `sqrt(3)/2<9/10`, contradicting the
original radius bound. Hence

    eta>pi/6.                                 (13)

Write k_theta=tan(theta). From (6) and (11), cancellation of the
positive sin(eta) gives

    (1-k_theta)*(1+cos(eta))
       <cos(eta)-k_theta*sin(eta),

and therefore

    k_theta>1/(1+cos(eta)-sin(eta))
           >sqrt(3)-1.                        (14)

The denominator is positive on (5); the second strict inequality
uses (13). In particular

    theta/2>arctan(3/10),                      (15)

because

    tan(2*arctan(3/10))=60/91<7/10<sqrt(3)-1.

Finally, the expression

    n=(cot(eta)-k_theta)/sqrt(1+k_theta^2)

strictly decreases in each variable on the actual positive domain.
For k_theta the derivative numerator is
`-1-k_theta*cot(eta)<0`; for eta monotonicity of cotangent suffices.
Using (13)--(14),

    n<1/sqrt(5-2*sqrt(3))<5/6.                 (16)

The last rational comparison is exact: after squaring positive
quantities it reduces to `50*sqrt(3)<89`, and `7500<7921` proves it.
No finite pose list or numerical extremum is used in these bounds.

## 4. Whole angular-order exclusion

**Theorem 4.1.** The unchanged physical mask (3) cannot occur in the
entire closed angular order `beta<=alpha`.

*Proof.* The function `d*sin(u)+(1/2)*cos(u)` is strictly increasing
on `0<u<pi/4`: its derivative is
`d*cos(u)-(1/2)*sin(u)>(d-1/2)*cos(u)>0`.
Consequently (2), together with beta<=alpha, gives m<=n. Set

    gamma=arctan(m)-alpha.

Equations (15)--(16) and `alpha>=theta/2` imply

    gamma<arctan(5/6)-arctan(3/10)
         =arctan(32/75)<arctan(9/20).          (17)

We now show that actual containment of B forces the opposite strict
inequality. Since K is on B's minimum-b side and b is an own axis,
the two far-side vertices have common b-coordinate `K.b+1` and
w-coordinates differing by one. At least one of the latter has
absolute value at least 1/2. Both vertices belong to the original
disk, so

    K.b+1<=sqrt(R^2-1/4)=d+1,
    K.b<=d.                                   (18)

Here `K.b>0` was already proved in the cited full owner-side source;
thus the positive square root in (18) is the actual upper support.
The unchanged geometry gives

    x+y=2+s-c+F*rho>1,
    (m+y)^2-p^2=2*x+y^2-1>(1-y)^2>0.

Hence m+y>p. The exact K projection in the gamma frame is

    K.b=-d*sin(gamma)+(1/2)*cos(gamma)+(m+y)/p.

Combining with (18) yields

    d*(1+sin(gamma))>1+(1/2)*cos(gamma).        (19)

We have `-pi/4<gamma<pi/2`. If gamma<=0, the left side of (19)
is less than 61/60, whereas its right side is greater than
`1+1/(2*sqrt(2))>61/60`. Thus gamma>0. If additionally
`gamma<=arctan(9/20)`, (19) and d<61/60 would give

    30*cos(gamma)-61*sin(gamma)<1.              (20)

But the expression on the left strictly decreases for
`0<=gamma<=arctan(9/20)`, and at the upper endpoint equals

    (600-549)/sqrt(481)=51/sqrt(481)>1,

contradicting (20). Therefore
`gamma>arctan(9/20)`, contrary to (17). QED.

This argument used actual containment and the full original A3/D3/V2
identities only. It applies with arbitrary exterior degrees under the
same inherited genuine owner hypotheses, and includes equality
beta=alpha. It does not require a force or torque equation at N.

## 5. A strict side-sector exclusion in the original true2 caller

Add the original loaded B2/C2 and unloaded side-N hypotheses of
`TWO_STRICT_REGULAR_PERPENDICULAR_SIDE_MASK_AND_ANGLE_COVER_2026_10_31.md`.
Its full endpoint-cone theorem places the unchanged channel direction
u between b and a, with

    delta_B=angle(b,u)>pi/4,
    0<=delta_C=angle(u,a)<pi/2,
    Theta=delta_B+delta_C.

The parallel case u=a is impossible by the physical radial-inner-side
support lemma in Section 2 of
`RADIAL_RADIAL_SIDE_CHANNEL_FULL_CAP_PROMOTION_WITH_ARBITRARY_POSITIVE_GRAPH_2026_10_31.md`:
the opposite port would have squared norm less than 13/50, while every
point of the actual boundary square B has norm greater than 14/25,
whose square exceeds 13/50. Thus delta_C>0. The strict C support is
the actual inner corner

    U=-d*a+(1/2)*z,
    T=U+u.                                    (21)

In the actual global angular frame,

    Theta=pi/2+gamma-(beta+eta)
          <pi-theta-eta<2*pi/3.               (22)

The first strict inequality uses `gamma<pi/2-alpha`. For the second,
(13)--(14) give theta>pi/6 and eta>pi/6.

If delta_B>pi/2, the actual strict support of B in direction -u is
its maximum-b, maximum-w vertex. Thus, for its unchanged side
coordinate beta_B in (0,1),

    T=K+b+beta_B*w.

Take its b projection in (21). Since Theta is in (pi/2,2*pi/3)
in this proposed sector and cos(delta_B)<0,

    K.b=T.b-1
       =-d*cos(Theta)+(1/2)*sin(Theta)
                           +cos(delta_B)-1
       <d/2+sqrt(3)/4-1
       <61/120+sqrt(3)/4-1<0.                 (23)

The middle bound follows because
`-d*cos(Theta)+(1/2)*sin(Theta)` strictly increases on
`[pi/2,2*pi/3]`: its derivative is at least
`d*sqrt(3)/2-1/4>0`. The last bound is exact, for
`sqrt(3)<7/4` gives `61/120+7/16<1`.
Equation (23) contradicts the original strict K.b>0. Hence this
entire strict side sector is impossible.

At delta_B=pi/2 the original application can occupy the full exposed
side. The vertex identity used in (23) is not asserted there. The
tie and its original mean remain explicitly open.

## 6. Literal remainder and proof scope

Every remaining C-radial feature of this original orientation must
satisfy all of

    beta>alpha,
    pi/6<eta<pi/4,
    tan(theta)>sqrt(3)-1,
    n<5/6,
    beta<eta-2*arctan(1-rho).

In the original unloaded side-N caller it also satisfies

    0<delta_C<pi/2,
    pi/4<delta_B<=pi/2,
    Theta<2*pi/3.

These are complete hand consequences, not a closure of the remaining
C-radial mask, the two-unique mask, either original D02 row or the
nine-square theorem. In the reflected owner orientation the whole
actual data must be exchanged before applying the same statement.
No normal is reselected; no side application is replaced; no original
circle coefficient, unit or full-star equation is deleted. No external
script, numerical certificate, Lean/Lake invocation or CI is used.
