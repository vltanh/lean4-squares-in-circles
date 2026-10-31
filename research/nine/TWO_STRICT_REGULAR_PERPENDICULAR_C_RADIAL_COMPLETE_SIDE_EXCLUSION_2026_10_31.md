# Complete C-radial side exclusion in the regular perpendicular chart

Date: October 31, 2026 UTC.

**Status: complete hand exclusion of the entire physical C-radial
side-channel mask.** In the original regular two-strict chart with both
roofs hub-owned and the genuine perpendicular AD normal owned by A, C
cannot have two physical circle corners when N is the original unloaded
true2 side transmitter. This includes either individual zero circle
coefficient, the original parallel channel direction, and every
transverse support tie with its full original side mean. Together with
the existing B-radial exclusion, both exterior endpoints in the remaining
regular side chart are physically unique.

The main exit is a uniform support gap: the original hub span has
`(K-L).b>1+23/32`, whereas the full original side channel and actual
endpoint supports give `(K-L).b<1+1/sqrt(2)`. No finite pose table or
computed exclusion is used.

## 1. Entire unchanged original chart

Retain the complete actual chart of
`TWO_STRICT_REGULAR_PERPENDICULAR_OWNER_EXTERIOR_RADIAL_MASK_EXCLUSION_2026_10_31.md`
and the full endpoint-cone conclusion of
`TWO_STRICT_REGULAR_PERPENDICULAR_SIDE_MASK_AND_ANGLE_COVER_2026_10_31.md`.
The actual stars are A3, D3, V2, B2, C2 and unloaded N2. All original
units, positive pairs, applications, side means, physical circle corners,
individual nonnegative circle coefficients and additional completing
units remain unchanged.

The original radius window and actual two-corner root V give

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1, 9/10<d<61/60,
    V=[d,d+1] x [-1/2,1/2],
    P=(d,1/2), Q=(d,-1/2).

Use the actual hub frames and original positive force ratios

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
    W=Q+rho*v,
    K=P-h+y*e, L=Q-k-t*v.                       (1)

The inherited original singleton-owner conclusions make K a genuine
relative-interior point of B's minimum-b side and L a genuine
relative-interior point of C's maximum-a side. These are actual own
axes and original applications. The unchanged full V2 torque is

    m*(d*s+c/2)=n*(d*S+C/2).                    (2)

No individual V circle coefficient is changed or assumed equal to
the other. The owner-side source already establishes `K.b>0`,
`L.a<0`, and that B is physically unique. A physically two-corner C
would necessarily have the entire radial position

    C=[-d-1,-d]*a+[-1/2,1/2]*z.                (3)

Suppose (3) occurs. The same genuine original contact L then satisfies

    L.a=-d, -1/2<L.z<1/2.                      (4)

All strictness in (4) comes from the actual side-interior contact,
independently of either physical corner's force coefficient.

## 2. A common full-star moment and the strict inequality p<q

The unchanged origin torques and (2) give the exact common quantity

    M=p*det(K,b)=q*det(L,a)
      =d*c+s/2-H*rho+n*(d*S+C/2).

Thus

    K.w=-M/p, L.z=-M/q.                        (5)

We print the B-containment implication needed here. Put
`gamma=arctan(m)-alpha`, so

    -pi/4<gamma<pi/2,
    b=(-sin(gamma),cos(gamma)),
    K.b=-d*sin(gamma)+(1/2)*cos(gamma)+(m+y)/p,
    -K.w=d*cos(gamma)+(1/2)*sin(gamma)-(1-x)/p.

The actual far side of B has b-coordinate K.b+1 and two vertices
whose w-coordinates differ by one. One of those coordinates has
absolute value at least 1/2. Since K.b>0 and both vertices belong to
the original disk,

    K.b<=sqrt(R^2-1/4)-1=d.                    (6)

The first displayed K projection shows that (6) is equivalent to

    d>=d_*=[(1/2)*cos(gamma)+(m+y)/p]
                                      /(1+sin(gamma)).

The quantity -K.w strictly increases with d because cos(gamma)>0.
At d=d_*, direct substitution gives

    -K.w=1/2+[(m+y)*tau-(1-x)]/p,
    tau=cos(gamma)/(1+sin(gamma))
        =tan(pi/4-gamma/2)>=p-m.

The last comparison uses gamma<=arctan(m). Also the actual hub
geometry gives

    x+y=2+s-c+F*rho>1,
    (m+y)^2-p^2=2*x+y^2-1>(1-y)^2>0.

Hence m+y>p, and

    (m+y)*tau-(1-x)
       >=(m+y)*(p-m)-1+m*y=p*(m+y-p)>0.

Consequently actual B containment implies

    M/p=-K.w>1/2.                             (7)

Combining the genuine radial inequality L.z>-1/2 in (4) with
(5),(7) gives the strict full-star chain

    0<p/2<M<q/2,
    p<q.                                      (8)

This step retained the actual B square and both physical C corners;
it made no use of an N support classification.

## 3. Exact radial angular restrictions

Define

    eta=arctan(J/(n+H)), psi=beta+eta.

Since `n+H-J=F*rho/t>0`,

    0<eta<pi/4,
    a=cos(eta)*k+sin(eta)*v,
    q=J/sin(eta),
    n=J*cot(eta)-H=cos(theta+eta)/sin(eta),
    t=(1-tan(theta))/(cot(eta)-tan(theta)).     (9)

The denominators are positive by the original n>0. Both beta and eta
are below pi/4, so 0<psi<pi/2. Taking the actual projections of L
and using L.a=-d gives

    d*(1+cos(psi))
       =cos(eta)+t*sin(eta)+(1/2)*sin(psi),     (10)

    L.z=-d*sin(psi)-(1/2)*cos(psi)
                          +sin(eta)-t*cos(eta).

Substitute (10) in L.z>-1/2. The result is exactly

    tan(psi/2)*(cos(eta)+t*sin(eta))
       <sin(eta)-t*cos(eta).

Its left side is positive. Thus the right side is positive too,
and the tangent subtraction formula on the actual acute interval
gives

    beta<eta-2*arctan(t),
    t<tan(eta/2).                             (11)

For fixed eta,t the right side of (10), divided by
`1+cos(psi)`, strictly increases with psi. At the strict upper
endpoint `psi=2*(eta-arctan(t))` supplied by (11), putting
`a_eta=tan(eta)` gives

    d < [sqrt(1+a_eta^2)*(1+t^2)+a_eta-t]
                    /[2*(1+a_eta*t)]
      < [sqrt(1+a_eta^2)+a_eta]/2
       =(1+sin(eta))/(2*cos(eta)).              (12)

For the second inequality, multiply the positive denominators and
cancel. It is precisely `t<a_eta+sqrt(1+a_eta^2)`, which follows
from 0<t<1 and a_eta>0. The final expression increases with eta.
If eta<=pi/6, it is at most sqrt(3)/2<9/10, contradicting d>9/10.
Therefore

    eta>pi/6.                                 (13)

Write k_theta=tan(theta). Using the last equality in (9) in (11)
and cancelling positive factors gives

    (1-k_theta)*(1+cos(eta))
       <cos(eta)-k_theta*sin(eta),

and consequently

    k_theta>1/(1+cos(eta)-sin(eta))
           >sqrt(3)-1>7/10.                   (14)

Also `n=(cot(eta)-k_theta)/sqrt(1+k_theta^2)` strictly decreases
in eta and k_theta. For the latter variable its derivative numerator
is `-1-k_theta*cot(eta)<0`. Thus (13)--(14) yield

    n<1/sqrt(5-2*sqrt(3))<5/6.                 (15)

The last comparison follows by squaring: it reduces to
`50*sqrt(3)<89`, whose squared comparison is 7500<7921.

## 4. The entire closed order beta<=alpha is impossible

The function `d*sin(u)+(1/2)*cos(u)` strictly increases for
`0<u<pi/4`, because d>1/2. If beta<=alpha, (2) therefore gives
m<=n. From (14),

    theta/2>arctan(3/10),

since `tan(2*arctan(3/10))=60/91<7/10`. Hence, using (15),

    gamma=arctan(m)-alpha
       <arctan(5/6)-arctan(3/10)
        =arctan(32/75)<arctan(9/20).           (16)

On the other hand, (6) and m+y>p imply

    d*(1+sin(gamma))>1+(1/2)*cos(gamma).        (17)

For gamma<=0, the left side is below 61/60 and the right side
exceeds `1+1/(2*sqrt(2))>61/60`, a contradiction. For
`0<gamma<=arctan(9/20)`, (17) and d<61/60 would require

    30*cos(gamma)-61*sin(gamma)<1.

The left side strictly decreases on that interval, but at its upper
endpoint it equals `51/sqrt(481)>1`. This is another contradiction.
Thus gamma>arctan(9/20), contrary to (16). The whole closed order
beta<=alpha, including beta=alpha, is excluded.

This part did not use an equation at B, C or N beyond actual physical
containment and the inherited original owner interiors.

## 5. The complementary order forces a uniform hub projection gap

We may now assume beta>alpha. We claim

    k_theta>3/4.                              (18)

Suppose k_theta<=3/4. By (13), `cot(eta)<sqrt(3)<7/4`.
The ratio `(1-k)/(7/4-k)` decreases with k, so (9) gives

    t>(1-k_theta)/(7/4-k_theta)>=1/4.

Consequently (11) gives

    beta<pi/4-2*arctan(1/4)=arctan(7/23).

But beta>alpha implies beta>theta/2. By (14) and
`tan(2*arctan(4/13))=104/153<7/10`,

    beta>theta/2>arctan(4/13).

This is impossible because `7/23<4/13` (91<92). Hence (18)
is proved with a strict reserve throughout this entire complementary
order.

Since theta<pi/4, (18) implies

    J<4/5, H>3/5, Sigma=H+J>7/5, F<1/5.

From (8),(9),(13),

    p<q=J/sin(eta)<2*J<8/5,
    m<sqrt(39)/5<5/4.                         (19)

The final comparison is exact: `39/25<25/16` is 624<625.
Using the unchanged actual span W-L=k+v and
`k+v=F*h+Sigma*e`,

    (W-L).b=(Sigma-m*F)/p
       >(7/5-1/4)/(8/5)
        =23/32>1/sqrt(2).                     (20)

The last comparison is 529>512 after squaring positive quantities.

For completeness, the other strict hub projection needs no radius
estimate. Because x+y>1 and m=x/y,

    x>m/(m+1),
    m*x+1>(m^2+m+1)/(m+1)>sqrt(m^2+1)=p.

The last squared numerator reserve is exactly

    (m^2+m+1)^2-(m^2+1)*(m+1)^2=m^2>0.

Thus the actual span K-W=-x*h+e satisfies

    (K-W).b=(m*x+1)/p>1.

Adding this to (20), with Delta=K-L, proves the uniform strict gap

    Delta.b>1+23/32>1+1/sqrt(2).               (21)

## 6. The full original side channel contradicts that gap

The complete actual N2 side equations give original applications
T in B and U in C and the unchanged unit direction u with

    T-U=u, |u|=1.

The full loaded B2/C2 endpoint-cone theorem and the original genuine
axis-port closed-cone theorem, as assembled in the side-mask source,
give the complete angular cover

    delta_B=angle(b,u)>pi/4,
    0<=delta_C=angle(u,a)<pi/2,
    0<Theta=angle(b,a)<3*pi/4,
    delta_B+delta_C=Theta.                     (22)

The full physical B-radial exclusion is what makes the first
inequality strict, including the exact pi/4 boundary. These are
conclusions about the original certificate, not a new normal choice.

Since u.a>0, every actual maximizer U of u on the radial square (3)
has a-coordinate -d. Thus, retaining a possible full exposed-side
mean when u=a, write only

    U=-d*a+sigma*z, -1/2<=sigma<=1/2.

By (4),(5),

    U-L=lambda*z,
    lambda=sigma+M/q<1.                       (23)

For delta_C>0 the original strict support gives sigma=1/2, but
that specialization is unnecessary. In particular no parallel
endpoint, individual zero circle coefficient or endpoint-valued
side mean has been discarded in (23).

Every actual point T of B satisfies `T.b>=K.b`, because K is on
B's minimum-b side. This holds equally for a strict corner, a full
exposed side, or an endpoint-valued mean. The orientation in (22)
gives `z.b=sin(Theta)>0`. Therefore

    Delta.b
      =(T-U).b-(T-K).b+(U-L).b
      <=cos(delta_B)+lambda*sin(Theta)
       <1/sqrt(2)+1.                          (24)

Here `cos(delta_B)<1/sqrt(2)` follows from (22), and
`lambda*sin(Theta)<1` follows from lambda<1 and
`0<sin(Theta)<=1`, also when lambda is nonpositive. No
classification of the exact transverse B support is used.

Equation (24) contradicts the uniform original-hub gap (21).
This excludes the entire complementary order beta>alpha and
finishes the complete physical C-radial side exclusion.

## 7. Complete consequence and literal scope

Both original angular orders are covered. Together with the already
complete owner-side B-radial exclusion, every remaining regular
two-strict, both-roof-owned, genuine A-owned-perpendicular-AD,
unloaded-side-N feature has exactly one physical circle corner at
each exterior endpoint B and C. The reflected D-owned orientation
has the same conclusion after exchanging the entire original data.

The support proof includes u=a, every original B transverse tie,
all genuine contact interiors, all endpoint-valued side means that
occur elsewhere, and all individual zero circle coefficients in the
two-corner physical masks. Its literal original row caller is the
unloaded-N side alternative in D02.L135. It does not treat loaded
N in D02.L1345 as an unloaded transmitter, assert closure of the
remaining two-unique side family, or mark an original coarse row
closed. All three actual completing units and all unused original
equations remain present throughout.

The proof is the exact continuous angular calculation (9)--(19) and
the uniform original-support contradiction (21)--(24). No external
script, numerical pose search, computer-generated exclusion, new
normal selection, replacement mean, shortened star, Lean/Lake
invocation or CI was used.
