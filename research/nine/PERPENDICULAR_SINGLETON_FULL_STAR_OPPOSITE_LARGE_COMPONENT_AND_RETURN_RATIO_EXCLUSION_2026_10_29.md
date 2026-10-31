# Full-star opposite returns and large return ratios in a perpendicular singleton roof

Date: October 29, 2026 UTC. Author: root-triangles continuation.

**Status: complete proposed hand theorems, awaiting independent review.**
The full original V2 moment and A3/D3 equations strengthen the upper-return
height theorem: the entire opposite-D-vertex row is impossible whenever
b>=1/2. Independently, the actual one-unit B--N--C projection bridge
excludes both surviving D return rows whenever gamma/nu>=18/5. The
complete remainder is printed explicitly. These are continuous interval
and force-ratio theorems; no entire D02 load family is claimed closed.

## 1. Unchanged physical chart and exact source pins

Retain the physical-two West/strict perpendicular-singleton chart, all
nine actual contained unit squares and every original positive force,
selected normal, physical mask, individual zero circle coefficient and
original application or full shared mean. The original entire stars are

    A:{V,D,B}, D:{V,A,C}, V:{A,D},

with A,D unloaded true3 and V loaded true2 with two PHYSICAL circle
corners. The actual AD singleton is A-owned alone, perpendicular to its
actual AV axis. The full original geometry is

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1, 9/10<d<61/60,
    V=[d,d+1] x [-1/2,1/2],
    P=(d,1/2), Q=(d,-t), 0<t<=1/2,
    H=t+1/2, 1/2<H<=1,
    h=(c,-s), e=(s,c), c,s>0, c^2+s^2=1,
    A=P+[-1,0]h+[-l,1-l]e, 0<l<1,
    W=P-xh-le, 0<x<1,
    v=W-Q=-a h+b e=(-u,y),
    a=H*s+x>0, b=H*c-l>0, a^2+b^2=1,
    u=a*c-b*s>0, y=a*s+b*c>0,
    w=-b h-a e=(-y,-u), D=Q+[0,1]v+[0,1]w.

In particular b<c, s<a, and u^2+y^2=1. Let mu,nu,gamma>0 be the
unchanged AV,DV,AD magnitudes, and put

    r=gamma/mu, q=gamma/nu, M=d*s+c/2>0.

The complete original A3 gives

    F_B=-mu*h+gamma*e,
    K=P-h+(1-l)*e,
    r=(1-l)/(1-x)=(1-H*c+b)/(1-a+H*s).          (1)

The actual B contains K+f for

    f=(-h+r*e)/sqrt(1+r^2),                     (2)

including every original B support face and every zero inward own-axis
coefficient. This physical support-point fact does not replace B by a
point or change its other contact or force equation.

The original full V2 moment is

    nu*t=mu*M,
    nu/mu=M/t>=2*d*s+c>c+s>1,
    r>q, t=M*q/r.                              (3)

Both original circle coefficients, including either possible individual
zero, remain in V's full force equation. Equation (3) uses its existing
torque and does not impose a unique physical corner.

The full original D3 exterior force is

    F_C=-nu*East-gamma*e,
    F_C.v=nu*u-gamma*b,
    F_C.w=nu*y+gamma*a>0.

Write its original C application or entire shared mean as

    L=Q+w+z*v, 0<=z<=1.

The complete unchanged D torque is

    q*[b-(1-z)*a]=u-z*y.                        (4)

The adjacent row z=0 was already excluded in full. In the two remaining
rows the exact identities are

    opposite vertex: z=1, q=(u-y)/b>0;
    D-owned C side: q=u/b, z=u*a/c in (0,1).    (5)

The strict side interval in (5) is deduced from (4) after retaining its
full initial [0,1] mean. It is not a replacement application.

The three complete direct inputs are:

| Source | Frozen SHA256 | Exact use |
| --- | --- | --- |
| PHYSICAL_TWO_WEST_STRICT_PERPENDICULAR_SINGLETON_ADJACENT_RETURN_EXCLUSION_AND_COMPLETE_RESIDUAL_2026_10_29.md | f3718c86a99ef196eba1ee875b66375582a0fc588f10275ec171c442e46780dd | Full original chart, every force/mean, adjacent exit and all c<=3/4 |
| ACTUAL_UNIT_PROJECTION_BRIDGE_AND_PERPENDICULAR_SINGLETON_RETURN_INTERVALS_2026_10_29.md | 97815bf7d2558343a76316a8095096bb780a8e4fe1664274c1863bcbbb8d6132 | Entire-unit projection bridge, original D torque, all-return y<=11/50 and side y<=3/11 |
| PERPENDICULAR_SINGLETON_UPPER_RETURN_ANGLE_COMPENSATION_AND_LARGE_SIDE_COMPONENT_EXCLUSION_2026_10_29.md | 0afb19ae0fbde08c104b6e5bf554ab27885c31dc1c16275de625341f956ce167 | Full upper-return angle compensation and all b>=16/25 |

These frozen sources are unchanged.

## 2. The upper-return proof retains the full slider gain

For b>=1/2 and c>s, the complete angle-compensation proof in the third
input defines the scalar comparison

    r0=(1-H+b)/(1-a), psi0=atan(r0),
    G(b)=1/2+b+sqrt((1+a)/2), a=sqrt(1-b^2),

and proves, over the entire original mean and roof-angle domain,

    f_y>sin(psi0)-s,
    sin(psi0)>=sqrt((1+a)/2).                    (6)

The exact original K height, before dropping any positive term, is

    K_y=1/2+s+c*(1-H*c+b)
       =1/2+b+s+(1-c)*(c-b)+(1-H)*c^2.

Since c<1 and c>b, (6) gives the stronger full-domain consequence

    (K+f)_y>G(b)+(1-H)*c^2.                    (7)

This is the original physical K+f and the original H. Nothing is moved
to realize the scalar zero-tilt comparison r0. In particular the extra
term in (7) is available at every actual H, including the endpoint H=1.

## 3. The whole opposite-vertex row with b>=1/2 is impossible

The already complete b>=16/25 theorem treats that entire interval. It
therefore remains to consider

    1/2<=b<16/25.                              (8)

The original c<=3/4 interval is already excluded as well. Define the
actual angles, without varying any packing,

    c=cos(phi), s=sin(phi),
    u=cos(theta), y=sin(theta),
    a=cos(delta), b=sin(delta), delta=theta-phi>0.

All these angles lie in (0,pi/2), with 0<phi<theta. The opposite-row
positive q in (5) gives u>y, so theta<pi/4. Condition (8) gives
delta>=pi/6 and hence

    0<phi<pi/12,
    s<13/50, c>24/25.                          (9)

The elementary bounds in (9) follow from
sqrt(3)>173/100, sin^2(pi/12)=(2-sqrt(3))/4 and
cos^2(pi/12)=(2+sqrt(3))/4. Their full strictness includes b=1/2,
since the original opposite return still has theta<pi/4.

Also (8) implies

    a^2>369/625>361/625, hence a>19/25.

In the actual ratio (1), its numerator is greater than b>=1/2, while
its denominator satisfies

    1-a+H*s<1-19/25+13/50=1/2.

Therefore the unchanged complete A3 forces

    r>1.                                      (10)

Next define positive scalars

    A0=(a-b)/b, B0=(a+b)/b.

They are positive because b=sin(delta) with delta<theta<pi/4. The
opposite-row identity (5), in the actual A frame, is exactly

    q=A0*c-B0*s.

Since d<61/60 and b>=1/2, one has

    2*d*(a-b)<a+b.

For an explicit whole-domain check, the stronger sufficient comparison
31*a<91*b follows from a<1 and b>=1/2; divide by 30 to compare
(61/30)*(a-b) with a+b. Thus d*A0-B0/2<0. Expanding the full positive
product M*q now gives

    M*q=(d*s+c/2)*(A0*c-B0*s)
        =(A0/2)*c^2+(d*A0-B0/2)*s*c-d*B0*s^2
        <A0/2=(a-b)/(2*b)
        <=a-b<=sqrt(3)/2-1/2<3/8.              (11)

The last comparison uses sqrt(3)<7/4. Every inequality holds throughout
the entire interval (8), with no angle subdivision or sampled pose.

Equations (3),(10),(11) force the original slider to satisfy

    t=M*q/r<3/8,
    H=t+1/2<7/8,
    (1-H)*c^2>(1/8)*(24/25)^2=72/625.          (12)

It remains to bound G on (8). The same complete compensation source
proves that G is concave on (0,1). Its continuous endpoint values on
[1/2,16/25] are both greater than 393/200. At the first endpoint,

    G(1/2)=1+cos(pi/12)>1+193/200=393/200,

because

    (2+173/100)/4-(193/200)^2=51/40000>0.

At the second endpoint the already printed exact comparison gives
G(16/25)>52/25>393/200. Concavity covers the entire interval, so (7),(12)
imply that the actual B point has height

    (K+f)_y>393/200+72/625=10401/5000>R,
    (10401/5000)^2-1105/256=1082579/100000000>0.

This is impossible. Together with the inherited b>=16/25 interval and
the inherited c<=3/4 interval, it proves the complete original
opposite-D-vertex exclusion for every b>=1/2. Both joining endpoints
are included; all side ownership, exterior degrees, physical masks and
all unused equations remain original.

## 4. Both remaining rows exclude the entire force-ratio range q>=18/5

This is a separate full projection-bridge application. Retain an actual
unit N touching both actual B and C, as in both literal D02 callers.
It can have either original load and any physical circle mask. The
complete source cited in Section 1 proves

    min_B e.X-max_C e.X
       >=1+a+(1-z)*b
           -1/sqrt(1+r^2)-1/sqrt(1+k^2),
    k=(s+q)/c>q,

and any actual one-unit B--N--C bridge requires this gap to be at most
sqrt(2). The entire squares, the original L and its full side mean,
and both original contacts with N are used in that conclusion.

Suppose q>=18/5. Each exact row in (5) gives b<1/q<=5/18, because
0<u-y<1 in the opposite row and 0<u<1 in the side row. Consequently

    a^2>299/324>576/625, hence a>24/25,
    299/324-576/625=251/202500>0.                (13)

By (3) and k>q, both r and k are strictly greater than 18/5. Thus

    1/sqrt(1+r^2)+1/sqrt(1+k^2)
       <10/sqrt(349)<27/50,
    (27/50)^2-100/349=4421/872500>0.            (14)

The whole-square gap is therefore strictly greater than

    1+24/25-27/50=71/50>sqrt(2),
    (71/50)^2-2=41/2500>0.                     (15)

The real N cannot span that gap. This excludes both original return
rows at every q>=18/5, including the exact q=18/5 endpoint. The adjacent
row was excluded earlier in full; no case is omitted by using (5).

## 5. Literal original joins and the honest residual

For both D02.L135 and D02.L1345 retain the actual rim and chord

    A--V--D--C--N--B--A, AD,
    A=0,V=1,D=2,C=3,N=4,B=5.

A,D remain unloaded true3; V,B,C remain loaded true2. N remains
unloaded true2 in L135 and loaded true2 in L1345. Every positive edge,
all physical zero-weight contacts, and all three actual completing
units remain. Section 3 needs no additional degree, force or boundary
assumption at the exterior bodies. Section 4 uses only the existing
physical B--N--C path, not a shortened or replaced component.

Combining only the complete exact sources and the two new theorems gives
the following necessary residual inside this particular original
physical-two, West/strict, A-only perpendicular singleton feature:

| Exact original C support on D | Conditions still required of a survivor |
| --- | --- |
| Opposite D vertex | c>3/4, 0<b<1/2, 11/50<y<1/sqrt(2), z=1, 0<q=(u-y)/b<18/5 |
| D-owned exterior side | c>3/4, 0<b<16/25, y>3/11, q=u/b<18/5, z=u*a/c in (0,1) |

Every row must also obey all original force and torque equations,
all containment/nonoverlap constraints, the original physical masks
and every full projection inequality of the cited bridge source.
These necessary domains are not asserted realizable. Whole-data
reflection transports each equation, mean and individual circle
coefficient; it does not alter the actual chart after extraction.

No entire D02 load family, original fine or coarse flag, global
common-selection compatibility premise, equality case or complete
nine-unit proof is closed by this residual theorem. No frozen source,
metadata, ledger or remote state was edited. There was no numerical
pose search, angle mesh, packing certificate, Lean/Lake compilation,
CI/workflow action, or external communication.
