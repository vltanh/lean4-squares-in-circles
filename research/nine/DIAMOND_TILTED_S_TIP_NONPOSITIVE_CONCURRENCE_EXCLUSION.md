# Nonpositive tip concurrence excludes every tilted hub in the S/S diamond

Date: October 27, 2026.

**Status: complete new hand exclusion of the entire stated interface;
full independent review requested.** The aligned-hub remainder is stated
explicitly. The proof retains the full H4/K3/B3/C2 graph and does not
assign a positive radial concurrence before it has been established.

Use the exact high nonparallel tilted-B domain in
DIAMOND_NONPARALLEL_S_TIP_FULL_DEGREE_DOMAIN.md. Thus

    B=[-U,1-U] times[-V,1-V], U=d*a, V=d*b,
    a>b>0, a^2+b^2=1, U>=1-epsilon,
    d=1+epsilon, 0<epsilon<1/60,
    q_B=(-t*a,-t*b), t=d-sigma,
    0<=sigma<=1/a,

and the actual graph remains HK,HB,HC,KB,KC,HL,BM with the two
real S leaves, physical boundary K,C and all nine units. Every
force, normal, owner, side mean, mask and zero individual circle
weight remains.

**Theorem.** If t<=0, the whole strict P/W interface is impossible.
In either of the other two interfaces, H must own the actual HB
axis as well as B. In particular every H tilted relative to B is
excluded throughout the entire t<=0 domain.

The following physical screen is proved first at arbitrary degree.

## 1. A shallow lower side of an aligned S root puts every boundary neighbor above

Suppose actual contained units A,L have the genuine aligned S chart

    A=[epsilon,d] times[-v,1-v],
    L=[d,d+1] times[-1/2,1/2],
    0<=v<=1/50.

Let T be any distinct physical boundary neighbor of A other than L.
There is no degree or force premise at A or T. We claim every real
circle corner Z of T satisfies

    Z_y>0.                                             (1)

An East support would put T beyond x=d, and the sharp contained-unit
support equality identifies it with L, impossible. A strict Southeast
support at(d,-v) gives an actual inward unit-normal segment entering
int(L); it is impossible even when the original application is an
endpoint. The Southwest point(epsilon,-v) has norm below R-sqrt(2)
and cannot belong to a physical boundary unit.

For an actual West side point P=(epsilon,Y), the boundary-point
bound gives Y>16/25; the negative interval[-v,0] is too small.
If a circle corner Z had Z_y<=0, then

    |Z-P|^2>=R^2-2epsilon*R
       >17/4-5/72=301/72>2,

contrary to the diameter of T. This includes the Northwest endpoint.
For every point P=(X,1-v) on the North side, including the Northeast
endpoint, 0<=X<=d. A circle corner with nonpositive height has
Z.P<=R*X. Therefore

    |Z-P|^2>=(R-X)^2+(1-v)^2
       >=(R-d)^2+(1-v)^2
       >(21/20)^2+(49/50)^2=2+629/10000.             (2)

Here R-d>21/20 follows directly by squaring against
R^2=(d+1)^2+1/4 and d<61/60. Thus these complete support
features also give(1).

It remains to exclude every possible South-normal boundary neighbor.
Its actual maximum-y port is P=(x,-v), epsilon<=x<=d. If T owns
that horizontal support, its frame is[z,z+1] times[-v-1,-v].
The real L and T have overlapping vertical interiors, so the
actual leaf screen forces z+1<=d; the opposite horizontal
alternative contradicts z<=x<=d. Every corner is then inside
radius R by |X|<61/60 and |Y|<=51/50.

Otherwise P is T's unique top vertex, and its full frame is

    T=P+[0,1](c,-s)+[0,1](-s,-c),
    c,s>0, c^2+s^2=1.

If x+c<=d, every horizontal corner magnitude is below61/60 and
every vertical magnitude below431/300, already giving squared
norm less than17/4. If x+c>d, the actual downward-right edge
crosses x=d. Nonoverlap with the real L, including its lower
inner endpoint, forces

    x<=d-lambda*(c/s), lambda=1/2-v>=12/25.

On the positive part of the whole angle range, the maximum of
sqrt(1-s^2)*(1-lambda/s) occurs at s^3=lambda and is
(1-lambda^(2/3))^(3/2). Since

    (12/25)^2-27/125=9/625>0,

lambda^(2/3)>3/5. The maximum is consequently below
(2/5)^(3/2)<4/15; the last squared reserve is8/1125.
On its nonpositive part that same bound is immediate. Thus

    x+c<d+4/15<77/60.

All four actual horizontal coordinates are between-1 and77/60,
and all vertical magnitudes are below431/300. Hence every
corner has squared norm less than

    (77/60)^2+(431/300)^2
       =17/4-24257/45000<17/4.

So T is circle-clear in every South-normal frame, a contradiction.
The complete actual support cover is now exhausted, proving(1).
This local result keeps all original contact owners, both circle
masks, all actual side means and every degree.

## 2. A strict P tip port cannot have t<=0

Put A_0=1-U. If t<=0, then sigma>=d and sigma*a<=1, so

    0<=A_0<=epsilon,
    V^2=d^2-U^2>=2epsilon+epsilon^2.

At the strict P port its actual outward B normal is proportional to

    (X,-Y)=(1-sigma*a,-sigma*b),
    0<X<=A_0, Y>=V.

The actual B support therefore satisfies

    h_B(n_BH)=(A_0*X+V*Y)/sqrt(X^2+Y^2)
       >=V^2/sqrt(epsilon^2+V^2)>epsilon.            (3)

For the strict last comparison, V^2>2epsilon^2 implies
V^4>epsilon^2*V^2+epsilon^4. But H's actual near point
requires h_B(n_BH)<=epsilon. This contradiction excludes
the entire P/W row at t<=0, independently of H's frame.

## 3. The complete tilted-H leaf cover at an owned East tip port

In the other two rows, the actual HB port and normal are

    P=(A_0,Z), n_BH=East,
    Z=-t*b=(sigma-d)b,
    0<=Z<=A_0*b/a.                                  (4)

Suppose H does not own the reverse horizontal axis. It has its
actual unique leftmost vertex at P and complete inward axes

    f=(c,s), j=(s,-c), c,s>0, c^2+s^2=1,
    H=P+[0,1]f+[0,1]j.                              (5)

If A_0=0, (4) gives P=O. Its possible radial side supports and
adjacent vertex norms are at most1, while its opposite corner
has norm sqrt(2). None can be a genuine S leaf at radius d>1.
Hence assume A_0>0. Then

    |P|<=A_0/a<61/3540<1/50,
    P.f>0, P.j=A_0*s-Z*c<A_0<=epsilon.               (6)

The near vertex P and both near-side axes are too small to carry
a genuine S application. The owned far+j direction would require
P.j=epsilon and is excluded by the strict inequality in(6).
The adjacent vertex P+j has positive f projection and therefore
cannot have its radial direction in its outward cone(-f,+j).
The opposite corner is also impossible, since

    P.(f+j)=A_0(c+s)+Z(s-c)
       >=A_0[s+c(1-b/a)]>0,
    |P+f+j|^2>2>d^2.

This is the full eight-feature genuine-leaf cover of H. Only
the following two actual alternatives remain:

* a strict leaf at P+f, with P.j<0;
* an owned far+f leaf, with P.f=epsilon and P.j<=0.

Every side-mean endpoint in the second alternative remains.

## 4. The strict H leaf contradicts the full actual circle sum

In the first alternative define

    U_H=1+P.f>1, V_H=-P.j>0,
    U_H^2+V_H^2=d^2.

With the own axes f,-j, the actual H rectangle has precisely
the shallow S-root form[U_H-1,U_H] times[V_H-1,V_H]. Thus the
complete arbitrary-degree physical theorem
SHALLOW_TILTED_S_ROOT_BOUNDARY_NEIGHBORS_ONE_SIDE.md applies to
both actual boundary neighbors K,C. With the unnormalized
transverse vector

    F_H=-V_H*f-U_H*j,

every actual circle corner of K or C has strictly negative F_H
projection. The real H leaf has zero projection.

The real B leaf direction is e_M=(-a,-b). Direct expansion using
(4) gives the exact identity

    F_H.e_M=a*s-b*c-b*(1-sigma*a).                    (7)

The radial support condition P.j<=0 and(4) imply
a*s<=b*c. Also sigma*a<=1. Thus(7) is nonpositive.
Taking the F_H projection of the FULL global sum

    alpha_L*e_L+alpha_M*e_M+F_K+F_C=0

is impossible: the genuine H leaf contributes zero, the B leaf
contributes at most zero, and both actual positive-total boundary
resultants contribute strictly negatively. All their physical
corner masks and individual zero weights are retained. Every
internal force, including HK, cancels only in this complete sum.

## 5. The owned H leaf uses the complete degree-free screen

In the second alternative P.f=epsilon, put v_H=-P.j>=0.
In the actual f,j coordinates,

    H=[epsilon,d] times[-v_H,1-v_H],
    L=S(f),
    0<=v_H<=Z<=A_0*b/a<1/50.

Section1 therefore gives strictly positive j projection for every
physical circle corner of K and C, or strictly negative projection
on -j. The real H leaf again has zero projection. Moreover

    (-j).e_M=a*s-b*c<=0,

by the same actual P.j<=0 relation. The full global circle sum
has strictly negative -j projection, another contradiction.
This includes v_H=0 and every original owned-leaf endpoint.

## 6. Exact retained domain and limitations

Sections2--5 exclude every t<=0 P/W frame and every t<=0
East/W or East/North frame with H tilted relative to B. No
equation at a false H3 or K2 was used. H4/K3 and all original
means remain, and the conclusion treats entire actual circle
masks rather than selected positive-weight submasks.

An H that owns the reverse East HB axis is parallel to B. That
whole H-parallel alternative remains separate, as do all t>0
interfaces. This source makes no whole hub/tip fine-family claim
until those original domains receive their own complete exits.

The fresh full-degree domain prerequisite has SHA-256
f92553ae946a6dd0a4b0ea3e88bde77027a25d2e9c32f26614d9e5b6ab06f24a.
The shallow tilted screen is the readable reconstructed source at
c8e399293ee684fa21a4d5028dc56ab9234007db2b7e1b3a35ad9e214efc45a3.
No absent earlier proof, numerical sample, altered normal, chosen
replacement mean, remote action, metadata edit, compilation or CI
is used here.
