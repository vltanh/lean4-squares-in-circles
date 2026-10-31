# An equal-roof two-hub chart cannot have a loaded two-force return

Date: October 28, 2026. Author: hexagon.

**Status: complete local physical/force exclusion, frozen for full
independent and root review.** B may have arbitrary degree and circle
load, including zero. The argument does not use a boundary-contact
moment at B or a boundary-neighbor concurrence theorem. It keeps the
entire true C2 equation, every original side mean, both physical circle
masks and zero individual circle weights.

## 1. Literal full chart and local theorem

All squares below are actual contained interior-disjoint unit squares
in the original disk of center O, with

    79/40 <= R <= sqrt(1105)/16 < 25/12.

The coordinate zero is an actual hub application, not the circle
center. The full equal-roof hub chart has the real points and axes

    u=(a,b), v=(b,-a), a>b>0, a^2+b^2=1,
    (a-b)/(a+b) < p < min(b/a,(1-b)/a),
    H=b+ap, t=1-H, P=(0,H), S=(-1,-t),
    alpha=(p,1)/sqrt(1+p^2), f=Jalpha,
    ell=a*sqrt(1+p^2)<1,
    T=P+[0,1]alpha+[q0,q0+1]f,
    q0<0<q0+1, q0<=-ell, u=P-ell*f.              (1)

In particular the actual point W=u+alpha belongs to T. The other
hub has its actual vertex v. The whole actual B and C are

    v0=t/(1-pH), eta=(-1,-v0)/sqrt(1+v0^2), jB=Jeta,
    B=S+[0,1]eta+[-zB,1-zB]jB, 0<=zB<=1,

    w=a-b(1+p), N=sqrt(a^2+w^2),
    zeta=(-w,-a)/N, j=Jzeta=(a,-w)/N,
    C=v+[0,1]zeta+[-z,1-z]j, 0<=z<=1.             (2)

The actual positive incoming force at C is directed along zeta,
at the unchanged hub application v. Its other actual positive pair
force is the C-to-B normal n at their original common application Q.
C has precisely these two pair forces and positive total circle load.
For their original magnitudes kappa,mu>0 and complete circle resultant
F_C, its full force and origin-moment equations are

    F_C-kappa*zeta+mu*n=0,
    -kappa*det(v-O,zeta)+mu*det(Q-O,n)=0.           (3)

B physically touches C. Its entire original force system remains;
no equation or degree condition is imposed on B. All three extras
in the original nine-square use remain present and arbitrary.

**Theorem.** The whole chart (1)--(3) is impossible.

In the original two-unloaded-hub caller, (1)--(2) come from the
complete A3 and D3 equations, with A=[-1,0] times [-t,H] and
D=[0,1]u+[0,1]v. B's ownership and its actual side interval in (2)
are consequences of that full A3 chart, not of a B2 equation. This
local theorem assumes those literal physical conclusions and does
not broaden a frozen original-load theorem by relabeling its forces.

## 2. The whole B lies to the left of C's incoming face

Write B0=v0/sqrt(1+v0^2). We first prove the coupled inequality

                              B0<b.                (4)

Put S0=a+b, L0=a-b and p0=L0/S0. The nonempty interval p0<p<b/a
gives a^2-b^2<2ab. Squaring its positive sides yields 8a^2b^2>1,
so ab>1/(2sqrt(2))>8/25 and 0<L0<3/5.

With a,b fixed, the exact derivative of the original v0 is

    dv0/dp=[1-a-b-t^2]/(1-pH)^2<0.

At p0 its continued value is S0(S0-1)/(S0^2-L0). Comparison with
b/a reduces exactly to L0*S0^2<1. Since S0^2=2-L0^2,

    L0*S0^2=L0(2-L0^2)<(3/5)(2-9/25)=123/125<1.

The cubic is increasing on [0,3/5], with derivative at least 23/25.
Thus v0<b/a, and the increasing map r/sqrt(1+r^2) proves (4).
All denominators are positive because 0<p<1, 0<H<1 and
1-pH>1-H=t>0. In particular 0<v0<1.

The full B box has max B_x<=-1+B0. If w<=0, the whole C box
has min C_x>=b-a/N>=b-1>-1+B0. This contradicts their actual
contact. Therefore

                              0<w<a.               (5)

For this remaining sign, every point of C's near-zeta face still
has x-coordinate at least b-a/N>=b-1. That entire face, including
both endpoints and every actual mean, is strictly separated from B.

## 3. A degree-free strict lower-half-plane bound for the whole B

This is the additional physical argument that removes any need for
B to be boundary. Use C's own coordinates relative to v, and set

    x=w/a=1-(b/a)(1+p), y0=a-t,
    E=sqrt(1+x^2), L=sqrt(1+v0^2),
    g=(x+v0)/(E*L), h=(1-x*v0)/(E*L),
    A0=(1+b+x*y0)/E,
    B1=(x*(1+b)-y0)/E.                            (6)

Here h is a positive scalar, not a normal. Equations (1),(5) give
0<x<1, y0=a+b-1+ap>0, g,h>0 and g^2+h^2=1. The original axes
and point S have the exact coordinates

    eta=(g,-h), jB=(h,g), S-v=(B1,-A0)             (7)

in the (zeta,j) frame.

The nonempty p interval in fact forces b>1/3. Otherwise
a^2-b^2=1-2b^2>=7/9, whereas 2ab<=2/3, contradicting
a^2-b^2<2ab. The exact reserve here is 1/9. Thus

    0<x<1-b/a<1-b<2/3,
    A0>(1+b)/sqrt(1+x^2)>4/sqrt(13)>11/10.         (8)

The final squared reserve is 16/13-121/100=27/1300>0. Since
g<1, every actual point of B, including all its side endpoints,
has j coordinate relative to v at most

    -A0+g*(1-zB)<=-A0+g<-1/10.                   (9)

The omitted eta displacement has coefficient -h<0, so (9) is a
whole-square bound. C's upper-j side has j coordinate 1-z>=0.
Consequently no point of that side or either of its endpoints can
be the actual BC application. No force, load, or concurrence at B
was used in obtaining this strict separation.

## 4. Exhaustive actual BC features force a perpendicular return

The incoming face and both its endpoints were excluded in Section 2.
The upper-j face and both its endpoints were excluded in Section 3.
The remaining C support features are its far-zeta side, its lower-j
side, and their common vertex, with every normal-cone endpoint kept.

The owned far-zeta normal n=zeta is also impossible. In B's actual
frame, zeta has coefficients g>0 and h>0. Hence B's minimum-zeta
support is the unique original vertex with eta coordinate zero and
jB coordinate -zB. Its zeta coordinate relative to v is

                           B1-zB*h<0.              (10)

For the strict sign, direct substitution gives

    B1=-M/N,
    M=(1+b)(1+p)-2a>0.

Indeed at p0=(a-b)/(a+b), M=2a(1-a)/(a+b)>0, and M increases
with p. Thus the point in (10) cannot be on C's far-zeta side,
whose coordinate is exactly one. This excludes the whole owned
side normal, including both endpoints of that face.

Every remaining selected C-to-B normal is therefore a nonnegative
combination of zeta and -j, with a strictly positive -j coefficient.
Both have positive eta projection, respectively g and h. Thus n.eta>0,
and the actual minimum-n support of B is on its minimum-eta face.
The unchanged application must have the form

    Q=S+lambda*jB,
    -zB<=lambda<=1-zB, in particular lambda<=1.    (11)

Its zeta coordinate is B1+lambda*h<=B1+h<1, because B1<0 and
0<h<1. Hence Q cannot be C's far-zeta/lower-j vertex either.
All alternatives have now been covered. The exact surviving contact
must be

    n=-j, Q=v+xi*zeta-z*j, 0<xi<1.                (12)

The strict lower xi endpoint is Section 2's whole-face separation.
The strict upper endpoint is the calculation following (11).

For this actual n=-j the two B-frame coefficients are h>0 and
-g<0. Its minimum support is consequently the unique original
minimum-eta/maximum-jB vertex. Thus (11) sharpens to

    Q=S+lambda*jB, lambda=1-zB, 0<lambda<=1.       (13)

At lambda=0, xi=B1<0, so that endpoint is genuinely impossible.
The actual lambda=1 endpoint remains. In particular Q+eta is a
real point of B. None of these facts resets a shared mean or selects
a different normal after multiplier extraction.

## 5. Full C2 now gives positive radial concurrence directly

With (12), the complete original force equation (3) is

                         F_C=kappa*zeta+mu*j,      (14)

so both its own components are strictly positive. The two original
force lines meet at

                              q=v+xi*zeta.         (15)

This is an actual point of C: 0<xi<1 and 0 belongs to [-z,1-z].
This statement includes z=0 and z=1. There is no appeal to a theorem
whose hypothesis requires a boundary neighbor.

Torque about q in the full equation (3) gives det(q-O,F_C)=0.
For every physical circle corner Z of C, the actual unit diameter
and containment give

    2(q-O).(Z-O)=|q-O|^2+R^2-|q-Z|^2
                     >=|q-O|^2+R^2-2>0.           (16)

The last strictness follows from R^2>=6241/1600>2, with reserve
3041/1600. Summing (16) with all original nonnegative circle weights
gives (q-O).F_C>0. Therefore q-O is a strictly positive multiple
of the full F_C. This uses its positive total weight only; either
individual weight in a physical two-corner mask may be zero.

Write O=(X,Y) in the C frame relative to v. Equations (14)--(16)
give in particular Y<0. The proper distances of the actual two
applications from q are exactly xi>0 and z>=0, both already
geometrically proved. The possible zero outgoing distance z=0 has
not been dropped.

## 6. The complete physical C circle mask

The following corner screen uses the real T point W from (1).
In the actual D frame, zeta=-l*u+m*v with m>l>0 and l^2+m^2=1.
For completeness these coefficients follow from (1),(2):

    l=a*(w+b)/N>0, m=(a^2-b*w)/N>0,
    m-l=b*[b-a+p(a+b)]/N>0.

Put

    C0=-alpha.zeta=(1+p)(a-bp)/(N*sqrt(1+p^2)),
    S1=-f.zeta=[b-a+p(a+b)]/(N*sqrt(1+p^2)).

Both are positive and C0^2+S1^2=1. Their difference has the sign
of 2a-b(1+p)^2. At the larger allowed p endpoint (1-b)/a, write
r0=b/(1+a). The latter expression equals

                2(1-2*r0-r0^2)/(1+r0)^2>0,

since a>b. It is larger at the actual p. Thus

                        C0>S1, C0>1/sqrt(2)>2/3.  (17)

Suppose a physical C circle corner were on its near-zeta face.
Comparison with the contained adjacent unit-advance corner would
give X>=1/2. But the real W=u+alpha has zeta coordinate
-(l+m)-C0 relative to v. Since l+m>1, its radius would satisfy

    |W-O|>=X+(l+m)+C0>1/2+1+2/3
                         =13/6>25/12>R,           (18)

a contradiction. Hence every physical C circle corner has zeta
coordinate one, and adjacent-corner comparison gives X<=1/2.

The unique lower-j circle corner is impossible: being farther than
the upper one would force its radial j component below -1/2,
contrary to (14). Thus the actual upper corner

                        Z_C=v+zeta+(1-z)*j         (19)

is physical. The lower corner on that same far face may also be
physical, with either original circle weight zero.

Set d=1-xi>0 and k=1-z. In fact k>0 without assuming that (19)
has a positive individual weight. Let Zbar be the full circle-weighted
mean of C's physical corners. By (16), for some s>0,

    q-O=s*(Zbar-O), s=(xi-X)/(1-X)<1.

Here 1-X>=1/2 and xi<1 justify the strict upper bound. Its j
component gives Zbar_j=Y*(1-1/s)>0 because Y<0. The largest physical
j coordinate k is at least this mean. Consequently

                              d>0, k>0.            (20)

The initial k=1 zero-proper-distance endpoint remains allowed until
the exact scalar theorem is applied.

## 7. Literal scalar application and all-mask circle contradiction

Equations (6),(7),(13) give exactly

    xi=B1+lambda*h,
    d=1-xi,
    k=1-A0+lambda*g, 0<lambda<=1.                  (21)

Together with (1),(5),(20), these are every premise of
THREE_SPOKE_HUB_OWNER_RETURN_SCALAR_BOUNDS.md, with its B0 named
B1 here to distinguish it from Section 2's B support coordinate.
That accepted complete exact scalar theorem therefore gives

                    d>1/3, 0<k<1/8, h>3/5, g>d.   (22)

No k upper bound, xi lower bound, or artificial independent mean
has been supplied to that theorem. Its complete 475-leaf rational
cover and the independent Fraction reconstruction are unchanged.

If (19) is C's unique physical circle corner, (15)--(16) give

    Z_C-O=R*(d,k)/sqrt(d^2+k^2).

The actual B point Q+eta has C coordinates (xi+g,k-1-h). Its
squared-radius excess over the real corner is exactly

    (g-d)^2+(1+h)^2
       +2R*[(g-d)*d-(1+h)*k]/sqrt(d^2+k^2).

Using (22), this is strictly greater than

    (1+h)*[1+h-2R*(k/d)]
       >(8/5)*[8/5-(25/6)*(3/8)]=3/50>0.          (23)

The omitted square and first cross term are nonnegative; the upper
bound on the subtracted quantity is 25/16, and x(x-25/16) is
increasing for x>=8/5. All signs in (23) are therefore justified.

If both far-face corners are physical, the actual center is

    O=(1-sqrt(R^2-1/4),k-1/2).

The same B point has displacement

    (sqrt(R^2-1/4)+g-d,-1/2-h).

Both squared components exceed the corresponding squared components
sqrt(R^2-1/4) and 1/2 of a real C circle corner. Thus it too lies
strictly outside the containing disk. Both zero individual-weight
endpoints are retained. This exhausts the physical mask and proves
the whole local theorem.

## 8. Exact input and original-scope boundaries

The sole external mathematical implication after the literal chart
is the complete scalar theorem

| File | SHA-256 |
| --- | --- |
| THREE_SPOKE_HUB_OWNER_RETURN_SCALAR_BOUNDS.md | dd6ee983deaeac1cf0c02758b2ddb2501a33175fb0281702a18027f869fdbf64 |
| certificates/three_spoke_hub_owner_return_scalar_bounds.py | d073ebfa7d1c27f8c4272a9d3b5c56e20f8de1a1ae310a8d7d790ff5c91acf99 |
| REVIEW_THREE_SPOKE_HUB_OWNER_RETURN_SCALAR_HEXAGON_2026_10_28.md | a1dc72a8f51e4902a736ce1477312d00580d5585fbe1aa216b9a6e07501dacd4 |
| REVIEW_THREE_SPOKE_HUB_OWNER_RETURN_DOMAIN_AND_SCALAR_ROOT_2026_10_28.md | 4afbf65098e6750573fd8714db6ca945a3be6c03c6cc40a6e6dec79a862e0fd9 |

The full A3/D3 caller must obtain (1)--(2) from the actual pre-channel
hub feature cover. This local proof does not replace that obligation,
use a loaded C3 equation as C2, or allow another positive force at C.
It explicitly allows arbitrary B forces and zero B circle load. Every
physical point used is in an actual unchanged square. No boundary
moment, virtual contact, force deletion, numerical sample, normal
reselection, Lean compilation, CI, or shared metadata edit is used.
