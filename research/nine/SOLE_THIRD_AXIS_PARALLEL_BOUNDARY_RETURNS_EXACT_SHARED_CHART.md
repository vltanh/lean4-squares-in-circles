# Parallel boundary returns at a sole-third-axis hub have one exact shared chart

Date: October 28, 2026 UTC. Author: sole-UT continuation.

**Status: complete proposed local hand theorem and literal original feature
reduction, submitted for full root and separate independent review.** The
proof covers every actual contact feature between the two parallel boundary
returns. It excludes the complete point-only return and the other shared
face, forces one physical circle corner of W, and retains the full original
mean and all V circle-weight endpoints. The theorem has no upper-radius
restriction and uses no force equation or boundary premise at the third
neighbor T.

This is an exact reduction of a whole physical feature, not an exclusion of
the remaining chart and not a whole original D02-row closure.

## 1. Complete local statement

Retain the fixed containing-circle origin O and R>=2. Let U,V,W,T be
distinct actual closed unit squares in D_R, with pairwise disjoint open
interiors. Keep every original force, actual separating normal, original
application or full shared-side mean, physical circle mask and individual
zero circle coefficient. Assume:

1. U is truly unloaded with exactly the positive neighbors V,W,T.
2. V is positively circle-loaded with exactly the positive neighbors U,W.
3. W physically touches the containing circle and physically touches V.
   Its degree, all other forces and its circle weights are arbitrary.
4. The sole U-owned normal is the original UT normal. The UV normal is
   owned by V and not by U, with its actual application in the relative
   interior of the actual V side. UW is not U-owned.
5. The physical frames of V and W are parallel.

The third unit T may have any true degree, total circle load and physical
circle mask. No equation at T is used. All additional actual units remain.

The complete original sole-third-axis chart, whose short local derivation
is recalled in Section 2, puts U=[0,1]^2 only as a translated support chart.
The physical origin is not moved. In that chart set

    P_V=(1,1), P_W=(1,0), n_UT=West,
    v=n_UV=(a,b), a,b>0, a^2+b^2=1,
    u=(b,-a), det(u,v)=1.

**Theorem.** The physical VW intersection has positive length and its
unchanged original V-to-W normal is u. There are actual parameters

    r=1-a,
    k=b+s, 0<=s<1-b, hence b<=k<1,
    x>=1/2, y>3/2,

such that, in the actual orthonormal u,v frame about O,

    V=[-x,1-x] x [y-1,y],
    W=[1-x,2-x] x [y-1-k,y-k],
    R^2=x^2+y^2,
    4x+2ky=4+k^2.                                      (A)

The unique physical circle corner of W is (2-x,y-k). The physical V
mask is either its unique corner (-x,y), with x>1/2, or the full two-corner
outer-v face, with x=1/2. Both individual weight endpoints of that latter
mask remain until the unchanged positive force equations impose their
actual signs.

If z is the original VW mean's v coordinate, and Lambda is the original
sum of V circle coefficients after the common 1/R has been absorbed,
the entire retained equations are

    y-1<=z<=y-k,
    F_V=Lambda*(-xi,y), Lambda>0,
    0<xi<=x,
    xi=x if x>1/2; 0<xi<=1/2 if x=1/2,
    mu=Lambda*y, nu=Lambda*xi,
    xi*z=y*(x-r).                                      (B)

In particular

    x>r, (1-a)*y>=x*k,
    x/y<=b/(1+a).                                      (C)

Write the unchanged UW normal as (c,-d) in the translated U chart, with
c,d>0 and c^2+d^2=1. Then

    ac-bd>=0,
    P_T=(0,t), t=ad/(ad+bc), 0<t<=a^2.                  (D)

If ac-bd>0, UW is a physical vertex/vertex contact, s=0 and k=b; then
t<a^2. If ac-bd=0, its original normal is u and the entire actual side
position 0<=s<1-b remains. These are conclusions about the given physical
data, not new normal choices.

## 2. The genuine sole-third-axis chart

All original U applications are distinct. The actual V-to-U application
does not belong to W by the full loaded-tip common-point theorem at
R^2>=4>13/4. The full unloaded-three-force touching-return separator
makes T closed-disjoint from V and W. In particular it supplies the
remaining two distinct applications.

Rotate the translated U chart so its original UT normal is West. Both
other normals strictly expose U vertices. Their vertices cannot be
opposite: the complete opposite-vertex unit-reach argument for an actual
touching return pair excludes that geometry. The two left vertices give
negative horizontal sum; either horizontal adjacent pair gives vertical
components of the same strict sign. Complete positive U force balance
therefore forces the two right vertices. Reflect vertically, without
exchanging V's true degree with W's, so V is the upper one. Thus

    P_V=(1,1), P_W=(1,0),
    n_UV=(a,b), n_UW=(c,-d), a,b,c,d>0.

Let mu,omega,tau>0 be their unchanged magnitudes. The full U force and
torque give

    mu*b=omega*d,
    tau=mu*a+omega*c,
    P_T=(0,t), t=mu*a/(mu*a+omega*c)=ad/(ad+bc).           (1)

The original t is strictly in (0,1), though it may be an endpoint of an
actual positive shared UT segment. No mean is set to a vertex.

The translated chart is exactly the local calculation in Section 9 of
the current exact single-axis cover. The premises of that local
calculation, just checked here, use no T2 equation or T boundary status.

## 3. Every parallel W placement and every VW contact are covered

Because V owns UV at its side interior, an actual r in (0,1) gives

    V=P_V+[-r,1-r]u+[0,1]v.                            (2)

Now n_UW.u=bc+ad>0. If n_UW.v=ac-bd<0, Q=P_W is W's strict
minimum-normal vertex and W has inward axes u,-v there. Both axes have
negative vertical components, so W lies at height at most Q_y=0.
But every point of V has height at least 1-(1-r)a>0. VW could not touch.
Thus

    ac-bd>=0.                                         (3)

If this dot product is positive, Q is W's vertex with inward axes u,v.
If it is zero, n_UW=u and Q is on W's minimum-u side. Hence every case,
including all side endpoints, has the actual form

    W=Q+[0,1]u+[-s,1-s]v, 0<=s<=1,                    (4)

with s=0 in the strict case of (3). In the translated u,v coordinates
based at P_V, Q=a*u-b*v. The two whole rectangles therefore are

    V: u in [-r,1-r], v in [0,1],
    W: u in [a,a+1], v in [-b-s,1-b-s].                (5)

Their actual contact requires 1-r>=a and 1-b-s>=0. If both inequalities
were strict, their open interiors would overlap. Consequently the
complete physical contact cover is exactly:

| Actual VW feature | Exact parameters | Original V-to-W support |
| --- | --- | --- |
| Positive shared u face | r=1-a, s<1-b | u |
| Positive shared v face | s=1-b, r<1-a | -v |
| One common vertex | r=1-a, s=1-b | alpha*u-beta*v, alpha,beta>=0 |

In the last row alpha^2+beta^2=1. Under the strict original point-contact
convention both are positive, but the following proof also covers their
zero endpoints. Thus no point normal is reselected to obtain this cover.

Equation (3), together with (1), gives t<=a^2: after multiplication by
positive denominators this is exactly bd<=ac. Equality is equivalent to
ac=bd; in that case the unit vectors give (c,d)=(b,a), hence n_UW=u.

## 4. The entire other shared face is impossible

Suppose VW has positive length and its normal is -v. At V the two pair
reactions are in the same inward direction -v. Its complete circle
resultant is therefore

    F_V=(mu+nu)*v.

Farthest-own-coordinate comparison forces the complete physical V mask
to be the two outer-v corners, with own u interval [-1/2,1/2] and own v
interval [d_0,d_0+1], where

    d_0=sqrt(R^2-1/4)-1>1/2.

Here a unique physical circle corner could not have zero u coordinate:
the other endpoint of a unit own interval would have strictly larger
absolute coordinate. The other two-corner orientation cannot have its
positive force entirely in v. Both physical outer corners and their
original weights remain.

W is parallel to V and shares its inner face. Its v interval is
[d_0-1,d_0]. Positive shared length makes both extremes of its u interval
have absolute value strictly below 3/2. Since d_0>1/2, every point of W
therefore satisfies

    |z|^2<9/4+d_0^2
         <d_0^2+2*d_0+5/4=R^2.

This contradicts W's physical boundary status. It covers the entire
original mean on that face without using V torque or any W equation.

## 5. A complete corner comparison used twice

Consider arbitrary x,y>=1/2 with x^2+y^2>=4, and an actual parameter
0<=k<=1. Put

    C=[1-x,2-x] x [y-1-k,y-k].

First

    x+y>12/5.                                          (6)

Indeed, if x+y<=12/5, convexity at fixed sum and x,y>=1/2 gives
x^2+y^2<=(19/10)^2+1/4=193/50<4, a contradiction.

Subtract each C-corner norm squared from x^2+y^2. The four exact
deficits are

    D_LT=2x-1+2ky-k^2,
    D_LB=2x-1+2(1+k)y-(1+k)^2,
    D_RB=4x-4+2(1+k)y-(1+k)^2,
    D_RT=4x-4+2ky-k^2.                                (7)

D_LT is strictly positive when k>0, since 2x-1>=0 and
k(2y-k)>0 for 0<k<1. At k=1 it is also strictly positive:
2x-1+2y-1=2(x+y)-2>0.

For D_LB, use (6), y>=1/2, and 0<=k<=1:

    D_LB=2(x+y)-1+2ky-(1+k)^2
         >14/5-k-k^2>=4/5.                            (8)

As a function of k, D_RB is concave. At its full interval endpoints,

    D_RB(0)=4x+2y-5>4/5,
    D_RB(1)=4x+4y-8>8/5.                              (9)

Here (6) and x>=1/2 were used for the first. Concavity puts every
intermediate D_RB above the smaller endpoint lower bound. Finally,

    D_RT(1)=4x+2y-5>4/5.                              (10)

Thus for 0<k<1 exactly one corner, RT, is left as a possible circle
corner; at k=1 every corner is strictly inside the circle. These are
continuous inequalities on the whole displayed domain, not sampled
orientations or a finite exclusion table.

## 6. Every point-only VW contact is impossible

In the last row of Section 3, let E=P_V-r*u. The actual common vertex is
E+u, and the whole W is

    W=E+u+[0,1]u+[-1,0]v.                             (11)

For its unchanged normal m=alpha*u-beta*v, the full V force is

    F_V=-nu*alpha*u+(mu+nu*beta)*v.

Its u component is nonpositive and its v component strictly positive.
Farthest-own-coordinate comparison therefore puts E.u=-x<=-1/2 and
E.v=y-1>=-1/2. The corner (-x,y) is an actual physical circle corner,
including a tied own coordinate, so

    x,y>=1/2, R^2=x^2+y^2>=4.

The square (11) is exactly C from Section 5 at k=1. Every one of its
four actual corners is strictly inside D_R, contrary to W's boundary
contact. This excludes the complete point-only geometry, all original
normal-cone endpoints and both physical V masks. No fixed-tip selector
or W force equation is used.

## 7. The surviving shared face fixes W's whole mask

Only the first row of Section 3 remains. Thus

    r=1-a, k=b+s in [b,1), m=u.

V's full force is F_V=mu*v-nu*u, with both magnitudes positive.
Exactly the same physical farthest-corner argument gives an actual
circle corner (-x,y) with x,y>=1/2 and R^2=x^2+y^2. The full actual
squares become precisely (A).

Since k>=b>0 and k<1, the first three deficits in Section 5 are strictly
positive. W is contained and physically boundary, so its remaining RT
corner must be on the circle. It is its unique physical circle corner,
and its exact deficit yields

    4x+2ky=4+k^2.                                      (12)

In particular

    x=1+k^2/4-ky/2<5/4,
    y^2=R^2-x^2>4-25/16=39/16>9/4.

Hence y>3/2. This excludes the entire physical V mask with tied v
coordinate y=1/2. The only remaining physical V masks are the unique
corner x>1/2, or its whole two-corner v face x=1/2.

## 8. Original means and zero weights are retained exactly

Write the original V circle resultant as

    F_V=Lambda*(-xi,y), Lambda>0.

If x>1/2 the physical corner is unique, so xi=x. If x=1/2 the two
physical corners are (-1/2,y),(1/2,y). Their full original nonnegative
weights give -1/2<=-xi<=1/2. The actual positive VW magnitude then
forces xi>0, retaining the endpoint xi=1/2 and every permitted mixture.
Thus 0<xi<=x in both masks.

The unchanged force magnitudes are mu=Lambda*y and nu=Lambda*xi.
The original VW mean is M=(1-x,z), with its entire actual interval
y-1<=z<=y-k. The UV application is P_V=(-x+r,y-1).
Taking the original complete V torque about O gives exactly

    mu*(-x+r)+nu*z=0,
    xi*z=y*(x-r).                                    (13)

Since y>3/2 and k<1, this z is strictly positive. Thus x>r.
Using the upper mean bound and xi<=x in (13) gives

    y*(x-r)<=xi*(y-k)<=x*(y-k),
    r*y>=x*k.                                        (14)

Finally k>=b and r=1-a give

    x/y<=r/k<= (1-a)/b=b/(1+a).

No unique-corner force formula has been applied at the physical-two
mask. In particular (13), rather than xi=x, is the operative full mean
equation there. Both endpoints of the actual shared VW segment remain.

## 9. Literal original scope and remaining obligations

In original M6.B6.HEXAGON.D02.L01345 use

    U=2, V=1, W=0, T=3,
    actual boundary path 1,0,5,4,3.

The current single-axis cover gives the full stated local chart in the
sole-UT interface, including V ownership at its actual side interior.
The true degrees remain U3,V2,W3,T2,5_2,4_2. Whenever V and W have
parallel frames, the complete feature therefore satisfies (A)--(D).
The whole point-only VW geometry, opposite shared face, other V mask
and other three W physical circle corners are excluded together.

The same local theorem is available in the opposite-ear original
M6.B6.HEXAGON.D0235.L0134 at U=2,V=1,W=0,T=3, conditional on the
stated actual sole-third-axis and external-V-side feature. There T is
loaded true degree three, which the theorem permits. The reflected
unloaded star at 5 has the analogous conditional use. No T2 equation
or closing-pocket allocation is transferred to that caller.

The remaining chart (A)--(D) is not shown impossible here. Its entire
UT shared/singleton feature, every W3 force, true T equation and every
completion square still require their original treatment. This source
closes no original row or graph parent and changes no ledger flag.

## 10. Exact operative inputs and verification boundary

| Source | SHA256 | Exact use |
| --- | --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Original complete forces, torques, actual means and radial circle coefficients |
| LOADED_TWO_FORCE_BOUNDARY_NEIGHBOR_COMMON_POINT_EXCLUSION.md | 5a95c3255a634f603a47c8311971902f2b8b699e4ebf2d076b21b01fddf941ba | Distinct true V2 applications with the actual physical-boundary W |
| UNLOADED_THREE_FORCE_TOUCHING_RETURNS_STRICT_SUPPORT_SEPARATION.md | 406fce53d22cc20eec43a373a877798dab583a6bd93f684ff124293016c44c87 | Actual T is closed-disjoint from V,W, and the complete opposite-U-vertex reach obstruction |
| D02_ALL_MASK_FREE_UV_EXCLUSION_AND_EXACT_SINGLE_HUB_AXIS_COVER.md | 214475cb4a6fe839b6589a346e12f2aea9be97b958a5229e1c1ff4344740e670 | Section 9's local full-U3 chart; the entire original sole-UT caller has its V-owned entry already established |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Literal original graph/load/degree joins, with all three extras unchanged |
| LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md | 3b3f40af8f62beee8a55b8d4c8d26398097362d88e91d32116885b4ceea96e90 | Same-nine R>2 only for the original callers; local theorem already covers R=2 |

The physical contact cover and every new continuous inequality are
printed in full. No pose sample, angle mesh, numerical optimization,
computational exclusion packet, normal reselection, replaced mean,
false W2/T2 equation, Lean compilation, CI, workflow, ledger edit,
commit or remote write is used.
