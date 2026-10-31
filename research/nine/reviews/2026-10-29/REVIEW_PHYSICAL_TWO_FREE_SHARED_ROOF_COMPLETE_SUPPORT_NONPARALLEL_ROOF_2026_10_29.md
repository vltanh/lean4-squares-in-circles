# Independent full review: every physical-two free/shared roof is excluded

Date: October 29, 2026 UTC. Reviewer: nonparallel_roof.

## 1. Decision and exact reviewed object

**PASS unchanged** for the complete selection-free free-roof/shared-
roof exclusion, its entire continuous shared interval, both physical
circle-coefficient endpoints, every strict-shift third-support row,
both whole-side endpoint geometries and the two literal D02 callers.

Reviewed source:

    PHYSICAL_TWO_CORNER_FREE_ROOF_SHARED_OTHER_ROOF_COMPLETE_SUPPORT_EXCLUSION_2026_10_29.md
    SHA256 100ab931815c26dd35f36ac2b6a0ea40bf39695ccd59f8b0ad7d135c72940d51
    471 LF lines; 18540 bytes.

I read all 471 lines and reconstructed the entire proof independently,
including the original force/moment algebra and the uniform exact
support estimate. I authored neither this source nor its new physical-
two arguments and made no edit. The analogous unique-circle manuscript
that I authored is expressly not an input and supplies no missing
slope bound or radial-membership premise to this review.

The source also does not depend on the new five-application manuscript.
Its common-physical-endpoint argument is checked directly here, so
there is no dependency cycle between the two new results.

## 2. Scope and complete preceding feature input

The original full stars are A:{V,D,B}, D:{V,A,C}, V:{A,D}.
The hubs are unloaded true3, V is loaded true2 with TWO PHYSICAL
circle corners, and B,C are distinct actual exterior units of
arbitrary degree, load and mask. Every other original unit remains.

AV is a strict free vertex/vertex singleton. DV has positive
physical shared length, with its original mean over the whole
closed overlap. The original AD and exterior contacts retain
all owners and means. The free V normal and a V side-axis
normal cannot be parallel, so no extra nonparallel assumption
is silently inserted.

The accepted preceding physical-two theorem applies literally
on R>sqrt(2), d<3/2. The new source has the stronger stated
bound d<5/[2*(1+sqrt(2))], so it lies in that complete scope.
The preceding support cover removes every transverse or outer
port and puts the shared roof on the inner side, with the
free roof at one of its two endpoints.

The resulting whole-data rotation/reflection gives

    V=[-1/2,1/2] x [d,d+1], P=(-1/2,d),
    n=(xi,zeta), xi,zeta>0,
    F_V=k*(chi,d+1), -1/2<=chi<=1/2.

Both physical upper corners remain when an individual
coefficient is zero. The sign chi>0 later derived in this
ordered left-corner chart is a force consequence, not a
reclassification of the physical mask. Reflection covers
the opposite ordered corner and its other zero endpoint.

## 3. Full original V2 torque supplies the decisive inequality

The actual shared D has the aligned chart

    D=[l,l+1] x [d-1,d], -3/2<l<1/2,
    M=(m,d), max(l,-1/2)<=m<=min(l+1,1/2).

The strict l bounds express actual positive overlap;
the mean interval remains closed. Incoming normals
at V are n and North. The complete V equations are

    mu*n+nu*North=k*(chi,d+1),
    nu*m=mu*(d*xi+zeta/2).

The torque sign is correct: the V-outward free force
has moment mu*(d*xi+zeta/2), while the original South
shared force contributes -nu*m. Each actual circle
atom has zero origin moment.

For r=mu*xi>0, j=zeta/xi>0 and T=nu/r>0, this gives

    r=k*chi, T*m=d+j/2,
    chi>0, m>0, T>=2*d+j>j.

The endpoint m=1/2 is included in the weak first
inequality. No changing-sign quantity is divided
out. This replaces the unavailable unique-circle
incoming-slope restriction; neither j<=1 nor a
physical-two radial-concurrence membership is used.

## 4. Complete actual shift cover and the forced A/D chart

For l<-1/2, P is side-interior on D's top. The short
segment P-t*n lies in the open interior of A by the
strict original A support and also lies inside D
because xi,zeta>0. This excludes the entire negative
shift, using actual positive overlap to put P strictly
between D's vertical sides.

For -1/2<l<1/2, A must reach rightward from P to
touch D. Its strict outward positive-positive normal
therefore forces inward axes

    u=(c,-s), v=(-s,-c),
    c,s>0, c^2+s^2=1, j>c/s.

The unique rightmost A vertex P+u lies strictly
between D's horizontal sides. If it were to the
right of D's left side, nearby A interior would
overlap D interior; if left, the units would miss.
Thus l=-1/2+c and the actual AD contact is the
singleton Q=P+u, side-interior on D's left side.
The original A-to-D direction is exactly East.

This is forced geometry, not a convenient frame
or a selected normal. It includes every strict
shift and keeps m in [-1/2+c,1/2]. The case l=-1/2
is deliberately retained for a separate full proof.

## 5. Both full hubs and every A exterior support

With original AD magnitude rho>0, the complete forces are

    F_AB=(-r-rho,-r*j),
    F_DC=(rho,-nu).

The latter strictly exposes D's lower-right corner
K=(1/2+c,d-1), which is therefore the actual DC
application. Full D torque about K gives

    rho*(1-s)=nu*(1/2+c-m).

Writing L=rho/r and sigma=nu/rho, the complete
mean bound m<=1/2 gives

    sigma<=c/(1+s), T<=L*c/(1+s).

No D term or original mean is suppressed in these
identities.

The A component along v is always positive. The
sign of the component along u therefore exhausts
its actual support as P+v, the full side P+v+q*u,
or P+u+v. I independently recomputed the full torque
about P in each case:

    near vertex: L*(s-c)+(s*j-c)=0;
    side:        L=(s*j-c)/c, q=s^2-c*s/j;
    far vertex:  L=((s-c)*j-(s+c))/c.

The side row derives 0<q<s^2<1 from j>c/s. It does
not assume a fixed singleton mean or drop the side
as an artificial endpoint. The vertex rows have
the same signs as the full original force equation.

In the side row, T<j follows from
T<=(s*j-c)/(1+s). In the far-vertex row it follows
from T<=((s-c)*j-(s+c))/(1+s). Both contradict
the already derived T>j. The latter numerator is
positive whenever the original rho is positive;
no invalid division by it is made.

The remaining near-vertex torque has s*j-c>0,
so it forces c>s. No earlier c/s ordering was
imported from the unique-mask theorem.

## 6. Uniform support contradiction for the remaining strict shift

At the actual DC corner K and original normal,

    H_C=(1/2+c+(1-d)*sigma)/sqrt(1+sigma^2).

Set delta=max(d-1,0). Using the full sigma bound
and the positive coefficient 1/2+c gives

    H_C>=((1/2+c)*sqrt(1+s)
               -delta*sqrt(1-s))/sqrt(2).

The source's exact single-interval estimate is
correct on c>s, or 0<s<1/sqrt(2)<5/7:

    c^2-(1-3*s/7)^2=(2*s/49)*(21-29*s)>0,
    (1+s)-(1+3*s/7)^2=(s/49)*(7-9*s)>0.

The compared square roots are positive. Therefore

    (1/2+c)*sqrt(1+s)
      >(3/2-3*s/7)*(1+3*s/7)
      =3/2+s*(3/14-9*s/49)>3/2.

The final coefficient has reserve 57/686 at the
larger rational comparison endpoint 5/7. This
is a uniform algebraic bound, not a sampled
orientation or a missing angular subcase.

Consequently H_C>(3/2-delta)/sqrt(2)>d. For d<=1
the last comparison follows from 3/(2*sqrt(2))>1.
For d>1 it is exactly the stated broad bound
(1+sqrt(2))*d<5/2. The actual contained C lies
beyond H_C, contradicting its universal minimum-
support budget d. Its actual full equation and
circle mask were never replaced.

## 7. Entire whole-side endpoint, including every shared AD mean

At l=-1/2 the actual D is [-1/2,1/2] x [d-1,d].
Together with V it fills the local right half-plane
at P. A's tangent quadrant lies in the left half-plane.

For strictly tilted A both inward axes have negative
horizontal component, so AD is exactly the singleton
P. The original A-to-D direction has g_x>=0,g_y<=0
and is independent of n=(xi,zeta). Their positive
sum is strict in A's outward cone. Full A3 therefore
exposes its actual opposite vertex, and full torque
about the common application P forces the external
unit direction f=(u+v)/sqrt(2).

The physical left-half-plane geometry gives
f_x<=-1/sqrt(2), |f_y|<=1/sqrt(2), so

    h_A(f)=-(1/2)*f_x+d*f_y+sqrt(2)
      >=(5/2-d)/sqrt(2)>d.

This is a direct contradiction at actual B, with
no new generic selector and no unique circle
vector assumption. The possible normal-axis
endpoints included in the weak g signs do not
invalidate the independence or support argument.

For aligned A, strict positive-positive AV support
forces its Southwest quadrant. Thus A is exactly
[-3/2,-1/2] x [d-1,d], and AD is its whole vertical
shared side. Keep W=P-z*North, 0<=z<=1. The entire
A3 force and moment give

    F_AB=(-r-rho,-r*j), P_B=(-3/2,d-1),
    r*(j-1)=rho*(1-z).

For L=rho/r>0 and tau=j/(1+L), this yields
0<tau<=1, including both z endpoints. Its actual
support is

    H_B=(3/2+(1-d)*tau)/sqrt(1+tau^2)
       >=(3/2-delta)/sqrt(2)>d.

The numerator lower bound is positive, so the
denominator comparison has the correct direction.
No AD endpoint or DV mean is moved. Aligned three-
and four-unit junctions are both covered by this
direct support argument; no independent matched
normal parameter is presumed.

These tilted and aligned cases exhaust the entire
endpoint. In particular the new proof does not
confuse a common physical point with a variable
mean elsewhere on a shared contact.

## 8. Radius, literal callers and residual boundary

I rechecked the exact original-radius reserves
3041/1600, 31/57600 and 13/420 printed in Section 8.
They include both closed original endpoints and
put the entire original interval strictly inside
the broad local domain. The larger artificial
equality d=5/[2*(1+sqrt(2))] is not claimed.

The literal original roles A=0,V=1,D=2,C=3,N=4,B=5
preserve the six rim edges and chord02. A,D retain
their true unloaded degree three, V,B,C their
loaded degree two. N remains unloaded in L135
and loaded in L1345. All three completing units
and every original extra equation remain.

The complete consequence is that a free roof at
physical-two V forces its other roof to be a
physical singleton. In the West/strict chart,
the West endpoint t=1/2 is consequently excluded
only in this free-roof feature, because that
endpoint requires positive physical shared length.
It is not removed from the general physical-two
domain. No unique-corner fixed-tip selector is
applied to the resulting two singletons.

The source does not assert all roofs owned, AD
owned, either complete remaining chart impossible,
or either whole original D02 row closed.

## 9. Exact checked inputs and verification boundary

| Input | LF / bytes | SHA256 |
| --- | --- | --- |
| PHYSICAL_TWO_CORNER_LOADED_TRIANGLE_TIP_TRANSVERSE_PORT_EXCLUSION_AND_INNER_FACE_DOMAIN_2026_10_29.md | 476 / 21179 | 317de21d86ca2559dd225911ced5358f1049329d7c2a8a3892d193749a188d1c |
| PHYSICAL_CONTACT_STRESS.md | 399 / 17993 | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | 244 / 11952 | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 |

All three direct pins match. The complete preceding
physical-two theorem was reviewed in full at these
unchanged bytes. The full physical force/torque
source was read earlier in this continuation, and
the original chord-02 graph/load/degree contract
was checked again for both literal callers.

This is a full independent review of every new
case and operative join. It does not claim a new
recursive audit of every historical physical-
certificate dependency. No selected-normal
extension is required by the new theorem.

No pose sampling, angular mesh, computational
packing certificate, Lean/Lake, CI/workflow,
source repair, metadata or original flag edit,
remote mutation or merge was used.
