# Full independent review: unique-circle two-strict-roof perpendicular exclusion and remaining owned domain

Date: October 29, 2026 UTC. Reviewer: roof_review.

**Verdict: PASS unchanged for the exact displayed theorem and all four
remaining owned-interface rows.** The radius-free obstruction is proved
separately at each possible sole perpendicular owner. The unique-circle
caller then excludes both using its full original V2 equation. No
interchange of the upper and lower physical vertices is needed or used.
The complete shared-interface means, including both endpoints, survive
in the two shared rows. The same-axis rows are necessary domains, not
exclusions, and neither original D02 row is thereby closed.

This is a full independent mathematical review. I did not author or
contribute a calculation to the source under review. I read all 430 LF
lines, reconstructed every operative section, and checked the required
interfaces against the previously fully read sources listed below. This
report is separate from the theorem; no source repair is requested.

## 1. Frozen object and complete review scope

The reviewed file is
UNIQUE_CIRCLE_TWO_STRICT_ROOF_PORTS_PERPENDICULAR_INTERFACE_EXCLUSION_AND_COMPLETE_SAME_AXIS_DOMAIN_2026_10_29.md.

Its exact identity at review completion is:

    SHA256 f8cce87f5bbc22ba898db4029676dd84f1fb1c448212a809ee6809cffc5056eb
    17046 bytes; 430 LF lines.

The substantive checks cover the arbitrary positive roof separation in
Section 1; both unchanged-chart perpendicular computations; the full
unique physical-circle force and moment; the physical owner enumeration;
all four point and shared-side charts; every exterior force, application,
and moment formula; the angular interval; both actual-point containment
inequalities; and both original D02 graph/load callers.

I independently recomputed the four direct dependency hashes. All match
the exact pins in the frozen source:

| Direct dependency | Verified SHA256 | Literal interface checked |
| --- | --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Original positive forces, full shared means, physical masks, strict singleton convention |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Actual triangle owner-axis dot-product obstruction |
| UNIQUE_CIRCLE_TRIANGLE_TIP_THREE_PORT_TYPES_AND_HUB_INTERFACE_OWNER_COVER_2026_10_29.md | 8266220efbb8ce769de90a90e27e86997400575d0b8bb80f5843af38ca447073 | Literal Type III geometry and separately conditional owner entry |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Both original graph/load roles and retained completion units |

The containment fact attributed to two other sources is fully proved
again in Section 4. No theorem about their later callers is imported.
The new perpendicular calculation does not depend on a boundary return,
on either exterior unit being loaded, or on any normal selector.

## 2. Radius-free geometry and the actual ownership hypotheses

The initial chart is internally consistent for every ell>0:

    P1=P0+ell*North,
    nA=(c,-s), tA=(s,c), nD=(C,S), tD=(-S,C),
    A=P1-[0,1]nA+[-r,1-r]tA,
    D=P0-[0,1]nD+[-t,1-t]tD,
    0<r,t<1, c,s,C,S>0,
    H=c*S+s*C, K=c*C-s*S.

Both frames have positive orientation. Direct dot products give
nD=K*nA+H*tA and tD=-H*nA+K*tA. Thus H>0,
H^2+K^2=1, and H,K are sine and cosine of alpha+beta,
where alpha,beta lie strictly between zero and pi/2.

The support inequality g.P1<=g.P0 follows from actual contact:
A is in its closed maximum-g half-plane and D in the opposite
minimum-g half-plane. Therefore g.North<=0. Each perpendicular
axis has nonzero vertical component, leaving exactly g=-tA or
g=-tD. This inference does not assume that the normal lines meet
inside a unit or that a selected shared mean is a physical vertex.

The genuine one-owner feature is a physical singleton at a relative
side-interior point of its owner and a strict vertex of the other hub.
The strict vertex/vertex convention forbids an own-axis normal at an
owner vertex. A positive shared segment would have both owners.
Thus the strict parameters used in each perpendicular calculation are
the actual physical owner conditions, not added genericity assumptions.

This theorem requires the opposite hub's entire unloaded true3 star.
It does not assume an unloaded equation at the owning hub. In its
later unique-circle caller both original hubs are unloaded true3, so
each of the two applications is justified independently.

## 3. Genuine A-only perpendicular owner, reconstructed directly

For g=-tA the actual AD application is

    W=P1-u*nA-r*tA, 0<u<1.

To minimize g on D, its nD coordinate must be zero because
g.nD=-H<0 while the nD coordinate interval is [-1,0].
Its tD coordinate is 1-t if K>0 and -t if K<0. The case
K=0 would make the normal D-owned as well, so is not a sole-owner
feature. Write W=P0+v*tD.

Taking the nA component of W-P1 gives

    u=v*H-ell*s>0.

It follows that v>0. Because -t<0<1-t, this proves K>0 and
v=1-t. No exchange of the two roof labels has been made.

With the actual positive roof magnitude nu and AD magnitude rho,
the complete D force equation gives

    F_C=-nu*nD-rho*tA
       =-(nu+rho*H)*nD-rho*K*tD.

Both own components are strictly negative. Its original D application
must therefore be Q_C=P0-nD-t*tD, including if the external
neighbor has another owner, load, or degree. No exterior equation is
needed for this inference.

The two nonzero terms in the complete D moment about P0 are

    det((1-t)tD,rho*tA)=-rho*(1-t)*H,
    det(-nD-t*tD,F_C)=rho*K-t*(nu+rho*H).

Their sum is exactly zero precisely when

    nu*t=rho*(K-H).

The left side is strictly positive. Hence K>H, and because
alpha+beta belongs to (0,pi), this is alpha+beta<pi/4.
The positive ell disappeared only after its geometric sign was used.

## 4. Genuine D-only perpendicular owner in the unchanged chart

For g=-tD, the actual D-side application has the form

    W=P0-uD*nD+(1-t)*tD, 0<uD<1.

Here the D-to-A direction is tD. The minimum-tD support of A
has zero nA coordinate since tD.nA=-H<0. Thus W=P1+v*tA,
where v=-r if K>0 and v=1-r if K<0. Again K=0 is a
both-owned case and is not silently discarded from the whole domain.

The nD component of W-P0 is ell*S+v*H=-uD<0.
Consequently v<0, K>0, and W=P1-r*tA. This is a direct
calculation at the same upper A and lower D as in Section 3.

The complete A force equation and actual strict exterior support are

    F_B=rho*tD-mu*nA
       =-(mu+rho*H)*nA+rho*K*tA,
    Q_B=P1-nA+(1-r)*tA.

The AD moment is rho*r*H. The exterior moment is
-rho*K+(1-r)*(mu+rho*H). Their sum gives

    mu*(1-r)=rho*(K-H)>0.

This is the second required proof of the same angle obstruction.
In particular, the source does not reflect the unique circle corner
or exchange a vertex adjacent to that corner with its opposite vertex.
The asymmetry that would invalidate such a shortcut is respected.

## 5. Literal unique-circle V2 and exclusion of both perpendicular rows

The caller has the actual unique physical circle corner Z=(a,b),
a,b>1/2, and the two actual strict roof vertices

    V=[a-1,a] x [b-1,b],
    P1=(a-1,b), P0=(a-1,b-1),
    F_V=kappa*Z, kappa>0.

The incoming hub-owned roof normals are nA and nD as above.
They are non-axis normals at V, so neither roof can be a shared
side. The strict singleton convention makes each original hub
application a genuine side-interior point, supplying 0<r,t<1
and ell=1 without an extra physical assumption.

The entire V force and moment are retained:

    mu*nA+nu*nD=kappa*Z,
    mu*det(P1,nA)+nu*det(P0,nD)=0.

Using P1=P0+North and det(P0,Z)=a-b, the moment is
kappa*(a-b)-mu*c=0. The horizontal force gives

    mu*c=kappa*(a-b)>0, nu*C=kappa*b>0.

The vertical force then gives

    S/C=1+((a-b)/b)*(s/c)>1.

Thus a>b and beta>pi/4 follow from the unchanged full star.
Each genuine perpendicular owner contradicts the separately proved
alpha+beta<pi/4. No arbitrary choice of which unique-circle
vertex is upper or lower occurs after fixing this Type III chart.

The physical-mask scope is essential and correct. A physical
two-corner V with one zero coefficient remains physical-two and
cannot use this unique-corner identity or beta>pi/4. The local
radius-free angle theorem can be used elsewhere only with its
actual hub-side-interior roof hypotheses, not by setting a vector
component to zero in a different vertex-owner chart.

## 6. Exhaustive remaining owner list and the two sole same-axis rows

For an owned AD normal, g.North<=0 is strict because every
available A/D axis has nonzero vertical component. The complete list
is A-owned g=nA or -tA, and D-owned g=-nD or -tD.
The sole perpendicular choices have been excluded. The only equalities
allowing both owners are nA=-tD or -tA=-nD. Either gives
K=0,H=1,C=s,S=c. Thus no other owned direction is omitted.

For only A owning g=nA, the triangle owner-axis inequality at D
is nD.(-g)=-K>=0. Equality would give both owners, so K<0.
The support of D minimizing nA has zero nD coordinate and tD
coordinate 1-t. Equating this point with a point on A's front side
gives the exact first row:

    W=P0+(1-t)tD=P1-(S/H)tA,
    t=1-s/H, S/H<r<1, H>s, H>S.

Its complete exterior data are

    F_B=-(mu+rho)nA,
    Q_B=P1-nA-zA*tA, zA=rho*(S/H)/(mu+rho),
    F_C=rho*nA-nu*nD,
    Q_C=P0-nD-t*tD, nu*t=rho*(H+K)>0.

At A the AD moment is rho*S/H and the exterior moment is
-(mu+rho)zA. At D the summed moments are rho*(H+K)-nu*t.
The own components of F_C are rho*K-nu<0 and -rho*H<0,
so Q_C is its actual strict vertex. The parallel exterior Q_B is
the actual side point or complete mean fixed by torque; 0<zA<S/H<r.

For only D owning g=-nD, the separate triangle inequality at A
again gives K<0. Minimizing nD on A and equating the point on
D's front side gives the second row:

    W=P1-r*tA=P0+(s/H)tD,
    r=S/H, 0<t<1-s/H, H>s, H>S.

The complete exterior data are

    F_B=rho*nD-mu*nA,
    Q_B=P1-nA+(1-r)tA,
    F_C=-(nu+rho)nD,
    Q_C=P0-nD+zD*tD, zD=rho*(s/H)/(nu+rho),
    mu*(1-r)=rho*(H+K)>0.

At A the summed moments are mu*(1-r)-rho*(H+K).
The full D moment fixes zD, with 0<zD<s/H<1-t.
The own components of F_B have signs negative and positive, as
required for the displayed actual corner. The parallel exterior
application keeps its original point or shared-mean interpretation.

## 7. Both shared-interface rows, with every original mean endpoint

When both hubs own the normal, their frames are parallel up to a
quarter turn. A zero-length axis contact would put both units at
vertices and violate the original strict singleton convention.
Therefore these rows have genuine positive overlap, not an assumed
point contact with an axis normal.

For g=nA=-tD, express both units in the A frame relative to P0.
Since P1=-s*nA+c*tA relative to P0, their support intervals
meet only when t=1-s. The overlap in the tA coordinate is
[c-r,0], which has positive length exactly when r>c. This proves
the entire third chart, including the mean variable:

    c<r<1, t=1-s,
    W=P1-(c+z)tA=P0-z*nD+(1-t)tD,
    0<=z<=r-c.

The original A moment uses c+z, not c alone. It gives

    F_B=-(mu+rho)nA,
    Q_B=P1-nA-[rho*(c+z)/(mu+rho)]tA.

At D, F_C=rho*nA-nu*nD has strictly negative own components,
and Q_C=P0-nD-(1-s)tD is the actual corner. Its AD moment
is -rho*z; the exterior moment is rho-nu*(1-s). Thus
rho*(1-z)=nu*(1-s), exactly as written. Both z=0 and
z=r-c remain, and the parallel exterior coordinate is strictly
less than c+z<=r. No overlap endpoint is substituted for the mean.

For g=-nD=-tA, matching the other physical support gives
r=c and the overlap in the nA coordinate [t-1,-s]. Its
positive length is exactly t<1-s, giving the complete fourth chart:

    r=c, 0<t<1-s,
    W=P1-z*nA-c*tA=P0+(s+z)tD,
    0<=z<=1-t-s.

The actual exterior data are

    F_B=rho*nD-mu*nA,
    Q_B=P1-nA+(1-c)tA,
    F_C=-(nu+rho)nD,
    Q_C=P0-nD+[rho*(s+z)/(nu+rho)]tD.

The complete A moment is rho*z-rho+mu*(1-c)=0,
giving rho*(1-z)=mu*(1-c). The complete D moment fixes
the side coordinate involving s+z. It is strictly smaller than
s+z<=1-t. Both endpoints of z are retained, even where the
original application belongs to more than one physical side boundary.

The nonparallel exterior vectors in both shared rows force exactly
the displayed strict hub vertex. The parallel exterior vectors leave
a side support whose original application is fixed by the full torque.
None of these statements imposes an exterior degree, mask, or load.

## 8. Remaining angles and simultaneous actual-point constraints

In the sole-owner rows, theta=alpha+beta lies in (pi/2,pi)
and H>sin(alpha),H>sin(beta). For alpha,beta in (0,pi/2),
these imply theta<pi-alpha and theta<pi-beta, respectively.
Adding gives theta<2*pi/3. The shared rows have theta=pi/2.
Together with the actual V2 identity, the complete remaining cover is

    pi/2<=alpha+beta<2*pi/3, beta>pi/4,
    g=nA or g=-nD.

The endpoint pi/2 is retained precisely by the two shared charts.
The strict upper endpoint follows from genuine side-interior geometry;
the source does not treat it as a closed endpoint or assert sufficiency
of these necessary inequalities for a packing to exist.

For any contained actual exterior unit and any of its minimum-support
points Q for an inward unit normal f, Q+f remains in that unit.
In its own coordinates a positive component of f starts at the lower
side, a negative component starts at the upper side, and its absolute
value is at most one. A zero component leaves the original side
coordinate unchanged. This proves the fact at all means and endpoints.

Applying it separately to the actual B and C yields simultaneously

    |Q_B+F_B/|F_B||^2<=R^2,
    |Q_C+F_C/|F_C||^2<=R^2.

The vectors are nonzero because they are the original positive
external contact forces; their displayed coordinates also show this.
These are bounds on actual points of the retained units. The source
does not replace either exterior square by a convenient support point
or forget the shared z dependence in a parallel exterior formula.

## 9. Both original rows and the exact adoption boundary

For D02.L135 and D02.L1345 the literal graph retains the rim
A--V--D--C--N--B--A and chord AD, with A=0,V=1,D=2,
C=3,N=4,B=5. A,D are unloaded true3 and V,B,C are loaded
true2. N is unloaded true2 in L135 and loaded true2 in L1345.
The three completing units remain, so the whole original nine-unit
object, all physical masks, and all original equations are retained.

The new local theorem requires no equations at B,C,N and does not
replace any of them by an unloaded or boundary-free model. Their full
load equations and the full original radius window remain obligations
of the original row. The same applies to the completion units.

The Type III identification and owner entry are literal interfaces
from the separately accepted three-port cover. When roof or AD
ownership is obtained from compatible initial selection, that entry
keeps its existing explicit nonempty common-open-domain requirement.
This source neither constructs a missing common domain nor reselects
an extracted certificate. Its perpendicular implication is selection
free once the stated actual ownership data hold.

The manuscript excludes both genuine sole perpendicular owners and
records the whole surviving same-axis/shared domain. Type I, Type II,
and these surviving Type III rows remain to be resolved. It gives no
whole D02 closure, original flag change, or numerical case-count credit.

## 10. Verification and final disposition

All 430 source lines and all operative direct interfaces were reviewed.
The exact target identity and all four printed source pins match.
Every full-star sign and moment above was reconstructed algebraically;
the two perpendicular owners were checked separately without a symmetry
shortcut. All positive-overlap endpoints and both original graph/load
callers were included.

No numerical pose, angle grid, packing certificate, Lean/Lake run,
CI action, source edit, metadata edit, flag edit, or publication was
used in this review. No defect, missing owner row, endpoint repair,
or narrowing of the displayed feature is required.

**Final disposition: PASS unchanged at the exact frozen hash above.**
Adoption may credit this full perpendicular exclusion and exact
remaining owned domain, while retaining every stated conditional entry
and every still-open original-row obligation.
