# Two strict roof vertices force a same-axis hub interface at a unique circle tip

Date: October 29, 2026 UTC. Author: nonparallel_roof.

**Status: complete proposed hand local exclusion and exact remaining
domain, frozen for full independent and root review.** The new
radius-free angle obstruction removes both genuine perpendicular
hub-interface owners at once. Its two calculations use the original
upper and lower ports separately. No interchange of an adjacent and
an opposite vertex relative to the unique circle corner is used.

For the full unique-circle two-strict-vertex roof feature, every
remaining owned hub interface has the same direction as that hub's
roof normal. The source gives all four remaining physical rows,
including both genuinely shared interfaces with their full original
means. It does not exclude those same-axis rows or declare either
original D02 parent closed.

## 1. A radius-free angle obstruction at either perpendicular owner

Let P1 and P0 be actual points with

    P1=P0+ell*North, ell>0.

Let A,D be actual interior-disjoint unit squares whose original roof
applications P1,P0 lie in the relative interiors of their respective
maximum-nA and maximum-nD sides. Write

    nA=(c,-s), tA=(s,c),
    nD=(C,S),  tD=(-S,C),
    c,s,C,S>0, c^2+s^2=C^2+S^2=1,
    H=c*S+s*C>0, K=c*C-s*S,
    A=P1-[0,1]*nA+[-r,1-r]*tA, 0<r<1,
    D=P0-[0,1]*nD+[-t,1-t]*tD, 0<t<1.              (1)

Thus H=sin(alpha+beta), K=cos(alpha+beta), where
alpha,beta belong to (0,pi/2). The two frame changes are

    nD=K*nA+H*tA, tD=-H*nA+K*tA.                  (2)

Retain an actual positive A--D contact of magnitude rho>0 and
original normal g directed from A into D. At the hub not owning g,
retain its entire unloaded true-three force and torque equations,
with its positive roof force and its actual third neighbor. The
third neighbor has arbitrary degree, load, orientation and mask.

The actual AD supports imply g.P1<=g.P0, because P1 belongs
to A and P0 belongs to D. Thus g.North<=0. For an axis
perpendicular to either displayed roof direction the vertical
component is nonzero. The only possible perpendicular choices
are consequently g=-tA at A or g=-tD at D.

**Angle theorem.** If g is owned by precisely one of A,D and is
perpendicular to that hub's original roof normal, then

    K>H, equivalently alpha+beta<pi/4.               (3)

The actual AD point is a side-interior point of its owner and a
strict vertex of the other square. This is the genuine one-owner
physical singleton feature. No shared side or its variable mean is
included in that feature.

### 1.1. The genuine A-only perpendicular owner

Here g=-tA. Write its actual application as

    W=P1-u*nA-r*tA, 0<u<1.                         (4)

It minimizes g on D. The nD component of g is -H<0, so this minimum
has nD coordinate zero relative to P0. Consequently

    W=P0+v*tD,

where v is 1-t when K>0 and -t when K<0. The remaining K=0 would
make g an actual D axis, contrary to the genuine A-only hypothesis.
Taking the nA component of W-P1=-ell*North+v*tD gives

    u=v*H-ell*s>0.

Therefore v>0, which proves K>0 and v=1-t. In particular W is
the actual upper front vertex of D, with no selected replacement.

Let nu>0 be D's original roof magnitude. D's complete force equation
gives the original exterior vector

    F_C=-nu*nD-rho*tA
       =-(nu+rho*H)*nD-rho*K*tD.                   (5)

Both own components are strictly negative. Its actual D application
is therefore the strict opposite vertex

    Q_C=P0-nD-t*tD.                                (6)

The full original torque of D about P0 is

    det((1-t)*tD,rho*tA)+det(-nD-t*tD,F_C)=0.

Using det(nD,tA)=K and det(tD,tA)=-H, its exact expansion is

    -rho*(1-t)*H + rho*K-rho*t*H-nu*t=0,
    nu*t=rho*(K-H)>0.                              (7)

All magnitudes and t are positive. Equation (7) proves (3).
No equation of A, V or C has been shortened or required here.

### 1.2. The genuine D-only perpendicular owner, in the same coordinates

Here the original D-to-A direction is tD, so g=-tD. Its actual
D-side point has the form

    W=P0-uD*nD+(1-t)*tD, 0<uD<1.                   (8)

It is a minimum-tD support point of A. In (1), the nA coordinate
of that minimum is zero: tD.nA=-H<0 and A extends in -nA.
Thus W=P1+v*tA, where v=-r for K>0 and v=1-r for K<0.
Again K=0 would make the normal an axis of both hubs.

The nD component of W-P0=ell*North+v*tA is

    ell*S+v*H=-uD<0.

Hence v<0. It follows that K>0 and W=P1-r*tA, the lower
front vertex of the unchanged A.

Let mu>0 be A's original roof magnitude. The complete A exterior
vector and its strict support vertex are

    F_B=rho*tD-mu*nA
       =-(mu+rho*H)*nA+rho*K*tA,
    Q_B=P1-nA+(1-r)*tA.                            (9)

The full A torque about P1 expands directly as

    det(-r*tA,-rho*tD)+det(-nA+(1-r)*tA,F_B)=0,
    rho*r*H-rho*K+rho*(1-r)*H+mu*(1-r)=0,
    mu*(1-r)=rho*(K-H)>0.                          (10)

This again proves (3). The unchanged lower and upper labels have
been used throughout. In particular this proof does not infer a
unique-circle symmetry from exchanging the hub names.

Since H>0 and H^2+K^2=1, the strict inequality K>H is exactly
0<alpha+beta<pi/4. This completes the radius-free theorem for
arbitrary ell>0 and every actual exterior contact owner.

## 2. The literal unique-circle two-strict-vertex roof

Now retain distinct actual A,D,V,B,C, with complete original stars

    A:{V,D,B}, D:{V,A,C}, V:{A,D},

where A,D are unloaded true3 and V is loaded true2. No degree,
load or circle-mask assumption is made on B,C. All original positive
pair coefficients, normals and complete means are retained.

Suppose V has exactly one PHYSICAL circle corner. Use its actual
own frame and original circle origin to write

    V=[a-1,a] x [b-1,b], Z=(a,b), a,b>1/2,
    F_V=kappa*Z, kappa>0,
    P1=(a-1,b), P0=(a-1,b-1).                     (11)

The feature considered here has the two original roof normals
strict at those two V vertices and owned by the corresponding hubs:

    n_(A->V)=nA=(c,-s),
    n_(D->V)=nD=(C,S),                             (12)

with the strict component conditions of (1). These roof contacts
cannot have positive shared length, since their normals are not V
axes. The retained strict vertex/vertex singleton convention rules
out a hub vertex carrying its own axis at that singleton. Therefore
P1,P0 are the genuine relative-side-interior hub points of (1), with
ell=1 and both r,t strictly between zero and one.

### 2.1. The full loaded V2 forces the lower angle above pi/4

Let mu,nu>0 be the original AV,DV magnitudes. Its entire equations
are

    mu*nA+nu*nD=kappa*(a,b),
    mu*det(P1,nA)+nu*det(P0,nD)=0.                 (13)

Since P1=P0+North and det(P0,Z)=a-b, the moment equation is

    kappa*(a-b)-mu*c=0.

The horizontal force component then gives

    mu*c=kappa*(a-b)>0,
    nu*C=kappa*b>0.                               (14)

Thus a>b, without assuming a corner-order symmetry at this step.
The vertical force component yields

    S/C=1+((a-b)/b)*(s/c)>1.                       (15)

In particular beta>pi/4, so alpha+beta>pi/4.
Equations (13)--(15) use every original force of V and its actual
unique physical corner. A physical two-corner square with one zero
coefficient is not reclassified as unique to use this argument.

### 2.2. Complete perpendicular-owner exclusion

If the original AD normal has precisely one hub owner and is
perpendicular to that hub's roof normal, the radius-free theorem
gives alpha+beta<pi/4. This contradicts (15).

**Unique-roof theorem.** Both genuine one-owner perpendicular AD
features are impossible in the entire setting (11)--(13). This is
a selection-free implication for these actual original data. It
does not require an equation at B or C or a boundary premise at
the other unloaded hub.

## 3. Complete remaining cover when the original AD normal is owned

Assume now that at least one of A,D owns the unchanged AD normal g.
Every A point lies at or below its maximum-g support W, and every D
point lies at or above the same support. Applying this to P1 and P0
gives g.North<=0. Every available A/D axis has nonzero vertical
component, so the inequality is strict. The entire axis list is

    A-owned: g=nA or g=-tA,
    D-owned: g=-nD or g=-tD.                       (16)

The two sole-owner perpendicular choices have just been excluded.
If both hubs own g, the only compatible equalities in (16) are

    nA=-tD, or -tA=-nD.

Both say K=0, H=1, C=s, S=c. Thus g equals the same roof
direction at A in the first case, or the negative of D's roof
direction in the second. The shared mean remains original.

If only A owns and g=nA, the actual triangle side-normal obstruction
at D gives nD.(-g)=-K>=0. Since K=0 would make g D-owned too,
K<0. The same reasoning at A gives K<0 when only D owns and
g=-nD. These cover all owned normals, without assigning an owner
to a genuine free singleton.

The four exact physical rows follow. Put rho>0 for the original
AD magnitude and keep mu,nu from (13). All application formulas
below are derived from their full original force and torque.

### 3.1. Only A owns AD, in its roof direction

Here g=nA, K<0. D's minimum-nA support is its upper front vertex,
so the original common point and complete geometric constraints are

    W=P0+(1-t)*tD=P1-(S/H)*tA,
    t=1-s/H, S/H<r<1,
    H>s, H>S.                                    (17)

The exterior vectors, original applications and full D moment are

    F_B=-(mu+rho)*nA,
    Q_B=P1-nA-zA*tA, zA=rho*(S/H)/(mu+rho),
    F_C=rho*nA-nu*nD,
    Q_C=P0-nD-t*tD,
    nu*t=rho*(H+K)>0.                             (18)

For Q_C, its nD component is rho*K-nu<0 and its tD component
is -rho*H<0, proving it is the displayed actual vertex. Q_B is
the original back-side mean or point of A; its transverse coordinate
in (18) follows from the entire A torque about P1, not from a choice
of a convenient mean. In particular 0<zA<S/H<r.

### 3.2. Only D owns AD, in its roof direction

Here g=-nD, K<0. A's minimum-nD support is its lower front vertex.
The unchanged point and geometric constraints are

    W=P1-r*tA=P0+(s/H)*tD,
    r=S/H, 0<t<1-s/H,
    H>s, H>S.                                    (19)

The complete exterior data and full A moment are

    F_B=rho*nD-mu*nA,
    Q_B=P1-nA+(1-r)*tA,
    F_C=-(nu+rho)*nD,
    Q_C=P0-nD+zD*tD, zD=rho*(s/H)/(nu+rho),
    mu*(1-r)=rho*(H+K)>0.                         (20)

The strict nA and tA components of F_B have signs negative and
positive. This proves its displayed actual vertex. The D torque
fixes precisely the actual opposite-side application Q_C in (20),
including its shared-mean interpretation when DC is genuinely shared.

### 3.3. Both hubs own AD, with A's roof direction

Now K=0, C=s, S=c, g=nA=-tD. Physical positive shared length
has the entire chart

    t=1-s, c<r<1,
    W=P1-(c+z)*tA,
    0<=z<=r-c.                                   (21)

This is exactly the intersection interval: in D it is
W=P0-z*nD+(1-t)*tD, and in A it lies on the front side.
The displayed interval keeps both actual overlap endpoints and every
original mean between them. Its length is positive; a zero-length
axis contact at two vertices is excluded by the original strict
singleton convention.

The complete force and moment data are

    F_B=-(mu+rho)*nA,
    Q_B=P1-nA-[rho*(c+z)/(mu+rho)]*tA,
    F_C=rho*nA-nu*nD,
    Q_C=P0-nD-(1-s)*tD,
    rho*(1-z)=nu*(1-s).                           (22)

In particular z is not set to zero before applying torque. The
unshared expression in (18) is not silently used for this row.

### 3.4. Both hubs own AD, with D's roof direction

Here K=0, C=s, S=c, g=-nD=-tA. The complete actual shared chart is

    r=c, 0<t<1-s,
    W=P1-z*nA-c*tA=P0+(s+z)*tD,
    0<=z<=1-t-s.                                 (23)

Again both endpoints are retained in the original mean interval.
The full equations give

    F_B=rho*nD-mu*nA,
    Q_B=P1-nA+(1-c)*tA,
    F_C=-(nu+rho)*nD,
    Q_C=P0-nD+[rho*(s+z)/(nu+rho)]*tD,
    rho*(1-z)=mu*(1-c).                           (24)

Every strict exterior vector in (22),(24) has its actual unique hub
vertex as displayed. The parallel exterior vector has the precise
original opposite-side application fixed by full hub torque.

### 3.5. The entire remaining angular interval

The genuine rows (17),(19) give H>max(s,S). Since K<0, their
angle theta=alpha+beta belongs to (pi/2,pi). The inequalities
sin(theta)>sin(alpha) and sin(theta)>sin(beta) imply respectively

    2*alpha+beta<pi, alpha+2*beta<pi.

Adding gives theta<2*pi/3. The shared rows have theta=pi/2.
Thus every remaining owned row satisfies the useful closed/strict
combination

    pi/2<=alpha+beta<2*pi/3,
    beta>pi/4,
    g=nA or g=-nD.                                (25)

This is a cover of all actual owned AD possibilities under the stated
unique-roof feature. It does not assert that every point of the
displayed necessary domains is geometrically realizable.

## 4. Coupled actual-point inequalities available in every remaining row

Each actual exterior neighbor contains its original application plus
its unchanged inward unit normal. For completeness, in a unit's own
axes the coordinates of any unit minimum-support normal lie in
[-1,1]; adding that normal to a minimum-support point preserves both
own coordinate intervals. A zero component preserves the whole side
coordinate. This proves the statement for side means and endpoints
as well as strict vertices, without assuming the neighbor owns the
normal.

Consequently, if the actual B,C are contained in D_R about the same
origin, every row above retains the simultaneous necessary bounds

    |Q_B+F_B/|F_B||^2<=R^2,
    |Q_C+F_C/|F_C||^2<=R^2.                        (26)

The complete positive stars make F_B,F_C nonzero. Formula (26)
retains the transverse coordinates of the actual original means.
Replacing it by only a scalar support bound can lose this information.
In a parallel exterior row it includes, for example,

    |P1-2*nA-zA*tA|^2<=R^2

for (18), with the distinct shared expression for zA in (22).
No whole neighbor has been replaced by the point used in this
necessary containment test.

## 5. Both literal D02 callers and the exact credit boundary

In each original row D02.L135 and D02.L1345, retain rim
A--V--D--C--N--B--A and chord AD, with the exact labels

    A=0, V=1, D=2, C=3, N=4, B=5.

Their full stars are A3,D3,V2 as used above. B,C are loaded true2;
N is unloaded true2 in L135 and loaded true2 in L1345. All original
equations at B,C,N and all three completing physical units remain.
The new proof has imposed no reduced equation on any of them.

The already recorded three-port cover identifies the present feature
as its unique physical Type III. If the separate compatible initial
selection assembly has established that the actual roof and AD
normals are owned, its conclusion may be used as an input here.
This source supplies no missing nonempty common-selector domain,
does not reselect a normal of an extracted certificate, and does not
apply a unique-corner rule to a physical two-corner mask.

At this literal feature, both sole perpendicular owners are now
excluded, and (17)--(24) give the full remaining same-axis domain.
Both original D02 rows remain open. Their Type I and Type II domains
and the still surviving Type III same-axis rows require their own
complete support or completion exits.

## 6. Exact mathematical interfaces and verification boundary

| Source | SHA256 | Exact use |
| --- | --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Original full forces, shared means, physical masks and strict vertex/vertex singleton convention |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Only K<=0 for a surviving same-axis owner; the perpendicular moment obstruction is proved directly |
| UNIQUE_CIRCLE_TRIANGLE_TIP_THREE_PORT_TYPES_AND_HUB_INTERFACE_OWNER_COVER_2026_10_29.md | 8266220efbb8ce769de90a90e27e86997400575d0b8bb80f5843af38ca447073 | Literal Type III feature name and separate conditional owner entry; its full V2 identities are reproduced here |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Both original graph/load roles, exact degrees and retained three extras |

The actual-point fact in Section 4 was already proved in Section 3
of LOADED_TWO_APPLICATION_FULL_STAR_BOUNDARY_FREE_CONCURRENCE_DICHOTOMY.md
and restated in SUPPORT_POINT_UNIT_TRANSLATION_AND_PERPENDICULAR_PARALLEL_W_UNLOADED_TERMINAL_EXCLUSION.md.
Its complete short face proof is reproduced here; no later caller of
either source is imported.

All algebra above concerns complete continuous features. No pose
sample, angle grid, new packing certificate, original force deletion,
mean change, metadata or flag edit, Lean/Lake, CI, remote mutation or
merge is used. Separate full independent review is still required.
