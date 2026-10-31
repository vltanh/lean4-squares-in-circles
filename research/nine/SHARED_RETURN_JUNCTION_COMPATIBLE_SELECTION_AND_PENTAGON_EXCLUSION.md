# A shared return junction admits a compatible selection and excludes the coincident pentagon end

Date: October 28, 2026 UTC. Author: root continuation.

**Status: complete proposed selection theorem, force-free bridge lemma and
whole shared-HC coincidence interface; frozen for separate full independent
review.** No whole original fine or coarse family is declared closed.
The selection is made on the physical packing before obtaining multipliers.
It is explicitly compatible with the earlier nondense S-root side-bias
selection; that compatibility is not replaced by a genericity assertion.

Retain all nine actual closed unit squares, disjoint open interiors, the
original containing circle with center O, and

    79/40 <= R <= sqrt(1105)/16,
    d = sqrt(R^2-1/4)-1 < 61/60,
    epsilon = max(d-1,0) < 1/60.

Every original true degree, force, actual application, shared-side mean,
physical circle mask and individual zero circle coefficient remains. The
local geometric lemma below has no circle premise. The certificate and
pentagon applications use the stated original window.

## 1. The exact shared junction and its two independent strict intervals

Consider three actual units D,C,H with

    D intersection C = D intersection H = {P},

where these two contacts are physical vertex/vertex singletons, and C,H
share a positive-length side containing P. Suppose D,H are physically
circle-clear and C physically touches the circle. Normalize D's real frame
by a rigid chart to

    P=(0,0), D=[0,1]^2.

The full shared side of C,H starts at P. Indeed P is a vertex of each
by the singleton hypotheses; the common collinear sides both have unit
length. Choose the one possible diagonal reflection so that, for some
angle 0<u<pi/2, the complete actual frames are

    a=(-sin u, cos u), b=(-cos u,-sin u),
    C=P+[0,1]a+[0,1]b,
    H=P+[0,1]b+[0,1](-a).                              (1)

To verify exhaustiveness, C,H together occupy a half-plane tangent sector
of angle pi at their common endpoint. D occupies its quadrant in the
complementary half-plane. The two remaining angular gaps have total pi/2.
They are both strictly positive: a zero gap would give D a positive-length
shared side with C or H, contrary to its singleton intersections. This
gives exactly the interval for u and the chart (1), after interchanging
the coordinate axes if necessary.

For a strict normal from D into either other unit write

    n(phi)=(-cos phi,-sin phi), 0<phi<pi/2.

Its strict inward projections on C's two axes are sin(u-phi) and
cos(u-phi), so the complete strict D-to-C interval is

    0<phi_C<u.

Its strict inward projections on H's two axes are cos(u-phi) and
sin(phi-u), so the complete strict D-to-H interval is

    u<phi_H<pi/2.                                      (2)

No fourth actual unit contains P. The two remaining gaps each have angle
strictly less than pi/2, whereas every unit tangent sector has angle at
least pi/2. A connected tangent sector cannot occupy both disjoint gaps.
Thus this is a three-unit junction, with no matched opposite-pair normal
parameter. The two free pair normals in (2) are independent.

The only unit at this junction having two physical singleton contacts
there is D: the C--H contact is physically shared. The boundary/clear
labels in this statement also fix which of C,H is which. Hence the rule
below makes at most one request at a given physical junction.

Write the unchanged circle origin in this chart as O=(xi,zeta). Impose
the following additional, purely physical predicate on the prelisted
junction:

    D avoids closed D_epsilon, or |xi|>epsilon.          (3)

Here D_epsilon is centered at the original O, not at the translated P.
The predicate says that, if D is near O, its West axis at P does not
have small absolute original support height. It involves no force,
unknown mean, eventual load or positive graph.

## 2. One simultaneous compatible selection

Prelist all physical junctions satisfying Section 1 and (3), before the
multiplier theorem. If u<pi/4, restrict just the D-to-H interval to

    u<phi_H<pi/4.

If u>pi/4, restrict just the D-to-C interval to

    pi/4<phi_C<u.

If u=pi/4, impose no new restriction. Each imposed interval is nonempty
and open, and lies in the actual strict physical interval (2). After the
restriction, whenever u!=pi/4, both original selected D normals lie on
one and the same strict side of D's southwest diagonal.

This open restriction need not be dense. Its compatibility is as follows.

First, the previously imposed nongeneric C7 radial, pinned and mirror
restrictions concern pairs of two physical boundary units. So does the
near-bisector restriction on two physical radial-S units. Neither pair
in (2) is such a pair, since D is physically clear. There is no four-unit
matching at P to couple these new parameters to any boundary pair.

Second, retain the entire earlier S-root boundary-free side-bias rule.
It inspects every physical free near-unit/boundary pair, independent of
the eventual root or positive component. It can affect DC only when D
meets closed D_epsilon. At P its two outward side axes are West and
South. For n(phi), their positive component magnitudes are cos phi and
sin phi respectively. By (3), West cannot be its designated small
absolute-support axis. A South-small request, if present and nonempty,
therefore restricts precisely to phi>pi/4.

If u<pi/4, the physical DC interval (0,u) contains no such direction,
so the earlier rule leaves it unchanged; our new restriction is on DH.
If u>pi/4, the earlier South-small restriction is exactly (pi/4,u),
the same interval we use. If there is no small-axis request, or D is
not near, the earlier rule imposes nothing on DC. The DH pair has two
physically clear endpoints, so it receives no near/boundary request.
This checks every prior side-bias alternative, including equality in
the small-support test. In particular no two competing nondense open
requirements are silently intersected.

Third, different new junctions use different point-only pairs. A pair
with singleton physical intersection cannot recur at another point.
The uniqueness in Section 1 excludes opposite requests at the same
junction. All new intervals are independent of matched four-unit
parameters and of the unchanged earlier boundary-pair restrictions.

The remaining finite strict nonradial, diagonal-avoidance and nontrivial
analytic determinant exclusions are open dense on their original allowed
parameter domains. They remain available inside the nonempty open product
just constructed. Make these choices together before applying the
physical feasible-branch and multiplier theorem.

The usual exact planar uncrossing changes only matched opposite pairs
at four-unit junctions and adds actual shared-side forces. It does not
change either surviving singleton normal at the present three-unit
junction. Conic thinning only deletes atoms, and shared aggregation
does not change these physical singleton points. Therefore the final
common selected certificate retains the new property. No normal of an
already extracted equilibrium is reselected.

## 3. The full unloaded-three-force consequence

Suppose an eventual D in the prelist is unloaded of true positive degree
three, with exactly the positive neighbors C,H,E. Its two original C,H
applications are P. All degrees, loads and forces at those other units
remain arbitrary.

Because both original D-to-C and D-to-H vectors have strictly negative
components, full force balance makes the original D-to-E normal strictly
northeast. Its actual D application is consequently the opposite vertex

    Q=(1,1).

Full torque about P, which is valid because the full D force sum is zero,
then gives

    det(Q,n_DE)=0,
    n_DE=(1,1)/sqrt(2).                                 (4)

The original positive C,H vectors must therefore have positive sum in
the southwest diagonal direction. If u<pi/4, both selected phi values
are strictly below pi/4, so the sum of the absolute horizontal components
strictly exceeds the sum of the absolute vertical components. If u>pi/4,
the reverse strict inequality holds. Neither can give the diagonal (4).

Thus the complete original D3 equations force

    u=pi/4.                                             (5)

This is a necessary selected-certificate conclusion, not an assertion
about arbitrary differently selected equilibria. No C2 or H3 equation
has been assigned to a higher-degree unit, and the actual shared HC
mean has not entered or been replaced in the D equation.

## 4. A force-free diagonal bridge obstruction

Let e,f be orthonormal and keep actual units

    D=conv{0,(e-f)/sqrt(2),sqrt(2)e,(e+f)/sqrt(2)},
    H=[-1,0]e+[-1,0]f.

Let an actual unit E lie wholly in e.z>=sqrt(2). No actual unit A with
open interior disjoint from D can physically touch both H and E.

Indeed choose actual S in A intersection H and T in A intersection E.
Then

    sqrt(2) >= |T-S| >= (T-S).e >= sqrt(2).

All inequalities are equality. Thus S.e=0, T.e=sqrt(2), T.f=S.f=y,
with -1<=y<=0. The two points have distance sqrt(2) in A, so they are
opposite A vertices. Opposite vertices determine a unit square uniquely;
hence A is exactly D translated by y f.

In the original own axes (e-f)/sqrt(2),(e+f)/sqrt(2) of D, that translation
has components -y/sqrt(2), y/sqrt(2). Their absolute values are at most
1/sqrt(2)<1. Both pairs of open unit coordinate intervals therefore
overlap, so int(A) intersects int(D), a contradiction. This includes
y=-1 and y=0 and uses no assumption on an E application or side owner.

The lemma covers all actual A,H,E contact points. It does not select an
original force mean, use a circle equation, or change a physical unit.

## 5. The literal complete shared-HC coincident pentagon interface

Retain the original H4_D0 graph and all nine actual units:

    HA, HB, HC, HD, AB, BC, CD, DE, EA.

H is unloaded of true degree four, D unloaded of true degree three, and
C,E retain their full loaded degrees three and two. Assume A,B,C,E are
physically boundary. This covers original H4_D0.L0124 and the entire
physical-boundary-A mask of H4_D0.L124, preserving A's zero total circle
coefficient in the latter. The actual H is the original interior vertex
of the occupied outer rim. It is physically clear. D is also physically
clear, because otherwise the entire physical outer rim would be a
forbidden boundary C5.

Suppose HD and CD are physical singleton contacts at their same D vertex
P, HD is free, and HC is a positive-length physical shared side containing
P. This is the entire shared-HC portion of the remaining coincident
free-HD interface after the previously separate shared-CD/DE exits.

The point P is a vertex of C as well as H,D. If P were side-interior on
C, the C tangent half-plane and the two H,D quadrant sectors would fill
the plane exactly. H and D would then be the adjacent aligned quadrants
in the remaining half-plane and would share a positive-length side,
contrary to HD being a singleton. Thus all three are vertices. The
strict point-only convention makes CD free too, and Section 1 gives the
complete chart (1), with 0<u<pi/2. All HC means on the full shared side
remain, including both endpoints.

Full D3 alone gives (4), before any new selection. Hence the whole actual
E lies beyond the diagonal support at Q=(1,1). We must still prove the
physical predicate (3) before invoking Section 3.

### 5.1. Actual occupied order and the original E2 moment

At P the D, C and H tangent sectors occur in that cyclic order. More
explicitly, their center rays from P have angles pi/4, 3*pi/4+u and
5*pi/4+u. The actual H sector is on the left of the D-to-C rim strand.
For the incoming D-center-to-P segment this also follows from

    det((-1/2,-1/2),c_H-P)=sin(u)/2>0.

For the outgoing P-to-C-center segment, c_C-P and c_H-P are perpendicular
with positive determinant. The compatible three-sector routing retains
these incidences even though the DC and DH applications coincide.

The actual occupied-rim contract therefore gives the positive orientation

    D -> C -> B -> A -> E -> D.

The simultaneous actual circle accesses of C,B,A,E transfer it to their
circle order. The physical boundary angular-neighbor theorem and the
full boundary-contact moment theorem then give the original strict sign

    det(P_EA-O,n_EA)<0.                                 (6)

This concerns the unchanged EA normal and actual application or shared
mean. A positive total circle load at A is not required. All other actual
circle masks and the three arbitrary completion units remain.

In E's complete original two-pair-force torque equation, every individual
circle atom has zero moment about O. The E-to-D direction is -e, where
e=(1,1)/sqrt(2), with application Q. With original positive magnitudes
mu_DE,mu_EA this gives

    -mu_DE*det(Q-O,e)+mu_EA*det(P_EA-O,n_EA)=0.

Using (6),

    det(Q-O,e)=(zeta-xi)/sqrt(2)<0,
    zeta<xi.                                            (7)

This uses the full genuine E2 star; no force at C or H has been removed.

### 5.2. The earlier side-bias rule cannot make a conflicting request

If D avoids closed D_epsilon, (3) already holds. Otherwise its actual
near point implies xi>=-epsilon and zeta>=-epsilon in the D chart.
If also |xi|<=epsilon, (7) would give

    -epsilon<=zeta<xi<=epsilon,
    |P-O|<=sqrt(2)*epsilon<1/40.

But the actual physical boundary C contains P. Any actual circle point
Z_C of C has |Z_C-P|<=sqrt(2), so

    |P-O|>=R-sqrt(2)>11/20,

a contradiction. Therefore |xi|>epsilon whenever D is near. This proves
exactly the physical predicate used in the prelist. It does not infer it
from a normal chosen after extraction.

### 5.3. The selected diagonal equality is physically impossible

Sections 2--3 now apply literally and force u=pi/4. Put

    e=(1,1)/sqrt(2), f=(-1,1)/sqrt(2).

The unchanged actual units in (1) are

    C=[-1,0]e+[0,1]f,
    H=[-1,0]e+[-1,0]f.

D is exactly the diagonal unit in Section 4. Its original DE direction
is e and its original Q is sqrt(2)e, so the whole actual E satisfies
e.z>=sqrt(2). The original graph has both HA and EA, hence the actual A
touches H and E. The force-free bridge lemma contradicts interior
disjointness of A and D.

This excludes the whole shared-HC coincident free-HD interface for the
four-physical-boundary domain. It includes every HC mean, all original
E frames and means, and both physical circle masks at every boundary
unit. The strict-singleton HC residue is separate. The physically
clear-A part of L124 also remains separate. No complete original gate
receives closure credit from this source alone.

## 6. Exact direct inputs and proof boundary

| Source | SHA256 | Exact use |
| --- | --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Original strict singleton branch before multipliers and unchanged full force/torque equations |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | Complete tangent-sector/matched-normal domain, preservation of singleton normals and compatible physical circle accesses |
| S_ROOT_BOUNDARY_FREE_NORMAL_SIDE_BIAS_SELECTION.md | 48bc30d65e1581f4dc84ac0143b76482738dd46901e9f5384b66f94b34de8343 | Its full nondense near/boundary request, tested explicitly in Section 2; no dense replacement is asserted |
| C7_TWO_CIRCLE_CORNER_BLOCKS.md | 6ed5bdde4487a45935c85ecb9ee4556555491047d4739e529bd024f234affddc | Earlier open radial-run restrictions are on two-boundary pairs |
| C7_RADIAL_VERTEX_EDGE_EXCLUSION.md | e850a10e2d03217d7f4a37870dc309f101ddde7fe41b52adb82d7b6c5e7865d2 | Scope of the earlier radial-pair open choice in its Section 4 |
| C7_MIRROR_VERTEX_EDGE_EXCLUSION.md | 16e73078680111b4479c680f70ceb33d2c3c08801a0055328262bc31e4b27c89 | Scope of the earlier mirror boundary-pair choice |
| C7_PINNED_VERTEX_CONTACT_TYPES.md | 545e2e30193787a2a374adaf6063053024a717dc6f1bde1084b6c2c20590a51e | Scope of the earlier pinned boundary-pair choice in Sections 5--6 |
| ADJACENT_TWO_S_LEAF_C4_BOTH_TWO_CORNER_MASK_EXCLUSION.md | e55398acb2f544139113cfa30f93f8dd9dd68656c40d9ba0cfc4c20aeb7f870f | Its Section 1 near-bisector choice is on two physical boundary units |
| SIX_BODY_INNER_PENTAGON_LOAD_COVER.md | cfe85a201b09182200d5270f0dcdc0e590bf99eded19aaf6d56f86830e959c0a | Actual original H4_D0 graph, loads, full true degrees and physically clear interior H |
| INNER_PENTAGON_OCCUPIED_HUB_AND_EXTERIOR_POCKET_LOCALIZATION.md | 37fad266560ea5e2bca29723f4db00617c35a67be2e82b70fbf743b75006a502 | Sections 1--4 occupied-rim and simultaneous actual circle-order construction, valid for the retained H4 as well |
| CIRCLE_CONTACT_ANGULAR_ORDER.md | e54df61d3134c5709bee5ac1a250fdd51084828da114d896f14c7e6337c4e8c5 | Physical boundary C5 exclusion and angular-neighbor order |
| BOUNDARY_CONTACT_ORIGIN_MOMENT_ORIENTATION.md | 851417d7fcd12ccb93a6f7f09ba7d7b2bf9bccc61c82fee3457b5ee4cee47e9a | Full original moment sign on the physical boundary EA contact |

The selection, complete diagonal bridge proof, all full D3/E2 algebra and
the necessary physical compatibility predicate are proved above. This
source uses no sampled pose, angle grid, numerical exclusion certificate,
post-extraction normal change, chosen side mean, shortened positive star,
Lean compilation, CI, workflow, metadata edit or publication.
