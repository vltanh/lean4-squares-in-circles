# A same-face shared triangle return leaves at most one unit in its closing boundary-path pocket

Date: October 28, 2026 UTC. Author: cycles continuation.

**Status: complete proposed hand implication, awaiting full root and
separate independent review.** The geometric pocket theorem is uniform
over an arbitrary boundary path with the stated true degrees. Its
literal six-body caller excludes one complete physical feature of
M6.B6.HEXAGON.D02.L01345. It does not close that original row, because
singleton contacts and contacts on different hub faces remain.

Put Q=1105/256. Every square, containing-circle origin, original pair
normal, positive magnitude, contact application or shared-side mean,
physical circle mask and individual zero corner weight is unchanged.

## 1. Exact uniform physical statement

Work in 2<R<=sqrt(Q). Suppose a complete positive component consists
of one unloaded square U and k loaded boundary squares, 3<=k<=6,
with precisely the boundary path

    V, W, B_3, ..., B_(k-1), T

and the three hub spokes UV, UW, UT. There are no other positive
edges of this component. For k=3 the path is V,W,T.

Thus U has its true positive degree three; V and T have their true
positive degree two; W has degree three; and every other path body
has degree two. The actual outer-face order is U,V,W,...,T,U.
All other physical packing units and all zero-weight contacts remain.

Assume the actual physical intersections U intersect V and U intersect W
both have positive length and lie on the **same actual side of U**.
Their physical frames are consequently parallel to U's frame. This
same-face assumption is an explicit premise, not a consequence of
the phrase "both shared."

**Pocket theorem.** The actual closing exterior pocket through U,
between V and T, contains at most one whole additional unit square.

The statement retains every original mean on either positive-length
shared contact, including endpoint-valued means. T may have one or
two physical circle corners; its actual contact with U may be a
singleton or a shared segment, and its full circle force is retained.

The body U is physically circle-clear: if it touched the circle, the
physical triangle U,V,W would contradict the circle-boundary contact
graph theorem. In particular the quoted single-hub pocket theorem
applies at its actual physical scope.

## 2. The actual parallel frame and its unique circle corners

Rotate and, if necessary, reflect all data about the unchanged origin.
Write the common U side as x=a and arrange V above W. Both V and W
have x interval [a,a+1]. Their physical contact and disjoint open
interiors make their vertical intervals adjacent. Write them first as

    V=[a,a+1] times [s,s+1],
    W=[a,a+1] times [s-1,s].

Both squares touch the same circle. Their common maximum squared
x coordinate is the same, so equality of their farthest-corner
radii gives

    max(s^2,(s+1)^2)=max((s-1)^2,s^2).

This forces s=0. The positive lengths of the two U contacts then give

    U=[a-1,a] times [b,b+1],       -1<b<0,
    V=[a,a+1] times [0,1],
    W=[a,a+1] times [-1,0].                              (1)

Also max(a^2,(a+1)^2)=R^2-1. The negative branch
a=-sqrt(R^2-1) is impossible: the left edge of U would have
absolute x coordinate sqrt(R^2-1)+1>R. Therefore

    a=sqrt(R^2-1)-1,
    73/100<a<5/6.                                      (2)

For the lower comparison use R>2 and
3-(173/100)^2=71/10000>0. For the upper comparison use

    (11/6)^2-(Q-1)=103/2304>0.

In particular a>0. The physical circle masks of V and W are each
unique, with actual circle corners

    Z_V=(a+1,1),       Z_W=(a+1,-1).                    (3)

This uniqueness has been proved from their actual geometry; no
physical mask or zero corner weight was discarded.

## 3. The original full equations and the strict upper hub port

Let the original UV mean be P_V=(a,t), 0<=t<=b+1, and let the
original VW mean be (x,0), a<=x<=a+1. Write the actual circle
force at V as lambda Z_V, lambda>0, absorbing only the common
normalization into lambda.

The two original outward pair normals from V are West and South.
Its complete force equation makes their magnitudes lambda(a+1)
and lambda. Its complete origin torque therefore is

    lambda(a+1)t-lambda x=0,
    t=x/(a+1)>=a/(a+1)>0.                               (4)

In particular b+1>=t>0. No shared-side mean was set to a midpoint
or replaced by a geometric contact endpoint.

Write the original UW mean as P_W=(a,s), b<=s<=0, and its
positive magnitude as mu_W. Put mu_V=lambda(a+1). The complete
unloaded force equation at U gives

    n_UT=West,       mu_T=mu_V+mu_W>0.                  (5)

Its original UT mean is therefore

    P_T=(a-1,h),       b<=h<=b+1,

and its full original torque remains

    mu_T h=mu_V t+mu_W s.                               (6)

The crucial strict sign h>0 uses the actual far endpoint T,
not an inference from (6) alone.

The boundary path V,W,...,T follows clockwise circle order. Indeed
V to W is clockwise by (1), and every boundary-pair contact joins
consecutive actual circle-center directions on its minor arc.
A simple path of such consecutive edges cannot reverse that
orientation. The degree-free boundary-pair moment lemma gives
a strictly negative original directed moment on every clockwise
edge of this path.

At the true degree-two endpoint T, the normal to U is East and its
moment is -mu_T h. Its other original pair force, directed from T
to its predecessor on the boundary path, has strictly positive
moment because this direction is counterclockwise. Circle forces
have zero origin moment. The complete T torque equation gives

    h>0.                                                (7)

This is also exactly the endpoint sign (3)--(4) of
GENERAL_SINGLE_HUB_BOUNDARY_PATH_POCKET.md, with clockwise order.

The proper-concurrence theorem at this actual loaded degree-two
endpoint, whose predecessor is a physical boundary neighbor, gives

    q_T=P_T+ell(-1,0)=tau F_T,
    ell>=0, tau>0,                                     (8)

where F_T is its full original circle resultant. Thus

    (F_T)_y>0.                                          (9)

The possible two-circle outside concurrence is not placed inside T.

## 4. The two endpoint center directions are less than 120 degrees apart

Let c_T be T's actual center. Because UT has normal West, the
maximum x support of T is a-1. Write its actual horizontal
halfwidth as w_T. Every orientation has

    1/2<=w_T<=1/sqrt(2),
    (c_T)_x=a-1-w_T<0.                                 (10)

From (2) and 1/sqrt(2)<17/24,

    |(c_T)_x|=1-a+w_T<587/600.                           (11)

As a physical boundary square T has

    |c_T|>=R-1/sqrt(2)>31/24.                            (12)

The exact difference

    (31/24)^2-(587/600)^2-1/2=3169/15000>0

shows |(c_T)_y|>1/sqrt(2). Every point of T differs in y
coordinate from its center by at most 1/sqrt(2). Consequently
the entire closed T has y of one strict sign. Formula (9),
a positive weighted sum of its physical circle corners, makes
that sign positive. Hence c_T is in the strict second quadrant.

Let theta_T=arg(c_T) in that quadrant. Equations (11)--(12) give

    cos(pi-theta_T)=|(c_T)_x|/|c_T|
         <587/775<19/25<cos(2pi/9).                     (13)

The rational middle reserve is 2/775. For the last comparison,
4z^3-3z is increasing for z>1/2 and

    -1/2-(4(19/25)^3-3(19/25))=753/31250>0,

whereas 4cos(2pi/9)^3-3cos(2pi/9)=-1/2. Thus

    pi/2<theta_T<7pi/9.                                 (14)

The actual V center is c_V=(a+1/2,1/2), so

    tan(theta_V)=1/(2a+1)>3/8>tan(pi/9),
    pi/9<theta_V<pi/2.                                 (15)

For the last comparison one may use the exact inequalities
sin(pi/9)<77/225 and cos(pi/9)>15/16 proved in the centered-arc
source, together with

    3/8-(77/225)/(15/16)=269/27000>0.

Combining (14)--(15),

    0<theta_T-theta_V<2pi/3.                             (16)

This is a statement about the two unchanged physical centers.

## 5. The actual occupied crosscut routes every exterior extra

An angular estimate for the center endpoints by itself would not
locate a unit in the actual pocket. We now prove that location
using an occupied physical crosscut.

Replace the UV and UT applications **only in the crosscut
construction** by the gap-facing extremes of their actual contact
sets. In the chart (1) the UV extreme is

    A_V=(a,b+1).

The UT contact set lies on x=a-1. Its upper extreme is

    A_T=(a-1,h_ext),       h_ext>=h>0.                   (17)

The original t,h in every force and torque equation remain unchanged.
The outer U arc goes from A_V along its top edge, then down its
left edge to A_T. Its points all have positive y.

The argument of every point on that outer U arc is at least
arg(A_V). Indeed the argument increases along the top edge
traversed leftwards and along the negative-x left edge traversed
downwards. From (4),

    arg(A_V)>=arg(Z_V)>theta_V.                         (18)

For its upper angular bound, the left-side extreme gives

    arg(A_T)<=arg(P_T)<=arg(q_T)=arg(F_T).               (19)

The first inequality uses h_ext>=h>0 at the same negative x;
the second uses (8), which moves left at the same positive y.
Every point of the outer U arc has argument at most arg(A_T).

The actual boundary-corner cone theorem puts every circle corner
of T and its full positive resultant strictly within pi/12 of
theta_T. This is the geometric calculation in Section 2 of
GENERAL_BALANCED_THREE_BOUNDARY_FULL_WINDOW_METRIC_EXCLUSION.md;
its three-body balance theorem is not being invoked. Thus (19)
bounds the entire outer U arc above by theta_T+pi/12.

Join A_V to Z_V through the actual interior of V, with endpoints
retained. The straight segment already has its open part in int V:
A_V is in the relative interior of its left side, since
0<b+1<1. Its arguments lie between those of its two endpoints.
Both are strictly above theta_V, and both are below pi/2<theta_T.

Choose the gap-facing actual circle corner Z_T of T. By (17)
and the strict positivity of y on all of T, A_T and Z_T are in
the second quadrant. Both have argument strictly below
theta_T+pi/12; both are above pi/2>theta_V. Join them through
int T. If their straight segment lies on a side, perturb it
slightly into int T, preserving these strict angular inequalities.
The path meets U only at A_T and the containing circle only at Z_T.

These endpoint paths are disjoint, because V and T are
closed-disjoint by the boundary-path contact graph theorem.
Together with the outer U arc they form an actual occupied
crosscut from Z_V to Z_T. Choose the closing circle arc on
the exterior side of the actual outer-face order.

This is the upper minor circle arc. To verify the choice, the
physical boundary path V,W,...,T runs clockwise, as proved in
Section 3; the actual circle-corner order agrees with the center
order. Therefore its complementary core gap from V to T is
counterclockwise. Both selected corners are in the upper half-plane,
with Z_V in the first quadrant and Z_T in the second, so this
complementary gap is precisely their upper minor arc. All remaining
core circle-corner intervals lie on the path's clockwise side.
Additional completion corners may lie on the closing arc and are
not removed or assumed absent.

The entire actual Jordan boundary, including this circle arc,
therefore lies in the closed pointed convex cone

    C={r(cos theta,sin theta):
          r>=0, theta_V<=theta<=theta_T+pi/12}.          (20)

Its aperture is strictly below 3pi/4 by (16). The bounded Jordan
region also lies in C: each defining closed half-plane of C
contains the whole Jordan boundary, so the opposite open
half-plane, connected to infinity without meeting that boundary,
contains no point of the bounded component.

The paths may enclose portions of the endpoint squares themselves;
this causes no problem. Every extra's open interior avoids the
closed core squares and hence avoids the occupied crosscut.
A whole extra in the closing pocket is confined to its bounded
side, and its center, being an interior point, lies in (20).
Additional zero-weight contacts can subdivide this region but
cannot open a passage through its occupied boundary. At a weak
physical junction, the standard compact-inner-subset routing gives
the same bounded-side assignment; taking closures retains the
whole square. No open extra interior is crossed by a perturbation.

The whole single-hub boundary-path pocket theorem applies to the
same component, with all three U spokes and every actual degree
retained. It gives

    dist(O,E)>1/4

for each whole extra E in this closing pocket. Since E contains
its open radius-1/2 incircle, its actual center satisfies

    |c_E|>3/4.                                          (21)

Indeed if |c_E|<1/2, the origin belongs to that incircle; if
1/2<=|c_E|<=3/4, points of that incircle toward the origin have
distance with infimum at most 1/4. Either contradicts the strict
distance bound.

The centered forty-degree arc theorem now applies to every such
E and to the boundary squares V,T. Their pairwise minor center
separations are strictly greater than 2pi/9. By (20), an extra
center's angle is at most theta_T+pi/12. It cannot be at or above
theta_T, because then its separation from T would be at most
pi/12<2pi/9. It also cannot equal theta_V. Therefore each extra
center actually lies in the open interval

    theta_V<arg(c_E)<theta_T.                            (22)

If two distinct extras E_1,E_2 lie in the pocket, order their
center arguments in (22). Each of the three successive gaps

    V to E_1,       E_1 to E_2,       E_2 to T

is its minor gap, since the entire interval has length below
2pi/3<pi. Each gap is strictly greater than 2pi/9. Their sum
is strictly greater than 2pi/3, contradicting (16). This proves
the whole pocket capacity at most one.

## 6. Literal D02.L01345 feature exclusion, with all three extras

For the original rim 0,1,2,3,4,5 and its positive chord 02,
with load mask 01345, set

    U=2, V=1, W=0, B_3=5, B_4=4, T=3.

The complete boundary path is 1,0,5,4,3. The only unloaded
body is U, its true neighborhood is exactly V,W,T, and all
other degrees match Section 1. The original six-body component
retains three arbitrary additional unit squares.

The same-nine analytic radius theorem supplies R>2, using the
same nine physical squares before any component geometry is
applied. Hence all original R<=2 are already excluded, without
an assumption that a six-square core itself forces that bound.

Assume the actual contacts 2 intersect 1 and 2 intersect 0
both have positive length on the same side of square 2.
The pocket theorem then gives capacity at most one in the
actual closing exterior pocket through 2 between 1 and 3.

The exact central faces are the triangle 0,1,2 and the pentagon
0,2,3,4,5. The complete positive-chord central-capacity theorem
gives combined central capacity at most one. Every other exterior
pocket is a direct touching-boundary-pair pocket along the actual
path 1,0,5,4,3, and is empty by
CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md, Theorem 4.1.

For completeness, this is an allocation of all actual extras.
Occupied center/contact paths of the full six-body graph separate
the central face sides from the exterior. Actual paths through the
five boundary bodies to their physical circle corners split the
exterior into the four direct-pair pockets and the one closing
pocket through U. Every extra's connected open interior avoids
all these occupied paths, so it lies on one listed face or pocket
side. The compact-interior convention at weak junctions, followed
by closure, places its whole unit area there. Extra physical
zero-weight edges only refine this partition.

Thus at most one extra is central and at most one is exterior.
The three unchanged completion units cannot all be allocated.
This excludes the entire stated same-face positive-length
shared-contact feature of the original D02.L01345 row.

It does not exclude positive-length contacts on adjacent U
faces, nor either singleton-contact alternative, merely from
their normals being parallel. Those are separate original
physical domains. No original fine or coarse checkbox is
changed by this source.

## 7. Frozen operative sources and audit boundary

| Source | SHA-256 | Operative input |
| --- | --- | --- |
| GENERAL_SINGLE_HUB_BOUNDARY_PATH_POCKET.md | 958bb122342783a824d023c221ccc2c93a68300b00b0ffc3496c25ad394aec84 | Complete actual closing pocket lies beyond the quarter disk; exact endpoint degree and moment scope |
| FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md | aef2fc2adfda6168d7e2c2f824b373d6beafb12c8937e0f6bc93f7f36b464a67 | Degree-free Lemma 1.1 on the sign of a boundary-edge moment |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 | Local Lemma 2.1, true loaded-two-force proper concurrence with one boundary neighbor |
| GENERAL_BALANCED_THREE_BOUNDARY_FULL_WINDOW_METRIC_EXCLUSION.md | 5da69931a63ac7cbf93ec3ff494489dc05d2245017da1c4dcddf1b4a8a6c956e | Section 2 only: each actual circle corner and positive resultant differs from the actual center direction by less than pi/12 |
| ALL_UNITS_CENTER_RADIUS_THREE_QUARTERS_CENTERED_FORTY_DEGREE_ARC.md | d575e6632c7181fc8803e7c9dc73b222cdce055eca1c636b3f15eb9d5f2279b9 | Whole force-free centered arc theorem and exact twenty-degree comparisons |
| CIRCLE_CONTACT_ANGULAR_ORDER.md | e54df61d3134c5709bee5ac1a250fdd51084828da114d896f14c7e6337c4e8c5 | Complete boundary contact graph and physical minor contact order |
| CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md | b61b0dec7ded00984c687e353fd3f3bfb5a5a7ade45d87d69aaeade09f23d80b | Actual circle-corner order and whole direct-pair exterior-pocket emptiness |
| CHORDED_HEXAGON_CENTRAL_CAPACITY_ONE.md | 0b787eae6efe36d2ca6c40dbb079d3262192125fffe58026bacbfd657d1a9a34 | Full central free-union capacity at most one, retaining weak junctions |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Exact original graph, load mask and degrees |
| LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md | 3b3f40af8f62beee8a55b8d4c8d26398097362d88e91d32116885b4ceea96e90 | Same-nine analytic R>2 entry, retaining its full printed analytic dependency chain |

The displayed rational reserves were checked exactly as scalar
algebra; they are already printed in the proof. No pose enumeration,
normal adjustment, computational exclusion certificate, Lean
compilation, CI, workflow, ledger edit, commit or remote action is
part of this manuscript.

