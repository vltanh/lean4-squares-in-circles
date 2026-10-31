# The full five-spoke fan is excluded when both endpoint normals are hub-owned

Date: October 26, 2026.

**Status: accepted complete whole owner-family theorem after the full
reviews REVIEW_FAN_HUB_OWNED_ENDPOINTS_ROOT_2026_10_26.md and
REVIEW_FAN_HUB_OWNED_ENDPOINTS_GLOBAL_2026_10_26.md.**
This does not close the entire fan graph: an original oblique hub normal
at either endpoint remains outside its hypotheses. The three internal
hub normals are unrestricted. No original label is changed.

Keep the original selected positive fan

    H B_i (1<=i<=5),
    B_1 B_2, B_2 B_3, B_3 B_4, B_4 B_5.

The complete graph/load cover makes every B_i positively circle-loaded
and H physically clear. H has true degree five; B_1,B_5 have true degree
two; B_2,B_3,B_4 keep true degree three. All three other physical units,
circle masks, individual zero corner weights, actual common means and
all original positive forces remain. Work in

    2<=R<=sqrt(1105)/16.

The existing nine-square radius-two exclusion handles the lower portion
of the original radius window. Assume only that the two actual normals
n_1,n_5 from H to the endpoint bodies are H side axes. No normal is
reselected. In particular n_2,n_3,n_4 retain all their original side-owned
or oblique possibilities and all their positive magnitudes.

**Theorem.** This complete owner family has no nine-square completion.

## 1. The full five-force equation and actual normal order

Write mu_i>0 for the original hub-edge magnitudes. H's complete force
equation is

    sum_(i=1)^5 mu_i n_i=0.                              (1)

The actual cyclic spoke order at H is B_1,...,B_5. This is the physical
port-order argument used in `FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md`,
Section 2, now applied to the actual outer face H,B_1,...,B_5,H.
All five boundary bodies lie on that face, and the small physical
center/contact embedding preserves their cyclic order.

The actual outward normals have the same weak circular order. At
distinct contact points this is the monotone support-normal order on
the boundary of a convex square. On a side the normal is its side axis;
at a vertex it lies in the closed normal quadrant between the adjacent
axes. For coincident applications, each actual outward H normal points
along a sufficiently short inward segment of its neighboring square.
Those neighbor tangent sectors have disjoint interiors and the same
physical order as the contact spokes. Their normal directions therefore
keep that order inside H's one vertex normal quadrant. The selected
strict point-normal convention gives the strict version for free
vertex contacts; shared-side endpoint directions give its weak limits.
Three distinct boundary neighbors cannot coincide at an H vertex,
since they would form a forbidden physical boundary triangle. Thus
these are all coincident-contact cases. No normal is changed in this
argument.

After reflecting orientation, read this order clockwise. A repeated
endpoint axis either bounds an order of zero total turn (all normals
that same axis), or an order of one full turn. The first cannot satisfy
(1). Opposite endpoint axes bound a half-turn. Adjacent endpoint axes
bound either a quarter-turn or a three-quarter-turn. A quarter-turn
would put all five normals in one closed quadrant, impossible in (1).
These observations include zero angular steps and endpoint-valued means.

Write N=e_y, E=e_x, S=-e_y and W=-e_x in H's actual axes. The three
remaining endpoint possibilities are treated below with all internal
normals still present.

### 1.1. Opposite endpoint axes are impossible

If the endpoint axes are N,S, choose the clockwise half-turn through E;
reflection handles the one through W. All internal normals then have
nonnegative x-component, and both endpoint x-components vanish.
Equation (1) forces every internal x-component to vanish. Thus all five
normals are N or S. Since both signs occur along the connected path,
some consecutive pair is opposite. This violates the geometric
`UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md` at that actual contact
triangle. No opposite-axis case remains.

### 1.2. The first and last neighboring normals in the remaining cases

For equal endpoint axes N,N, the normal order makes one full clockwise
turn. The contact triangle at B_1 and the owned N normal give
(n_2)_y>=0. If n_2 occurred on the final W-to-N quarter-turn, all
subsequent normals would also have nonnegative y-component, while the
two N endpoints contribute strictly positively; (1) would fail. Thus
n_2 is N, a strict northeast normal, or E. Reflection of the terminal
argument makes n_4 equal to W, a strict northwest normal, or N.

For adjacent endpoints, name them N,W along the surviving clockwise
three-quarter-turn through E,S. The same endpoint triangle gives
(n_2)_y>=0. The only possibilities along that order are N, a strict
northeast normal, E, or W. The last would leave all later normals equal
to W and again make (1) impossible. Thus n_2 is N, northeast, or E.
At the other end the owned W normal gives (n_4)_x<=0; the corresponding
order and (1) leave only S, a strict southwest normal, or W.

These are conclusions from the full five-force equation, actual order,
and the two endpoint contact triangles. No equation at an internal
body has been truncated.

## 2. Exact endpoint signs, including a repeated neighboring axis

Let g_i be the original normal from B_i to B_(i+1), with magnitude
gamma_i>0, and let F_i be the complete actual circle resultant on B_i.
The two genuine endpoint equations are

    F_1=mu_1 n_1-gamma_1 g_1,
    F_5=mu_5 n_5+gamma_4 g_4.                            (2)

No such degree-two equation is assigned to an internal B_i.

For consecutive perpendicular owned hub sides, the complete geometric
normal-cone lemma in Section 2 of
`BOWTIE_PERPENDICULAR_CONTACT_EXCLUSION.md` gives:

    N to E: (g_1)_x>=0, (g_1)_y<=0;
    S to W: (g_4)_x<=0, (g_4)_y>=0;
    W to N: (g_4)_x>=0, (g_4)_y>=0.                    (3)

The transverse component needed in an endpoint equation is strict.
For example (g_1)_x=0 in the N-to-E case would make both original
endpoint force lines parallel. A true loaded degree-two body with a
physical boundary neighbor has nonparallel lines, by the complete
proper-concurrence lemma in
`TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md`, Lemma 2.1. Equivalently its
single boundary-neighbor contact would become radial, forbidden for
two physical boundary units. The reflected endpoint cases are identical.

If n_2 is strict northeast, its H application is H's northeast vertex,
on the same top side as p_1. The separating inequality at the two
actual H applications gives (g_1)_x>=0 when they are distinct. If
they coincide, p_1 is simultaneously a minimum-N point of B_1 and
a maximum-g_1 point of B_1, so its short inward N segment gives
(g_1)_y<=0. At B_2 the same point is a minimum-n_2 and minimum-g_1
support point, so its short inward n_2 segment gives g_1.n_2>=0.
Since both components of n_2 are positive, these two inequalities
exclude (g_1)_x<0. The zero x-component is excluded by the same
nonparallel endpoint lemma used above. Thus (g_1)_x>0 in the entire
northeast case as well. Rotating or reflecting this argument handles
the terminal strict northwest or southwest cases.

For two consecutive N contacts, actual clockwise port order is from
left to right. Their mutual normal therefore has strictly positive
x-component. To check the weak endpoints: if the two actual application
x-coordinates differ, the supporting inequalities give the weak sign;
a vertical separating normal is impossible since both units have the
same minimum y-coordinate and positive vertical width. If the two
applications coincide, their two tangent sectors, both above the same
line, must fill the two upper right-angle sectors. Both units are then
axis-aligned locally, one to the left and one to the right, and the
mutual normal has the same strict sign. An application in a side
interior would leave no room for the other tangent sector. This includes
all original shared means.

Likewise, two consecutive W contacts run from bottom to top and their
mutual normal has strictly positive y-component.

The loaded-tip proper concurrences also give, for each endpoint,

    q_i=tau_i F_i=p_i+ell_i n_i,
    tau_i>0, ell_i>=0.                                  (4)

The physical two-corner masks and unequal or zero individual corner
weights remain included. In particular (4) is not asserted to lie
inside a physical radial tip.

## 3. Equal endpoint axes are impossible

For endpoints N,N, the complete neighboring-normal cover of Section 1.2
and the endpoint sign arguments of Section 2 give

    (F_1)_x<0<(F_5)_x.

Because n_1=n_5=N, (4) gives

    (p_1)_x<0<(p_5)_x.                                 (5)

But the actual clockwise hub-side order is the opposite: the path
starts on the N side, goes around E,S,W, and returns to the N side.
Its final N contact lies to the left of its initial N contact, so

    (p_5)_x <= (p_1)_x.

This contradicts (5). Coincident means do not remove the contradiction.
Thus the entire equal-axis case is excluded before any completion
estimate.

## 4. Adjacent endpoint axes give an actual northwest cap

The endpoint axes are N and W. The complete first-neighbor cover is
N, northeast, or E; the last-neighbor cover is S, southwest, or W.
Section 2 and the
actual endpoint equations therefore give

    (F_1)_x<0,       (F_5)_y>0.

Write the original H rectangle as

    H=[-P_W,1-P_W] times [P_N-1,P_N].

Because (4) preserves the transverse port coordinates,

    (p_1)_x<0,       (p_5)_y>0.

Their membership in H now gives P_W>0 and P_N>0. Returning to (4),
the other two resultant components are also strict:

    (F_1)_y>0,       (F_5)_x<0.                          (6)

Thus both complete endpoint resultants lie in the strict northwest
quadrant. The actual ports p_1 and p_5 lie there too.

Put n=(-e_x+e_y)/sqrt(2). Every point on a physical boundary unit
has norm at least r=R-sqrt(2), by its diameter and any actual circle
corner. Since a northwest vector has l1 norm at least its Euclidean
norm, the unchanged ports satisfy

    n.p_i >= |p_i|/sqrt(2)
          >= (R-sqrt(2))/sqrt(2)
          >= sqrt(2)-1 > 2/5.                           (7)

The actual outer H arc from the top port to the left port passes
through H's northwest corner. On each of its two straight portions,
the n-projection is at least the smaller endpoint projection. Thus
the entire outer arc satisfies the same strict lower bound 2/5.

Every physical endpoint circle corner has n-projection greater than
1/2. Indeed the two possible physical circle corners on one unit have
angular separation 2 asin(1/(2R))<pi/6 when R>=2. Its nonzero
nonnegative resultant lies between them, so every physical corner is
within pi/6 of the resultant direction, even when one individual
weight is zero. For a one-corner mask the assertion is immediate.
Equation (6) puts the resultant within pi/4 of n, and consequently

    n.z > R cos(5pi/12)
        >= 2 cos(5pi/12) > 1/2.                         (8)

The final exact comparison is cos(5pi/12)>1/4, equivalently 49>48
after squaring positive radicals.

### 4.1. The corresponding outer circle arc is the northwest minor arc

The five positive whole-body circle resultants sum to zero, by summing
all six original body equations. Their circular order is the physical
boundary path order. This follows from the physical angular-neighbor
theorem, together with the local pi/12 corner/resultant-to-center
bound and the strict center separation greater than pi/5. Thus their
allowed center intervals are disjoint and preserve circular order.

Every consecutive resultant gap, including the closing gap from B_5
to B_1, is strictly less than pi. A larger gap would put all resultants
in an open half-plane; a gap equal to pi leaves the other three
distinct positive resultants strictly inside the complementary
semicircle and also cannot sum to zero.

By (6), the minor endpoint-resultant gap lies within the northwest
quadrant and is less than pi/2. It is therefore exactly their closing
gap. Choosing the actual endpoint circle corners facing that gap
preserves this order. The corresponding positive corner gap is less
than pi/2+2(pi/6)=5pi/6<pi. Both corners lie in the open n-cap from
(8), whose angular width is less than pi. Hence their corresponding
outer circle arc is the minor arc in that same n-cap. Every point
of the arc has n-projection greater than 1/2.

### 4.2. A complete occupied barrier, with original means retained

For the geometric barrier only, let a_1 be the gap-facing extreme of
the actual H--B_1 contact set on the top side: its leftmost point.
Let a_5 be the gap-facing extreme on H's left side: its highest point.
These choices do not replace p_1,p_5 in any force or moment equation.
They move along the same actual contact sets toward the outer hub arc,
so their n-projections are at least those in (7).

The endpoint units B_1 and B_5 are physically disjoint. A physical
contact between them would close the existing five-body boundary path
to a boundary five-cycle, excluded by `CIRCLE_CONTACT_ANGULAR_ORDER.md`.
Join each a_i to its actual gap-facing circle corner z_i by a path
inside B_i whose other points before z_i are in its open interior.
Such a path can be made of two straight segments through an interior
point arbitrarily close to a_i. Choose that point so its n-projection
still exceeds 2/5; convexity and (8) keep the entire path above this
level. These two endpoint paths are disjoint and meet H only at their
respective contact extremes.

Join a_1 to a_5 along the outer top/left boundary arc of H. It contains
no other positive hub spoke, by the original physical fan embedding.
The two endpoint paths and this H arc form a simple occupied crosscut
from z_1 to z_5, wholly in n.p>2/5. This construction includes full
side-contact segments and their weak endpoint limits. Extra zero-weight
contacts can subdivide the free pocket but cannot enlarge it.

Join the crosscut to the northwest circle arc of Section 4.1. The
whole Jordan boundary lies in n.p>2/5, so its bounded region is in
that same half-plane. The actual exterior pocket through H is precisely
this side of the crosscut: it follows the H outer arc and the closing
circle gap in the original exterior-face order. This is the occupied
crosscut argument, not an inclusion inferred from concurrence points.

Consequently every whole extra unit E in that actual pocket satisfies

    E subset {p : n.p>=2/5},
    dist(O,E)>=2/5>1/4.                                 (9)

## 5. The complete three-extra contradiction for this owner family

The fan is one of the three triangulated exterior-hexagon graphs.
The accepted `CHORDED_HEXAGON_CENTRAL_CAPACITY_ONE.md` gives zero
central capacity for its full bounded free union. Every exterior
pocket between two directly touching boundary bodies has zero unit
capacity by `CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md`. These facts
retain all original chord forces and all subdivisions by zero-weight
contacts. Thus all three physical completion units must occupy the
one exterior pocket through H.

In the only remaining adjacent-axis case, (9) puts each of these three
units at distance greater than 1/4 from O. Each of the five physical
boundary units has distance at least R-sqrt(2)>=2-sqrt(2)>1/4.
The whole-orientation arc theorem in
`GENERAL_SIDE_CHANNEL_CAP_INNER_ARC.md`, Section 1, gives each of these
eight actual units a disjoint open-interior radius-5/4 arc of angular
length greater than pi/4. Their total exceeds 2pi, a contradiction.

Sections 1--5 exhaust every original side-axis arrangement of both
endpoint hub normals, every physical endpoint mask, every internal square frame,
all original means and positive magnitudes, and every completion pose.
The entire both-endpoints-hub-owned owner family is therefore excluded.

The original fan with an oblique hub normal at either endpoint remains open.
No degree-five hub or internal degree-three boundary unit has been
turned into a transmitter or degree-two tip, and no positive chord has
been removed. This source does not close the fan graph, the other
chorded hexagons, or C1.6.b0. No numerical sample, Lean compilation,
CI run, remote write, or shared-ledger edit is used.
