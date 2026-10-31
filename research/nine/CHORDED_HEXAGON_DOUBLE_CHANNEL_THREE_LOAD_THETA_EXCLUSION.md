# Two parallel side channels exclude the whole three-load theta family

Date: October 27, 2026.

**Status: complete proposed original-load-family exclusion, pending full
root and separate independent review.** No original gate or shared
ledger is changed.

Keep the unchanged compatible selected certificate and all nine actual
interior-disjoint unit squares in

    79/40 <= R <= sqrt(1105)/16.

The exact positive component has six actual bodies X,Y,Z,U,V,W and
the seven positive edges

    XU, UY, XV, VY, YZ, ZW, WX.

Exactly X,Y,Z have positive circle load. U,V,W have their true degree
two and zero circle load; physical circle contact at a zero weight is
not removed. X,Y have their true degree three and Z degree two. Every
actual circle atom, selected normal, original shared-side mean,
zero-stress physical contact and the other three units is retained.

**Theorem.** This entire original graph/load configuration is impossible.

In the original interior-pentagon graph with spokes H0,H2 and no outer
chord, this is the full load set 023, with

    X=0, Y=2, Z=3, U=H, V=1, W=4.

The theorem therefore excludes exactly the complete original orbit
`M6.B6.PENTAGON.H2_D0.L023` and all its original graph-preserving
reflections. It does not close the other load orbits or the whole
H2_D0 graph.

The proof below uses sums of actual parallel forces and their exact
moments. No original force is removed. The resulting weighted point
on an endpoint is expressly not asserted to be a new pair contact,
and no physical or virtual transmitter is inserted at that point.

## 1. A loaded unit with two full parallel-force groups

We first state the exact local algebraic scope needed at the true
degree-three bodies X and Y.

Let S be a physical loaded unit. Partition all its original positive
pair forces into two nonempty groups, so every normal in group i is
the same actual outward unit normal n_i. Put

    mu_i = sum_(j in group i) mu_j > 0,
    p_i = (sum_(j in group i) mu_j p_j)/mu_i.

Keep its entire original circle resultant F. Direct summation gives

    F+mu_1 n_1+mu_2 n_2=0,
    mu_1 det(p_1,n_1)+mu_2 det(p_2,n_2)=0.          (1)

These are its original full force and origin-moment equations.
Each p_i is on the actual support face of S normal to n_i: all the
original p_j are on that same face, and the face is convex. Also

    |p_i|<R,              p_i.n_i<=R-1.              (2)

For the first inequality, a real contained neighbor cannot share a
circle point of S. Every original p_j is strictly inside the circle;
their finite positive convex combination remains strictly inside.
For the second, any one of the original neighbors in that group lies
beyond the same supporting line and has width at least one in n_i.
Its containment gives h_S(n_i)+1<=R. This argument does not need a
neighbor whose actual contact equals p_i.

### 1.1. Nonparallel group lines have proper positive radial concurrence

If n_1,n_2 are nonparallel, let q be their lines' intersection through
the displayed p_i. Then

    q=t F, t>0,
    p_i=q+a_i n_i, a_i>=0.                          (3)

Here is the complete reason the usual loaded-unit normal-line proof
has this scope. Torque about q in (1) gives det(q,F)=0. If the two
displayed points coincide, q is that point. For each positive circle
corner z of S,

    2 q.z = |q|^2+R^2-|q-z|^2 >= |q|^2+R^2-2 > 0.

Thus q.F>0 and q is a positive multiple of F; both proper lengths
are zero.

For distinct displayed points, the following full physical corner
cover uses only that they are support points of S and satisfy (2).
It is the exact rectangle calculation in `C7_FORCE_POLYGON.md`,
Sections 4--5, with the boundary-neighbor exclusions used only for
an all-boundary cycle omitted as specified below.

If S has one physical circle corner, choose its own orthogonal chart

    S=[a-1,a] x [b-1,b],
    a>=b>=1/2, a^2+b^2=R^2.

Then F is a positive multiple of (a,b) and q=tau(a,b). The interval
1-1/a<=tau<=1 puts q inside S. If tau>1, the only normal-line
vertices are the outer circle corner and the opposite inner corner;
no side-interior normal line is available. The circle point is
forbidden by (2), and two distinct points cannot both be the inner
corner. If tau<1-1/a and q_y<b-1, the same two-vertex alternative
applies. At q_y=b-1 the extra outward horizontal support has height
a>R-1, also forbidden by (2).

In the remaining outside strip q_x<a-1 and b-1<q_y<b, the possible
non-circle points are the left-side point at height q_y, an outward
horizontal right-side point, and the lower-right vertex. The right
side again violates (2). Distinctness requires the lower-right
vertex, whose outward normal has slope in

    0<=tan(eta)<(a-b)/a.

Its support is at least R/sqrt(2)>R-1, by the exact endpoint
calculation in that source's equations (18)--(20). For clarity, the
nonnegative polynomial there is

    (a-b)[2b^2(2-b)+(a-b)(2+4b-3b^2)
                          +(a-b)^2(4-2b)].

All bracket coefficients are positive for 1/2<=b<3/2. Thus this
last outside alternative also violates (2). Consequently q belongs
to S. Since a>1, its radial scalar is positive. Its position in the
supporting half-planes gives the two proper signs in (3).

If S has two physical circle corners, use the full radial chart

    S=[d,d+1] x [-1/2,1/2],
    d=sqrt(R^2-1/4)-1>9/10,
    F a positive multiple of (d+1,eta), |eta|<=1/2.

This includes either zero individual corner weight. Write
q=tau(d+1,eta). If tau<d/(d+1), the rectangle normal-line cover
has at most one non-circle support point once the outward right
face of height d+1>R-1 is excluded. This includes both equalities
|q_y|=1/2. It contradicts the two distinct displayed points.

For d/(d+1)<=tau<=1, q is in S and (3) follows. If tau>1 and
|q_y|>1/2, at most one non-circle support point is available, again
impossible. In the remaining tau>1, |q_y|<=1/2 case, the outward
right face is forbidden by (2); every possible non-circle point is
on the inner face or its endpoints. Since q_x>d+1, the vector from
q to each such point is in its outward-normal direction. Thus both
proper signs still hold, although q need not be in S. In every
case tau>=d/(d+1)>0. This proves (3) for the complete physical
circle-mask and grouped-mean domain.

No part of this proof asserts that p_i is a real contact with a
single neighbor. The support features, the strict absence of a circle
application and the width bound (2) are exactly the geometric data
used, and they have been proved from the full original groups.

### 1.2. The complete parallel-group alternative

If n_1,n_2 are parallel, put e=F/|F|. Every original group normal
is e or -e. None can be e: that direction supports a unique circle
corner, or in the symmetric two-corner case the radial outer side
of height d+1>R-1. Both are prohibited by (2). Hence all the original
pair normals are -e.

With a unique physical circle corner, -e strictly exposes its
opposite vertex. Zero origin moment in (1) makes that opposite
vertex radial. The actual frame is diagonal about e and the unit
is the radial D square, with the common inner point

    p_D=(R-sqrt(2))e.                                (4)

With two physical circle corners, write the radial chart above.
If eta is nonzero, the opposite support is the inner corner of
opposite transverse sign, which cannot have zero moment about the
positive (d+1,eta) direction. Thus eta=0. The actual unit is radial
S and the total weighted mean on its inner face is d e. All
individual applications retain their actual transverse coordinates
in [-1/2,1/2]. This is the entire S/D alternative, without a degree
assumption or a replacement of any individual force.

## 2. The two actual X--Y channels have the same side direction

Each of U,V is a genuine unloaded degree-two normal transmitter.
The other is a real unit bypass touching both endpoints. The full
radius-free theorem `UNIT_BYPASS_NORMAL_CHANNEL.md` therefore gives
width one for both. Their normal directions are identical: both
realize the unique shortest displacement between the closed convex
endpoint units X,Y. This is the original shortest-channel lemma,
also proved in Section 1 of
`TWO_PARALLEL_TRANSMITTERS_NO_THIRD_BYPASS.md`.

Let n point from X toward Y. Write the unchanged applications and
positive magnitudes as

    p_XU, p_UY=p_XU+n,       alpha>0,
    p_XV, p_VY=p_XV+n,       beta>0.                  (5)

The equality of the two magnitudes along each separate channel is
its own full translation balance. The equal displacements are its
own full torque and width-one geometry. No means are reset.

Both endpoints X,Y in fact own the common normal as an actual side
axis. The proof is exactly Section 2 of the same two-transmitter
source: if an endpoint had a unique support vertex, both channels
would meet it at their touching transverse endpoints. Their positive
axis contacts would then be forbidden singleton vertex/vertex
normals. Thus both endpoints are aligned with the side transmitters,
and each actual endpoint/transmitter support overlap has positive
length. This local argument does not need a third bypass and places
no restriction on the other original endpoint forces.

Define only the two endpoint weighted points and total magnitude

    mu=alpha+beta,
    P_X=(alpha p_XU+beta p_XV)/mu,
    P_Y=(alpha p_UY+beta p_VY)/mu.

Then the following are exact identities of the original forces:

    P_X in X, P_Y in Y, P_Y-P_X=n,
    both points are on their unchanged channel support faces,
    sum of the two X forces = mu n,
    sum of the two Y forces = -mu n.                 (6)

Their moments are mu det(P_X,n) and -mu det(P_Y,n).
These statements keep the two original application means on each
endpoint. P_X,P_Y are only their displayed weighted averages. They
are not given a physical pair edge and are not assigned to any new
square.

The remaining actual W channel joins Z and X and has its complete
original reserve w in {1,sqrt(2)}. The positive YZ edge is a genuine
contact between two physical boundary units.

## 3. All three loaded resultant-line pairs are nonparallel

At X the two full groups are its U,V forces and its original W force.
At Y they are its U,V forces and its original Z force. At Z its
two original pair forces remain separate. These partitions exhaust
the true full force equations at X,Y,Z, and Section 1 applies.

First Y cannot have parallel group normals. Section 1.2 would make
it radial S or D, with its actual YZ force on the radial inner
support. In radial S, the full horizontal-inner-face statement of
`C7_FORCE_POLYGON.md`, Lemma 2.1, makes every actual neighbor there
physically circle-clear, contrary to Z's real boundary contact. In
radial D the actual YZ application is (R-sqrt(2))e. A second
boundary unit containing that point would need its circle corner
at distance at most sqrt(2). Equality in the triangle inequality
forces the same outer circle point R e as Y, impossible for two
interior-disjoint contained units. Thus Y is nonparallel.

Z is a genuine degree-two loaded unit with boundary neighbor Y.
Its ordinary full proper-concurrence theorem likewise makes its
two pair normals nonparallel.

Suppose X's two group normals were parallel. Again Section 1.2
gives radial S or D. The actual U channel is side-normal of width
one. If X is radial S, its original U application is (d,y) in its
radial frame, |y|<=1/2, and its actual far application belongs to
the physical boundary Y at (d-1,y). Since

    9/10<d<61/60, |d-1|<1/10,
    r=R-sqrt(2)>14/25,

that actual point has squared norm less than

    1/100+1/4=13/50<(14/25)^2<r^2.                  (7)

Every point of a boundary unit instead has norm at least r.
If X is radial D, the actual U application is r e and its far
application on Y is (r-1)e. Here 1/2<r<1, so |r-1|<r, the
same physical contradiction. Therefore X is also nonparallel.

By Section 1.1, all three full resultant-line intersections are

    q_i=t_i F_i, t_i>0, i=X,Y,Z,

and every displayed group application is proper behind its original
outward normal. This does not assert that the radial two-corner
q_i lie inside their units or inside the containing disk.

## 4. The exact full-force concurrence triangle

Orient the three directed links X to Y, Y to Z, Z to X. The first
is the actual sum in (6), the second is the real YZ force, and the
last is the unchanged W transmission. Keep their positive magnitudes.
Properness at each displayed endpoint gives

    q_Y-q_X=(a_X+1+a_Y)n_XY,
    q_Z-q_Y=L_YZ n_YZ,
    q_X-q_Z=(b_Z+w+b_X)n_ZX,                         (8)

where all a_i,b_i are nonnegative. L_YZ is strictly positive:
otherwise the positive radial concurrence directions of the distinct
boundary units Y,Z would coincide. Thus all three links have
strictly positive lengths.

The full original origin moments give one common directed moment
on these three links. At X and Y this is direct summation of their
two channel moments, not a separate physical equation for a smaller
degree. Equality across X--Y also follows immediately from
P_Y-P_X=n. At W it is the original unchanged degree-two torque.
Call the common value H_0. The real YZ boundary contact has nonzero
moment, so H_0!=0. If necessary reflect the common coordinate
orientation, keeping these same directed labels, so H_0>0.

The identity at each side of (8) is then

    det(q_i,q_(i+1))=L_i H_0/mu_i>0.                (9)

The three consecutive positive radial increments lie in (0,pi).
Their sum is a positive integral multiple of 2pi and is below3pi,
so it equals2pi. The triangle is simple and has O in its strict
interior. Equivalently, its three directed sides put O strictly on
the left by the common positive moment; the positive radial order
rules out degeneracy. These are exactly the force-polygon identities
proved here from the original full endpoint equations.

The physical boundary-center directions and the positive circle-
resultant directions have the same circular order. The complete
corner/center separation theorem applies to the actual boundary
units X,Y,Z; additional physical boundary units at zero weight only
impose further restrictions. The actual YZ contact uses the minor
consecutive center arc. The other two consecutive arcs are the
outward channel arcs of (8), as checked next.

## 5. The two entire channel-angle bounds retain their real endpoint geometry

We give the precise inheritance from
`FIVE_CYCLE_THREE_LOAD_EXCLUSION.md`, Sections 1--4, rather than
calling its exact-degree-two component theorem on this graph.

For a link of reserve w_0=1 or sqrt(2), orient its actual support
points as

    P_left=(l,h), P_right=(l+w_0,h), h>0,

with O on the inward side of the strictly positive-moment edge.
For X--Y these are exactly the weighted points (6); for Z--X they
are the two original actual W applications. Both are support points
of their actual loaded endpoints. Properness makes their radial
concurrences have the same positive height h.

The horizontal center gap is w_0 plus the two true square
halfwidths, hence at least two. Their center norms are below91/60,
so their horizontal signs oppose. The full endpoint argument in
the cited source then gives their vertical center coordinates
nonnegative. For an oblique endpoint its support point is a vertex;
a nonpositive center height would make all farthest circle corners
strictly negative in height, contrary to its positive vertical
circle resultant. In the aligned case the same statement retains
the zero center-height, two-corner endpoint. The X--Y endpoints are
aligned already; no actual-neighbor incidence at their weighted
points is needed in this geometric calculation.

Consequently each relevant center arc is the upper minor arc,

    gamma=pi-delta_left-delta_right,
    delta_left,delta_right>=0.                      (10)

The radial order and inward origin side in Section 4 identify this
minor arc with its actual consecutive arc, including every zero
center-height endpoint. The third loaded center lies on the other
arc.

Set theta=arccos(9/25) and beta=theta/2, so
cos(beta)=sqrt(17)/5. Every actual boundary center has norm>19/15.
For any reserve-one link, its two displayed endpoint points are in
their actual unit squares and are distance one apart. Hence

    |c_right-c_left|<=1+sqrt(2).                     (11)

This applies to (6) exactly as written, without an intervening new
square. If gamma>=pi-beta, the center lower bounds instead give

    |c_right-c_left|^2
       >(722/225)(1+sqrt(17)/5)
       >65702/11250>583/100>(1+sqrt(2))^2.           (12)

Thus every reserve-one arc has gamma<pi-beta.

Only the real W channel can have reserve sqrt(2). The original
compatible diagonal avoidance puts both of its actual endpoint
applications in relative interiors of endpoint sides. Hence those
two loaded frames share the channel axis and their exact horizontal
center gap is 1+sqrt(2). No endpoint degree is used by that physical
normal-selection consequence.

The complete strict concavity calculation in the cited source's
Section 3 applies to the horizontal coordinate x_R(delta) of an
aligned boundary center. If gamma>=pi-beta, (10) gives
delta_left+delta_right<=beta and therefore

    1+sqrt(2) >= x_R(0)+x_R(beta)
                >7/5+779/750
                =1829/750>17/7>1+sqrt(2),           (13)

an impossibility. In its exact derivative formula the controlling
factor has lower bound 4r_c^2-r_c-sqrt(2)>3-sqrt(2)>0, since the
actual boundary center radius r_c>1. Thus this is the same whole-
angle strict concavity argument, not a discrete orientation check.
It depends only on the actual two endpoints, the real diagonal
reserve and their proper radial lines, all established above.

Both entire channel arcs therefore satisfy gamma<pi-beta for all
original masks, frames, mean endpoints and the full R interval.

## 6. The real boundary edge completes the contradiction

The actual touching boundary units Y,Z have center distance at most
sqrt(2), while both center radii exceed5/4. Their minor center-angle
gap is therefore strictly below theta=arccos(9/25). Physical boundary
angular order identifies it with their consecutive arc in Section 4.

The two channel arcs and this real boundary arc form the full turn
of the three actual loaded center directions. Sections 5--6 give

    2pi = gamma_XY+gamma_YZ+gamma_ZX
         <(pi-beta)+theta+(pi-beta)=2pi,

because 2beta=theta. This contradiction excludes the whole component.

Every algebraic group used its complete original force and torque.
Every metric point in (11)--(13) belongs to its actual endpoint unit.
The width-one identity for the doubled channel is the weighted sum
of its two real width-one identities. The other width and all
diagonal selection statements concern the unchanged actual W.
There is no invented physical comparison packing or erased channel.

## 7. Exact original-parent join and limitations

For the original no-chord two-spoke interior-pentagon graph, take
X=0,Y=2,Z=3,U=H,V=1,W=4. Under the entire original load set023,
H,1,4 are indeed true unloaded degree-two bodies, 0,2 are true
degree three, and3 has true degree two. The three positive paths
and real boundary edge are exactly those in this theorem. All
three arbitrary original completion units stay in place, although
the contradiction already concerns the complete six-body force
and geometry domain. Reflection gives the original equivalent024
labeling.

Thus the complete original gate `M6.B6.PENTAGON.H2_D0.L023` is
mathematically excluded by this source, pending the stated reviews.
No pose subdivision, circle-mask restriction or completion placement
was used. The remaining H2_D0 load sets013,134,1234,0124 and the
whole graph parent retain their own obligations.

The grouped-force lemma is available at a higher-degree body only
when all its actual positive pair forces have the two stated normal
directions. It does not permit arbitrary forces to be discarded or
rotated, and a general chorded graph need not satisfy that premise.
The double-channel identity requires its two actual true unloaded
transmitters. A loaded bypass cannot be grouped as if it were an
unloaded transmitter.

No original atom, circle weight or occupied square is deleted; no
actual mean is replaced; no selected normal is changed; no Lean
compilation, CI, numerical pose, remote write or shared-ledger
mutation is used.
