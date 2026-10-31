# Every selected simple positive cycle separates central and exterior completion squares

Date: October 30, 2026. Author: common-certificate continuation.

**Status: complete proposed uniform physical theorem, frozen for separate
independent review.** This applies to an entire simple positive component,
with arbitrary load placement, side or diagonal transmitters, actual
shared means and physical circle masks. It proves strict separation of
all central/exterior pairs of additional squares. It does not exclude
the remaining completion configurations or close an original parent.

## 1. Entire original scope and common selection

Keep a packing of actual closed unit squares with disjoint open
interiors in the disk centered at O=0 with radius

    R>sqrt(2).

Use the original common physical force-and-torque certificate with its
physically compatible noncrossing embedding and the common generic
normal restrictions of the complete two-port theorem [G]. These
restrictions are imposed in the legitimate open normal domain before
extracting the certificate and survive matched uncrossing and thinning.
No original normal is reselected after its coefficients are obtained.
The separate accepted review [GR] checks that construction and theorem.

Assume that one entire positive body-pair component is a simple cycle
C. In particular each of its vertices has full positive body degree
two; it has no additional positive branch, chord or external edge.
All other physical contacts, including zero-stress ones, remain actual.
Every physical circle atom remains, including individual zero weights.
A loaded body means that its total circle coefficient is positive,
which implies physical contact with the same containing circle.

Use the compatible center/contact Jordan drawing of C supplied by
[P]. Its junctions can be routed in arbitrarily small neighborhoods
while retaining their physical cyclic sector order and every actual
circle-access spoke. The interior of any additional square misses
the closed core union. Its inside/outside winding label is therefore
stable under sufficiently small such routings. This is the physical
region convention established in [C], Section 2, including shared
endpoints and coincident contact limits.

An additional square is called central if it has the bounded-side
label and exterior if it has the unbounded-side label of this bare
cycle. A square in any actual exterior channel pocket is exterior
in this sense, even when circle spokes or further physical contacts
subdivide that pocket. No free region is identified with an artificial
force polygon or convex hull.

**Theorem 1.1.** Every central additional square T and every exterior
additional square E satisfy

    T intersect E = empty,
    dist(T,E)>0.

The theorem concerns the complete closed squares. Their positive or
zero stress status and their physical circle masks are unrestricted.
The proof consists of a purely geometric circle lemma, the full
unloaded two-port rule, and a complete local-sector separation argument.

## 2. Opposite squares in a four-square junction cannot both touch the circle

The physical local geometry [P], Section 1, gives the following exact
fact. At most four interior-disjoint unit squares meet at a point p.
If four meet, each contributes a right-angle inward tangent sector;
the four sectors fill a full turn, their frames agree, and their union
is the full aligned 2 by 2 block centered at p. Adjacent squares share
a full unit side and opposite squares meet only at p.

**Lemma 2.1.** Suppose this whole four-square block is contained in
D_R. If two opposite constituent squares physically touch its containing
circle, then p=O and R=sqrt(2).

Proof. In the common orthonormal frame, write p=(u,v). The full
block is

    [u-1,u+1] times [v-1,v+1].

Its largest squared norm is

    (|u|+1)^2+(|v|+1)^2.

Every point attaining this maximum is an outer corner of the block:
for either fixed coordinate, the squared norm is strictly convex in
the other coordinate, so an interior coordinate cannot attain its
maximum over a nondegenerate interval. An outer corner p+(epsilon,eta),
epsilon,eta in {-1,1}, is a maximizer precisely when epsilon is a
maximizing sign for u and eta a maximizing sign for v. Both signs
are possible in one coordinate only when that coordinate of p is zero.

A constituent square which physically touches the containing circle
has a point of norm R. Since the entire block is contained in D_R,
that point maximizes the norm on the full block. Each constituent
square contains exactly one outer corner of the block. Thus if two
opposite constituents touch the circle, their two opposite outer
corners are both maximizers. Both signs must then maximize in each
coordinate, giving u=v=0. The maximum norm is now sqrt(2), and the
physical boundary contact forces R=sqrt(2). QED.

The lemma permits arbitrary placement and rotation of the entire
block and covers every zero-coordinate tie. It uses physical circle
contact, not positivity of an individual corner coefficient. In the
strict domain R>sqrt(2), two opposite constituents consequently
cannot both be physically boundary squares.

## 3. A simple selected positive cycle has no supported opposite junction pair

**Lemma 3.1.** No positive cycle edge of C is the opposite pair at
an actual four-square junction.

Proof. Such an edge is a point-only vertex/vertex contact. The common
selected normal strictly exposes both original vertices and is a free
normal in the precise sense of [G], Section 2. Suppose one endpoint
V has total circle coefficient zero. The singleton subset {V} is then
entirely unloaded and its full positive cut consists of exactly its
two incident cycle edges. The complete two-port theorem [G], Theorem
3.1, says that neither cut contact can be a free vertex/vertex contact.
This contradicts the proposed edge. The theorem includes shared
contacts on the other cut edge and physically boundary unloaded bodies;
no contact or physical corner has been discarded.

Therefore both endpoints of the proposed opposite edge have positive
total circle coefficient. Both are actual physical boundary squares.
They are opposite constituents of the same full four-square block,
contradicting Lemma 2.1 because R>sqrt(2). QED.

The matched-parameter convention at a four-square junction causes no
exception. The complete two-port theorem covers the linked normals
explicitly, and the physically compatible extraction retains at most
one supported opposite pair. The proof neither changes the remaining
normal nor promotes any neighboring zero contact to a positive edge.

This conclusion is uniform in the cycle length, load allocation and
transmitter widths. It does require full cycle degree two. Merely
finding a cycle inside a larger positive graph does not supply its
unloaded singleton-cut hypothesis.

## 4. A central/exterior contact would require a supported opposite pair

The following is a separate geometric statement about any compatible
physical Jordan cycle, before using Lemma 3.1.

**Lemma 4.1.** If two actual additional squares T and E have distinct
central/exterior labels and touch at p, then exactly four actual
squares meet at p: T,E and two core squares V,W. The core squares
are an opposite pair, V-W is an original positive cycle edge, and
its actual application is the singleton p.

### 4.1. The contact must meet a positive cycle application

Choose any p in T intersect E. If p lies outside the closed core
union, a fixed small disk around p misses the core and every
sufficiently small physical junction routing. Join an interior point
of T to p and p to an interior point of E by short segments whose
other points are in the respective open interiors. The resulting
path avoids the cycle and gives the same winding label to both
interiors, a contradiction.

More generally, if no original positive cycle application is at p,
choose the center/application drawing and its sufficiently small
routings away from p. An open segment from the center of a convex
square to a boundary application lies in that square's interior.
It therefore cannot contain p, which also belongs to an additional
square, unless p is its boundary application. There are only finitely
many strands and junctions, so a fixed small disk can again be
avoided, giving the same contradiction.

This covers p meeting just one core square. It also covers two core
squares with a physical zero-stress mutual contact, or with a positive
shared interval whose original application is elsewhere. A zero
contact is not inserted as a cycle edge. No circle spoke creates
an exception: its open segment is in its own core interior, and a
containing-circle endpoint cannot be shared by two actual squares,
as proved in [P], Section 6.

Hence p is an original positive application of a cycle edge V-W.
The two distinct additional squares T,E also meet there.

### 4.2. The complete four-sector and shared-mean endpoint cases

There are at least these four actual squares at p, and the physical
sector bound allows no fifth. Thus their four inward sectors are
the aligned quadrants of Section 2, and p is a vertex of each.

If V,W were adjacent quadrants, T,E would be the other adjacent
quadrants. Inside a sufficiently small junction disk, route the
V-W cycle strand on the V/W side, preserving the original sector
order. The T and E sectors are connected to each other on the
other side of that strand. A short path between nearby interior
points of T and E then avoids the cycle, contradicting their
different stable labels.

This includes an original shared-side mean equal to p. Its force
application is not changed: only the geometric graph strand is
routed arbitrarily close to the actual common side, within the
occupied V/W sectors. Each of V,W has only one other cycle edge,
and that other edge cannot use p. Indeed only V,W,T,E meet at p,
while T,E are not core vertices and C is a simple cycle. Thus no
second cycle strand obstructs this local connection or changes the
required sector order. The routing stays arbitrarily close to the
original junction, so it preserves the eventual labels of interior
points and their compact connecting paths.

The adjacent case is impossible. Therefore V,W are opposite
quadrants, their actual intersection is the singleton p, and the
positive V-W edge is the opposite pair claimed in Lemma 4.1. T,E
are the other opposite pair. This proves the lemma with every
physical weak junction and shared-mean endpoint retained.

## 5. Complete proof, uniform callers and retained constraints

If a central T touched an exterior E, Lemma 4.1 would produce
a supported opposite junction pair. Lemma 3.1 excludes that pair
in the same original common selected cycle. Hence their closed
intersection is empty. Compactness of the two actual squares gives
a strictly positive minimum distance. This proves Theorem 1.1.

There are finitely many actual additional squares. Consequently,
if both classes are nonempty, the minimum of these pairwise
central/exterior distances is also positive. Every sufficiently
small simultaneous motion of the additional squares therefore has
strict initial clearance across these pairs. This statement removes
only their mutual active-contact constraints; it does not provide
any motion respecting their other neighbors or circle containment.

The theorem gives the following actual uniform applications.

| Original entire component | Complete additional restriction |
| --- | --- |
| Every remaining simple C6 load/channel family in [C], Section 3 | Every centrally placed extra is closed-disjoint from every extra in any actual exterior channel cap, including both central extras when two are present. |
| Every no-long simple C7 with four, five or six loads | The same conclusion holds for every central/exterior pair among the two actual extras, across all side/diagonal assignments and all physical one-/two-circle and shared/singleton masks. No assumption that a central extra exists is added. |
| The two-RR seven-cycle X-U+-A-U3-D-B-U--X | Its one actual central extra and its one occupied third-pocket extra are closed-disjoint. This uses their already proved region labels and no feature of the surviving direct-return owner. |
| Any other entire selected simple cycle at R>sqrt(2) | Every central/exterior pair of actual completion squares is closed-disjoint, with the same full-degree and common-selection hypotheses. |

For the project radius window 79/40<=R<=sqrt(1105)/16,
R>sqrt(2) is automatic. The theorem is not restricted to the
boundary-only cycle case or to physically clear transmitters.
It does not require minimum Phi, absence of zero contacts,
positive individual radial corner weights, fixed shared means,
all-side transmission or an unblocked physical star.

Contacts within the central class or within the exterior class
remain possible. So do every extra/core contact, every nonconsecutive
core contact, all actual circle constraints and all shared-side
interval constraints. In particular a central extra can still block
several transmitters, and a transmitter can still communicate a
motion constraint between that central square and an exterior
pocket square. This separation does not by itself eliminate such
a network or close any original coarse or fine parent.

## 6. Complete direct sources and review boundary

| Label | Complete source or review | SHA-256 |
| --- | --- | --- |
| [P] | PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe |
| [C] | SIMPLE_CYCLE_CHANNEL_POCKET_CAPS.md | f9a008a8cebb02825891d773afeafa0fa953f5c499988bdaae0bac947ff6f1e7 |
| [G] | GENERIC_TWO_AND_THREE_PORT_CUT_RULES_FOR_ARBITRARY_UNLOADED_BODY_MODULES_2026_10_30.md | f6b12507086fd284e99b637748ef3b40c994c56aba44264a2c3a408338181251 |
| [GR] | REVIEW_GENERIC_TWO_THREE_PORT_UNLOADED_MODULE_CUTS_BRANCH_BUDGET_INDEPENDENT_2026_10_30.md | b8c0e97d822da38d43bf5577ec9a85bea75eec059751a1afcc020ecd6e4e4dcd |
| [N] | RADIAL_RADIAL_TRANSMITTERS_CAN_SLIDE_OUTWARD_AND_CANNOT_FORM_A_CLOSED_TWO_BODY_BLOCKER_NETWORK_2026_10_30.md | 0fbcce339700b2d2e23fa30a516a64c2773e868b90ed60f695fcc93ac4cafff7 |

All five complete texts were read and their exact pins checked.
Only [N], Section 8, supplies the one-central/one-exterior labels
for the specific two-RR caller; it is not needed in the general
proof. The proof of Theorem 1.1 uses [G], Theorem 3.1 only,
and does not depend on its three-port determinant rule or a
symbolic rational-mean claim. [GR] is the separate accepted
noncontributor gate of that common-selection input. The author's
own earlier cut and outward-network sources are not independently
reviewed by this manuscript.

The local-sector argument first appeared in the unadopted two-RR
network continuation. The present manuscript supplies its full
uniform four-junction/circle and generic two-cut join, and states
all actual callers and remaining constraints. Root separately
confirmed the geometric outline; a full independent read of this
frozen source remains required before adoption.

No numerical pose or angle search, grid, optimizer, new computational
packing certificate, Lean/Lake invocation, CI, physical deletion,
normal replacement, new positive edge, metadata edit or remote
operation was used. Original inventories and closure counts remain
unchanged.
