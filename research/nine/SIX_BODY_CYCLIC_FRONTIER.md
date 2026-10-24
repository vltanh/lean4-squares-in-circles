# The complete six-body cyclic frontier

**Status: complete hand graph, attachment, load and plane-domain cover;
root and separate independent full hand audits passed.** This manuscript refines every six-body row of the positive
cyclic inventory. It proves the graph and attachment cover below. It
does not prove a sharp radius or completion theorem for an open row.

Use the same selected simple plane positive graph as the main proof.
The full physical contact graph may have additional edges, including
zero-weight contacts at common junctions. There are three additional
physical squares outside a six-body positive component; every one of
them remains in the completion problem.

Inherited geometric statements use the declared window
79/40<=R<=sqrt(1105)/16. The abstract block and embedding counts
themselves have no radius premise.

## 1. Exactly six coarse profiles

For cyclic block sizes s_i and bridge count b, the block-tree identity
in CYCLIC_BLOCK_INVENTORY.md is

\[
                     m=1+\sum_i(s_i-1)+b.
\tag{1}
\]

Each cyclic block has at least three vertices. At m=6 there can be
one or two cyclic blocks, since three would contribute at least six
to the sum in (1). The possibilities are exactly

| Coarse row | Cyclic blocks | Bridges | All remaining physical squares | Whole hand status |
| --- | --- | ---: | ---: | --- |
| C1.3.b3 | One triangle | 3 | 3 | CLOSED; all seven attachments |
| C1.4.b2 | One four-body block | 2 | 3 | OPEN |
| C1.5.b1 | One five-body block | 1 | 3 | OPEN |
| C1.6.b0 | One six-body block | 0 | 3 | OPEN |
| C2.33.b1 | Two triangles | 1 | 3 | OPEN |
| C2.34.b0 | A triangle and a four-body block | 0 | 3 | OPEN |

This is an exhaustive coarse list. The following sections refine its
actual graph layouts, rather than choosing numerical poses.

## 2. One triangle with three bridges: seven rooted layouts

Delete the three triangle edges. Every remaining nontrivial component
is a tree attached to exactly one triangle vertex. Attachment to two
different triangle vertices would put those connecting edges on a
cycle, contrary to their being bridges. A detached component would
contradict connectivity of the positive component.

The three outside vertices are therefore distributed among trees rooted
at the three triangle vertices. Up to triangle symmetry, their counts
are 3, 2+1, or 1+1+1.

For the count3, the rooted tree has four vertices including its root.
There are exactly four possibilities:

1. A length-three chain from the root.
2. One edge from the root to a vertex with two leaf children.
3. One leaf at the root and a separate length-two arm from the root.
4. Three leaves directly attached to the root.

Indeed the root has degree1, 2, or3 in this tree. Degree1 leaves
a three-vertex tree rooted at its neighbor, which is either a chain
or a two-leaf fork. Degree2 forces subtree sizes1 and2. Degree3
forces three single leaves. This proves the four-item cover.

For the count2+1, the two-edge rooted tree is either a chain or two
leaves at one root; the other root has a single leaf. These give two
further layouts. The count1+1+1 gives one leaf at each triangle vertex.
Thus there are exactly seven abstract rooted layouts.

The fourth layout, three leaves at the same triangle articulation,
is excluded by ONE_ARTICULATION_TRIANGLE_LEAF_EXCLUSION.md. The entire
first layout is now excluded by TRIANGLE_THREE_BRIDGES_LONG_CHAIN_EXCLUSION.md,
including its initially possible loaded intermediate vertex. The entire
sixth layout, two leaves at one root and one leaf at another, is excluded
by TRIANGLE_THREE_BRIDGES_DOUBLE_LEAF_ROOT_EXCLUSION.md. Its full two-leaf
central-disk theorem and exact d=1 exception retain every actual root
force. OUTER_BRIDGED_TRIANGLE_EXCLUSION.md now excludes the entire second
layout as well: the two-leaf fork body contains the required central
disk, and its actual bridge points outward into a true end triangle.
TRIANGLE_THREE_BRIDGES_DISTINCT_ARM_EXCLUSION.md now excludes the
entire fifth layout, a length-two arm and a leaf at different roots.
The actual three external resultants have nonzero common cycle moment;
RADIAL_TRIANGLE_CONCURRENCE.md proves positive concurrences even when
one of the other roots has parallel cycle forces. The arm's small
support and the direct-leaf root's central disk then exclude every
aligned or tilted arm root, retaining both true degree-three equations.

TRIANGLE_THREE_BRIDGES_MIXED_ARMS_EXCLUSION.md closes the entire
same-root mixed-arm layout. Its full D and S companion proofs retain
the genuine four-force articulation. The S proof excludes every
noncritical core and the entire critical endpoint: the opposite-leaf
case invokes the actual P skeleton with all five other physical units.

TRIANGLE_THREE_DISTINCT_LEAVES_EXCLUSION.md closes the final layout,
one genuine leaf at each triangle root. Below d=1 the central roots'
tangent half-planes contradict disjointness. At d=1 the actual three
root-and-terminal rays route the three roots and three extras into
wedges of total capacity at most5. Above d=1, the full zero-moment
alternative is excluded; positive radial concurrences then exclude
all D and tilted-S roots. Aligned nonparallel roots would have radial
concurrences beyond4 while their actual contacts have norm<61/60.
Both the all-nonparallel and one-parallel alternatives are excluded.

**All seven rooted attachments and the entire C1.3.b3 cell are CLOSED
hand**, by TRIANGLE_THREE_BRIDGES_CELL_CLOSED.md. Root and independent
full audits passed both final attachment proofs and the complete
assembly. Every true degree, physical mask and actual mean remains.
The two critical capacity exits explicitly count all three extras;
the assembly makes no isolated-core claim at those endpoints.

## 3. One four-body block with two bridges: eleven layouts, nine remaining

A simple biconnected graph on four vertices is C4, the diamond, or K4.
For completeness, minimum degree2 gives at least four edges. With
four edges every degree is2 and the graph is C4; five edges give K4
minus one edge; six give K4. NO_POSITIVE_K4_SUBGRAPH.md excludes the
last possibility even inside a larger component.

The two outside vertices can form a length-two arm, two leaves at the
same block vertex, or one leaf at each of two different block vertices.
The forest argument from Section2 proves this list is exhaustive.

| Block | Length-two arm root orbits | Two leaves at one root | Distinct-root pair orbits | Total |
| --- | --- | --- | --- | ---: |
| C4 | One vertex orbit | One vertex orbit | Adjacent or opposite | 4 |
| Diamond | Degree3 hub or degree2 tip | Hub or tip | Two hubs, two tips, or hub/tip | 7 |

In the diamond every hub touches every tip, so all unordered hub/tip
pairs are equivalent. The two hubs are mutually adjacent; the two tips
are not. These are all its vertex and pair orbits. Hence the table
has eleven complete abstract attachment classes.

The closed four-body-block-plus-one-leaf theorem cannot be applied by
discarding a positive second leaf or arm. The root's force and torque
equations change, and a tip with a new bridge may have positive degree3.
ROOTED_BLOCK_ATTACHMENT_OBSTRUCTIONS.md excludes the entire diamond
arm-at-tip and two-leaves-at-one-tip layouts. Both unchanged hubs retain
positive degree three and the other tip degree two, forcing a physical
boundary triangle. Nine full attachment classes remain; no hub-rooted
or distributed-root diamond case is excluded by that argument.

### 3.1. All remaining load, leaf and transmitter-width domains

FOUR_BODY_BLOCK_TWO_BRIDGES_LOAD_COVER.md supplies the full necessary
refinement of the eleven attachments. The nine open layouts have
thirteen whole positive block-load orbits and thirty-five complete
leaf/width alternatives, with every actual root force retained.
The asymmetric C4 adjacent-root/single-load family keeps both mixed
S/D orders; no root swap is used unless it also preserves the load set.

TWO_LEAF_ROOT_NO_UNLOADED_TRANSMITTER.md is a uniform new completion
obstruction. A two-leaf root's actual central disk contradicts the
support bound across any adjacent true unloaded transmitter, except
at d=1. There, exact support equality forces a physical third S unit,
without assigning it degree one. The strict opposite-quadrant domain
is the full actual Y cage. At an axis endpoint the other genuine leaf
forces the whole P slider, even when the original mean is nonzero.
Both critical capacity theorems count every original body.

Consequently C4 with two leaves at A retains precisely block loadsBD
orBCD. C4 with leaves at opposite roots A,C requires both B,D loaded:
an unloaded channel cannot join two units that each meet D_epsilon,
since its reserve would satisfy1<=w<=2epsilon<1/30. At distinct roots
every whole D/D leaf assignment is impossible because both actual
roots would contain O in their open interiors. Each remaining mixed
S/D assignment requires d>1, with that entire high-radius domain kept.

All arm alternatives S/side,S/diagonal,D/side remain explicitly;
the D/diagonal bridge is excluded by its original off-origin vertex
normal condition. The arm root is physically clear by its actual
application of norm<31/60<r. The complete C4 and diamond load table
uses each body's true total degree before forcing a load. Root and
independent full audits passed both source files, all critical means
and every full graph/symmetry application. There are still2 of11
whole attachments closed and9 open; C1.4.b2 remains open.

## 4. One five-body block with one bridge: sixteen rooted block types

The bridge attaches one genuine degree-one leaf to a vertex of the
five-body block. The ten abstract biconnected types on five vertices
are enumerated by the complement-degree proof in
FIVE_BODY_BICONNECTED_REDUCTION.md, Section2. That enumeration uses
only biconnectivity and is still valid for a block in a larger graph.

Three of the ten types contain K4: K5 minus two adjacent edges,
K5 minus one edge, and K5 itself. They remain excluded by the global
positive-K4 theorem. The other seven types and all root orbits are:

| Five-body block | Root orbits | Number |
| --- | --- | ---: |
| C5 | Any cycle vertex | 1 |
| House | Roof, one of the two degree3 hubs, or one of the two lower degree2 vertices | 3 |
| K2,3 | A vertex in the two-part or in the three-part | 2 |
| Three-page book | A hub on the common edge, or a page tip | 2 |
| Four-path fan | Universal hub, path endpoint, or inner path vertex | 3 |
| K4 with one edge subdivided once | New subdivision vertex, an endpoint of the subdivided edge, or one of the other two vertices | 3 |
| Four-rim wheel | Hub or rim vertex | 2 |

The indicated within-class symmetries are graph automorphisms. The
displayed classes cannot be interchanged: degree, adjacency to the
unique degree2 subdivision vertex, or the house roof distinguishes
them. Thus there are exactly sixteen rooted abstract block types.

Crucially, the old load-connectivity exclusions for an **entire**
five-body component do not exclude all seven blocks here. The extra
loaded leaf is another vertex in the loaded noncontact graph. It may
connect previously separate complement components. Similarly, the
exact C5 component theorem cannot be imported at its bridge-attached
root, whose degree is now3. The positive-K4 subgraph theorem has no
such limitation and was legitimately used above.

For every row retain both actual S/D leaf geometries, the root's
additional force and torque, all block circle masks and all three
completion squares. The sixteen-type catalogue is a domain cover,
not a geometric existence assertion. ROOTED_BLOCK_ATTACHMENT_OBSTRUCTIONS.md
excludes the entire book-hub and wheel-hub leaf attachments. The book
would have three loaded common neighbors, and the wheel four loaded
rim vertices. The other fourteen full rooted types remain open.

### 4.1. Complete positive-load and leaf-type refinement

FIVE_BODY_BLOCK_LEAF_GRAPH_LOAD_COVER.md now proves the complete
necessary load cover of all sixteen rooted types by hand. The leaf
root stays physically clear and the genuine S/D leaf is always loaded.
The fourteen open types retain38 whole block-load orbits; each includes
all root-preserving images, every original circle mask and actual mean.
The full positive-loaded complement is automatically connected because
the actual leaf is nonadjacent to every block load. Thus no isolated
five-body complement exclusion is imported.

Six further whole both-S/D families are excluded. Two rooted C5
load families have actual two-transmitter channels with a unit bypass.
In two house families, an actual unloaded channel would separate its
endpoints despite their positive physical contact. In the hub- and
tip-rooted K2,3 families, two true unloaded transmitters have a third
physical bypass; TWO_PARALLEL_TRANSMITTERS_NO_THIRD_BYPASS.md excludes
that full local configuration without deleting the root leaf force.

Four remaining whole S alternatives are also excluded by
S_LEAF_CONNECTED_BOUNDARY_NEIGHBORS.md: the fan-hub mask1234, the
subdivided-K4 endpoint maskCD, and its other-original-vertex masksDA
andDAB. Their full D alternatives remain open. This closes the entire
S leaf type for the fan-hub and subdivided-edge-endpoint roots, but
neither whole rooted graph. There are still2 of16 whole rooted types
closed, and C1.5.b1 remains open with all three arbitrary extras.

## 5. A biconnected component needs at least five exterior-face vertices

Here G is the **entire** selected biconnected positive component,
not a block with external positive attachments. Let L be its loaded
vertices. The established inputs give |L|>=3, all physical boundary
vertices on the unbounded face, and a connected physical noncontact
graph on L. The positive-graph complement on L is therefore connected
as well: every physical noncontact is absent from G.

In a simple biconnected plane graph the unbounded-face boundary is a
simple cycle. Let its length be k. Since L lies on that cycle, k>=3.
If k=3, its vertices are pairwise adjacent in G, so a three-vertex
loaded complement has no edges. If k=4, the complement of its boundary
cycle is two disjoint edges. Every induced subgraph on at least three
of these four vertices is disconnected; additional positive chords
only delete complement edges. Both cases contradict connectedness.
Consequently

\[
                              k\ge5.
\tag{2}
\]

This applies to every selected biconnected component with the stated
load inputs. It does not constrain a small block's exterior face when
additional loaded bodies lie outside that block.

## 6. Every six-body biconnected component has one of two plane domains

For six vertices, (2) leaves k=5 or k=6. If e and f are its edge and
face counts, Euler's formula and the minimum bounded-face length3 give

\[
 6-e+f=2,\qquad 2e\ge k+3(f-1),\qquad e\le15-k.
\tag{3}
\]

The inequality remains valid without assuming any triangular face
contains a physical region with positive area. It is a statement about
the selected simple plane graph; actual square-region routing is a
separate gate.

### 6.1. Exterior hexagon

All six vertices lie on the exterior cycle. Every further edge is an
interior chord, and the chords have a simultaneous noncrossing plane
realization. Thus the complete domain is a six-cycle with a set D of
noncrossing diagonals, with

\[
                              0\le |D|\le3.
\tag{4}
\]

The nine possible labeled diagonals and their noncrossing subsets give
a finite semantic cover. Their actual square poses, circle masks,
contact points, shared means and weights remain continuous variables.
The K4, boundary-contact and clear-degree-two restrictions may remove
subsets, but no diagonal set is discarded merely by drawing a sample
configuration. In particular D empty is the mixed six-cycle family,
which is not covered by the exact five-cycle theorem.

### 6.1a. Exactly nine hexagon graphs, with every necessary load orbit

SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md gives the complete hand
chord count: one zero-chord type, two single-chord types, three
noncrossing two-chord types and three triangulations. Its full load
cover uses only true degree-two/degree-three restrictions, boundary
path-forest and complement connectivity, and the explicit local
unloaded-hub and bypass theorems. A word such as014 denotes the loaded
set {0,1,4}; each entry includes all graph-preserving dihedral images.

| Positive chords | Three loads | Four loads | Five loads |
| --- | --- | --- | --- |
| None | 013,024 | 0123,0124,0134 | 01234 |
| 02 | 014,134,135 | 0134,0135,0145,1345 | 01345 |
| 03 | 014,024,124 | 0124,0125,0134,1245 | 01245 |
| 02,03 | 124,125 | 1234,1235,1245 | 12345 |
| 02,04 | 125,135 | 0135,1235,1245 | 12345 |
| 02,35 | None | 0134,0145 | None |
| 02,03,04 | None | None | 12345 |
| 02,03,35 | None | 1245 | None |
| 02,04,24 | 135 | 0135 | None |

The single-short-chord load family013 is excluded in full: its actual
path3--4--5--0 has two unloaded degree-two transmitters, but body2 is
a unit bypass touching its endpoints. The whole bypass theorem forbids
this reserve. No hub is made degree two by deleting its chord.

The two bare-cycle entries013 and0123 were already excluded by the
long-channel and boundary-path theorems. Thus this table leaves38
necessary whole graph/load orbits, including four for the bare cycle.
It does not assert that any open orbit is realizable. Together with
the five exterior-pentagon domains below, the graph cover consists
of fourteen whole biconnected graph domains. Every open orbit keeps
its full continuous masks, owners, weights and actual means, and all
three extra squares. No whole chorded graph is closed by enumeration.

### 6.2. Exterior pentagon with one interior body

There are five exterior-cycle vertices and one interior vertex H.
Every edge is a cycle edge, an H-spoke, or a chord joining two cycle
vertices. Write h=degree(H) and d for the number of those chords.
Biconnectivity and (3) give

\[
                  2\le h\le5,\qquad 0\le d\le5-h.
\tag{5}
\]

The spokes inherit the cyclic order of their endpoints. Every chord
must admit the same plane embedding with the spokes; equivalently it
lies in one of the closed sectors cut out by the spoke star. This is
a topological constraint, not an assumption that contact edges are
straight segments in the original physical packing.

H is physically circle-clear by the exterior-face input, so its circle
load vanishes. At least one exterior-cycle vertex is physically clear
too: otherwise the five exterior units would form a physical boundary
C5, forbidden by CIRCLE_CONTACT_ANGULAR_ORDER.md. Thus this entire
domain contains at least two physically clear component bodies.

When h=2, H is a genuine zero-load degree-two transmitter. Its two
neighbors cannot physically touch, by the normal-channel theorem; in
particular they are not consecutive pentagon vertices and are not
joined by a positive chord. All nonconsecutive pairs form one pentagon
symmetry orbit. This conclusion does not prescribe a width until the
relevant bypass or channel premises have been supplied.

When h=3, NO_UNLOADED_DIAMOND_HUB.md applies to H. None of its three
neighbors may physically touch both others. Three consecutive pentagon
vertices are therefore forbidden. Among the remaining three-vertex
subsets of a five-cycle, there is one symmetry orbit: exactly one
cycle edge together with an isolated third vertex. Any added chord or
zero-weight contact creating a two-edge path among these three is
also forbidden. This is a full neighbor-pattern restriction at exact
positive degree3, not a theorem about h=4 or h=5.

For h=4 and h=5 retain every hub force and its actual application.
The degree-three hub theorem cannot be applied after deleting one of
these positive spokes. Equations (4)--(5) and these exact degree2/3
restrictions form a complete six-body biconnected domain cover.

### 6.3. Full pentagon chord cover and exact load refinements

Number the exterior pentagon0,1,2,3,4 in order, and retain its actual
interior H. The following is a complete refinement of (5), using
only the already specified plane sectors and exact degree conditions.

If h=2, choose its two nonconsecutive spoke endpoints as0,2. The
short spoke sector has boundary H--0--1--2--H; the long sector has
boundary H--2--3--4--0--H. The only possible outer diagonals inside
these sectors are02,03,24. Diagonal02 is impossible because H is a
clear degree-two transmitter whose neighbors cannot physically touch.
Diagonals03 and24 cross in the long sector and cannot coexist.
Reflection interchanges them. Thus h=2 leaves precisely two
abstract plane domains: d=0, or one of03,24, with all its geometry
still retained. In either domain, the rim vertex1 is a physical
unit bypass for H's channel, so UNIT_BYPASS_NORMAL_CHANNEL.md also
forces H's transmitter reserve to be exactly1.

If h=3, take the allowed spoke set to be{0,1,3}. The only nontrivial
outer diagonals in the spoke sectors are13 and30. Since01 is already
a rim edge, either diagonal would make one of H's three neighbors
touch both other neighbors. NO_UNLOADED_DIAMOND_HUB.md excludes
both possibilities at the actual zero-load degree-three H. Hence
d=0 throughout this entire domain.

If h=4, name the missing-spoke rim vertex4. All spoke sectors except
H--3--4--0--H have only one exterior edge. The only possible outer
diagonal is therefore03. Thus there are initially two domains:
d=0 or the single chord03. If h=5, every spoke sector has only one
rim edge, so d=0. This gives six initial plane domains in total.

**The h=5 domain is excluded.** Every rim vertex has exact positive
degree3: its two cycle neighbors and H. The neighbor H physically
touches both of its other neighbors. The selected zero-load
degree-three theorem therefore forces every rim vertex to be loaded.
All five would physically touch the circle, contradicting their
physical boundary C5. This is a whole-core exclusion, with every
actual mean, physical corner mask and all three extras retained.

**The all-four-spoke-loaded subfamily of h=4,d=0 is excluded.**
Assume here, explicitly, that all four of0,1,2,3 are loaded. Vertex4
cannot physically touch the circle, because that would create a
physical boundary C5. It is therefore a zero-load exact-degree-two
transmitter joining3 and0. The hub H is a unit bypass touching both
endpoints. The complete unit-bypass theorem gives actual applications
p_3,p_0 with

\[
                              |p_3-p_0|=1.
\tag{6}
\]

Their center distances from these actual points are at most1/sqrt(2),
so the triangle inequality gives

\[
                 |c_3-c_0|\le 1+\sqrt2.
\tag{7}
\]

But H and4 are both unloaded, so the four positive rim resultants
sum to zero. The actual path0--1--2--3 meets every hypothesis of
FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md, which gives
|c_3-c_0|>1+sqrt(2). This contradicts (7). Every actual transmitter
mean is included in (6); no positive spoke was discarded.

This implication does not initially force all four spoke vertices
loaded. Only1 and2 have the zero-load degree-three obstruction:
H touches both of their other rim neighbors. At0 and3 the missing
H--4 contact is not available as a premise. This distinction is
necessary for the following exact remaining load cover.

The entire pentagon/interior-body case has five remaining abstract
plane domains:

| Interior degree | Spokes, up to pentagon symmetry | Outer chords | Status |
| --- | --- | --- | --- |
| 2 | 0,2 | None | Whole geometry/completion open; H has reserve1 |
| 2 | 0,2 | One of03,24 | Whole geometry/completion open; H has reserve1 |
| 3 | 0,1,3 | None | Whole geometry/completion open |
| 4 | 0,1,2,3 | None | Whole geometry/completion open; the all-four-spoke-loaded subfamily is excluded |
| 4 | 0,1,2,3 | 03 | Whole geometry/completion open |

In the last row H has four positive spokes; vertices0 and3 have
degree4. A degree-three obstruction cannot be applied to any of
those vertices by dropping its fourth force.

### 6.3a. Every necessary load orbit of the five pentagon graphs

SIX_BODY_INNER_PENTAGON_LOAD_COVER.md now refines all five surviving
graph domains by hand. Its full table includes every graph-preserving
dihedral image and every original physical feature/mean domain:

| H spokes | Outer chord | Three loads | Four loads |
| --- | --- | --- | --- |
| 0,2 | None | 013,023,134 | 1234,0124 |
| 0,2 | 03 | 124,134 | 1234,0124 |
| 0,1,3 | None | 013,023,024 | 1234,0134,0124 |
| 0,1,2,3 | None | 124 | 0124 |
| 0,1,2,3 | 03 | 124 | 0124 |

The complete two-spoke/no-chord load family0234 is excluded. H has
actual reserve1 by its unit bypass1, so its loaded endpoints0,2
have center separation at most1+sqrt(2). The same four actual loaded
bodies form the balanced boundary path2--3--4--0, whose endpoints
must be more than1+sqrt(2) apart. No endpoint force is deleted.

The entire two-spoke/chord03 family024 is now excluded as well:
H and1 are two true unloaded transmitters between0,2, while3 is
a third physical bypass through03 and23. The new radius-free local
theorem retains the bypass's actual degree-three equation and all
other forces. The table retains nineteen whole necessary graph/load
orbits. It does
not assert any is realizable or close a graph by enumeration. The
previous physical H--4 noncontact remains specific to the four-spoke
no-chord domain. All actual hub degrees, means and three extra units
remain. Together with Section6.1a this completes the necessary load
roadmap for all fourteen biconnected graph domains.

### 6.4. Complete necessary load masks before adding chords

For the exterior-hexagon domain, first ignore its additional positive
chords. Removing edges only enlarges the positive-graph complement.
The loaded complement must already be connected for the bare cycle.
Thus the following list is an exhaustive necessary load-mask cover;
chords and zero-weight physical contacts may prune it further.

With three loads, a graph on those three vertices has connected
complement exactly when it has at most one edge. On a six-cycle the
three-load possibilities up to dihedral symmetry are therefore the
alternating mask{0,2,4}, or the one-edge mask{0,1,3}. Indeed the
three positive cyclic gaps between the loaded vertices sum to6.
Their unordered patterns are (1,1,4), (1,2,3), or (2,2,2);
the first has two cycle edges and is excluded. For three marks,
rotation and reflection identify all permutations of these gaps.

With four loads, the two zero-load positions have cyclic distance
1,2, or3. Each is allowed by the bare-cycle complement test: the
induced positive graph is respectively a four-vertex path, a
three-vertex path plus an isolated vertex, or two disjoint edges.
Their complements are respectively a four-vertex path, a graph with
a universal vertex, or a four-cycle, hence connected.
With five loads there is one zero-load position, one orbit; the
complement of the induced five-vertex path is connected. For example
its vertex1 is joined in the complement to3,4,5, and vertex2 is
joined to4. Six loads would give a forbidden physical boundary C6.

There are therefore exactly six necessary bare-hexagon load orbits:
two three-load, three four-load, and one five-load orbit. A zero-load
vertex is not declared physically clear unless a separate geometric
input forces that conclusion. At least one vertex of the six-cycle
is physically clear, because all six on the circle would give C6.

For the exterior pentagon with clear H, all loads lie among its five
rim vertices. The same bare-cycle complement argument as the C5
component gives exactly one three-load orbit (one rim edge, with
the two zero-load rim vertices nonconsecutive) or one four-load
orbit. Five loads would be a physical boundary C5. Spokes and the
allowed chord of Section6.3 retain their full additional forces;
these load masks do not license an application of the exact C5
component exclusion to the augmented graph.

For h=4,d=0, the forced loads1,2 make the three-load mask exactly
{1,2,4}. Adding0 or3 instead of4 would give two positive rim edges
among three loads, whose complement is disconnected. With four loads,
the zero-load rim position can only be0,3, or4; positions1 and2 are
already loaded. The last alternative is the entire subfamily excluded
in Section6.3. The first two are reflection partners. Hence every
surviving h=4,d=0 component has vertex4 loaded, and its full load cover is
{1,2,4} or {0,1,2,4}, up to reflection exchanging0 and3.

Moreover H and4 are physically disjoint in this surviving domain.
If both0 and3 physically touched the circle, all five rim bodies would
be on the circle, which is impossible. At least one endpoint, say0,
is physically clear and unloaded. Its exact positive neighbors are
H,1,4. H already touches1. If H also physically touched4, the
selected zero-load degree-three theorem at0 would give a contradiction.
Thus H has no physical contact with4, including a zero-weight one.
The reflected argument applies when3 is the clear endpoint.

For h=4,d=1, the added chord03 makes4 a degree-two triangle tip,
so it is loaded. Vertices1,2 are loaded as before. At most one of0,3
can physically touch the circle because they and4 form a physical
triangle. The same two necessary positive load orbits consequently
remain: {1,2,4} or {0,1,2,4}, up to reflection. The degree-four hub
and degree-four chord endpoints keep all their forces. The physical
H--4 noncontact conclusion from d=0 is not asserted in this domain.

These finite labeled graph, embedding and load choices still quantify
over all actual physical circle masks, corner weights and continuous
poses. They do not constitute a finite numerical configuration list.

### 6.5. Actual completion regions for every remaining simple C6

SIMPLE_CYCLE_CHANNEL_POCKET_CAPS.md proves each exterior channel
region lies in the actual outward cap D_R intersect {y>=h}, where
h>0 is the actual channel height. Its proof uses occupied endpoint-
to-circle-corner segments and the original channel segment. Every
physical circle mask has a facing corner of height at least h;
actual circle order supplies the correct outer arc. The argument
retains every genuine shared mean and weak contact junction.

The whole bounded free region of the physical six-body ring has
area at most3sqrt(3)/2<3, including all its free components. Thus
it holds at most two of the three extras. Every remaining exact
simple C6 requires at least one extra in a proved outward cap, with
center height at least h+1/2. Alternating three loads have three such
caps; each four-load separated-zero orbit has two; five loads have
one. Direct boundary-pair pockets and two-corner outer caps hold no
extra. Additional physical contacts only subdivide these regions.

This is a complete localization theorem. A joint capacity bound for
the caps and central region remains open for all four whole C6 load
orbits. No extra is assumed to lie in the concurrence polygon, and
no positive chord is dropped to apply the simple-cycle theorem.

### 6.8. The whole unique-corner, one-diagonal central region

SIX_CYCLE_ONE_DIAGONAL_INNER_CAPACITY.md strengthens the central
capacity for the complete alternating three-load family with exactly
one diagonal transmitter and three physical unique circle corners.
Every original shared-side mean is retained. Its full port/turn cover
proves each loaded turn is at most135 degrees, with equality forcing
the actual concurrence to be its circle corner. Both diagonal-end
turns are strictly between90 and135 degrees.

The exact six actual contact points give a polygon of area<5/2.
The diagonal transmitter occupies its actual inward half, of area1/2.
The full bounded central free union consequently has area<2, including
weak-limit components. It holds at most one extra, so at least two
of the three extras must lie in the actual exterior channel caps.
Root and independent full audits passed the complete region theorem.
This does not exclude a whole positive core, close the one-diagonal
width class, or extend to a physical two-corner endpoint by a limit.

## 7. Two triangle blocks and one bridge: exactly three layouts

If the triangles share an articulation A, their union has five
vertices. The sixth vertex is a bridge leaf, attached either to A
or to one of the four symmetry-equivalent tips. These are two layouts.
If the triangles are disjoint, they already use six vertices and their
single bridge joins one vertex of each. Triangle symmetries give one
such layout. There is no third relation between distinct blocks:
blocks intersect in at most one vertex, and the block incidence graph
is a tree.

The shared-A-plus-leaf layout is excluded by
ONE_ARTICULATION_TRIANGLE_LEAF_EXCLUSION.md. The entire disjoint
triangles joined by a bridge is now excluded by
OUTER_BRIDGED_TRIANGLE_CAP_EXCLUSION.md. Its stronger sign is at the
actual radial bridge application: each true end triangle requires
p dot M_tips<0. Reversing the common bridge produces an outward
endpoint and a contradiction, including p=0. The two different
articulation-center pressure signs alone were not sufficient.

Only the entire tip-attached bowtie-leaf layout remains. Its former
tip has degree3 and its shared articulation degree4. Neither can be
replaced by an unchanged degree2 tip or the new exact-degree3
one-bridge end-triangle root. TIP_LEAF_BOWTIE_D_EXCLUSION.md now excludes the entire D-leaf type,
through its complete parallel and nonparallel articulation proofs.
The entire aligned S-leaf type is now excluded by
TIP_LEAF_BOWTIE_S_ALIGNED_NONPARALLEL_EXCLUSION.md and
TIP_LEAF_BOWTIE_S_ALIGNED_PARALLEL_EXCLUSION.md. The nonparallel
proof exhausts the preselected left-vertex owners and all physical
B masks, then routes both true C/E petal ports to one high H side.
The parallel proof keeps both actual wall means. Proper B concurrence,
the true degree-four H equation and end-triangle pressure determine
the complete M sector. Its tilted-H alternative uses the exact petal
torque to reach support>39/40; its aligned-H alternative uses the
full all-frame boundary-wall bottom>1/2 theorem. All critical zero
coordinates and shared means are included.

END_TRIANGLE_HIGH_FACE_EXCLUSION.md proves the uniform all-mask
contradiction when both actual end-triangle ports share a root side
of height at least39/40. The quantitative companion
END_TRIANGLE_FACE_RESULTANT_ANGLE.md gives Mhat.N>1/2 at side height
at least4/5 and Mhat.N>4/5 at height at least29/30. These statements
retain arbitrary additional root forces. Root and independent full
audits passed both aligned proofs and both local tools.

Only the whole tilted S-leaf articulation remains in this last
layout. All B/H owner and frame alternatives, physical circle masks,
actual means, root force equations and all three extras remain.
C2.33.b1 is still open with two of its three full layouts closed.

## 8. A triangle and a four-body block: three layouts, two remaining

With no bridges, the two blocks share exactly one articulation.
The four-body block is C4, diamond or K4. K4 is globally excluded.
The C4 articulation has one vertex orbit. The diamond articulation
is a hub or a tip, giving two more. Thus there are three abstract layouts.
ROOTED_BLOCK_ATTACHMENT_OBSTRUCTIONS.md excludes the entire diamond-tip
articulation layout: the unchanged hubs and other tip would be a loaded
physical triangle. The C4 and diamond-hub layouts remain open.

The triangle's two nonarticulation vertices have exact positive
degree2 and are loaded, so its whole end-triangle pressure is available
at the shared articulation. The four-body block retains the resulting
additional interface force and all its actual body equations. An
isolated four-body-component exclusion cannot silently remove this
force.

### 8.1. Exactly four remaining whole graph/load orbits

TRIANGLE_FOUR_BODY_BLOCK_LOAD_COVER.md proves the full necessary
load refinement. Label the C4 H--A--B--C--H and the attached triangle
H--X--Y--H. H is physically clear; X,Y are loaded true degree-two tips.
The whole one-adjacent-block-load family has a positive normal channel
whose endpoints actually touch, an immediate contradiction.

In the one-opposite-block-load family B, the two true unloaded
transmitters align both endpoints and have reserve1. B's genuine
degree-two equation forces the actual radial S unit with equal circle
weights. The complete other petal then has M=-F_B along H's side axis,
whose support is2-d>59/60. END_TRIANGLE_AXIS_RESULTANT_SUPPORT_BOUND.md
proves both petal ports are on that maximizing side and gives the
contradictory strict bound<59/60. H retains all four forces.

The exact remaining C4 block-load representatives areAB,AC,ABC.
Both two-load cases have a single actual side transmitter, proved by
their real unit bypass. For the diamond rooted at hub H, the sole
block-load set isKAB; its other hub K has true degree3 and is forced
loaded, while H retains degree5. The diamond-tip layout stays closed.

Root and independent full audits passed the load table, both entire
single-load exits and the uniform axis-resultant theorem. The four
remaining graph/load orbits require a whole contradiction, sharp bound
or complete joint three-extra exit. One of three whole attachment
layouts is closed; C2.34.b0 remains open.

## 9. Complete local and load-family exits beyond the initial cover

UNLOADED_TRIANGLE_HUB_EXTERNAL_SEPARATION.md has a full source-by-source
scope audit: unloaded exact-degree3 A,D, their exact-degree2 common roof
T, and external positive neighbors B,C force the latter to be physically
closed-disjoint. T is automatically loaded. B,C may have arbitrary
additional forces, loads or physical circle masks, and their forbidden
contact may have zero multiplier. All such local motifs are prelisted
before extracting the common certificate.

SIX_BODY_MIDDLE_MOTIF_CONSEQUENCES.md gives exactly four six-body positive
graphs with distinct external neighbors under those exact local degrees.
Only two receive new whole positive-load-family exits: a house block
with a lower-vertex leaf cannot have both house hubs unloaded, and a
hexagon with opposite triangular ears cannot have only three loads.
For the latter, in the exterior labeling with chords02,35, the complete
remaining four-load masks are{0,1,4,5} and{0,1,3,4}. Both remain open.
The other two graphs, a two-root chain/leaf triangle and a one-ear
hexagon, gain full physical BC noncontact but no graph exclusion.

BOUNDARY_THREE_EDGE_PATH_DIAMETER.md proves endpoint-center distance<3
for every physical three-edge path of four boundary units. The full
scope audit uses Sections1–5 of the earlier seven-cycle metric theorem;
no seventh body enters. A normal channel with at least two exact unloaded
transmitters requires distance>=3, so the complete four-load C6 orbit
with adjacent zero-load vertices is excluded. Endpoint degrees and loads
are unrestricted in this stronger local channel obstruction.

SIX_CYCLE_THREE_LOAD_LONG_CHANNEL_EXCLUSION.md excludes the full simple
C6 orbit with positive-load gaps(1,2,3). Its exact long reserve gives
R²>=17/4 and a narrow endpoint-center cap. The isolated parallel load
is completely handled before proper concurrence is used. Both short
transmitter widths, every physical mask and all actual means then have
uniform strict distance/radius contradictions. All three extras remain.

Consequently the complete simple C6 residual is exactly:

| Positive-load orbit | Whole remaining scope |
| --- | --- |
| Three alternating loads | Three single-transmitter channels, with zero or one diagonal; every remaining physical corner mask and mean |
| Four loads, zero vertices at distance2 | The isolated loaded body and both genuine channels, all means |
| Four loads, opposite zero vertices | Both boundary pairs and both full channel-width alternatives |
| Five loads | One full transmitter and the whole loaded boundary path |

SIMPLE_CYCLE_LOADED_FORCES_NONPARALLEL.md now excludes parallel pair
forces at every loaded body of every exact simple positive cycle with
at least three loads. The direct, one-side, diagonal and two-transmitter
channel alternatives are all covered, including isolated loads. Proper
radial concurrence is therefore available for every loaded vertex in
the four remaining C6 orbits. Physical two-corner concurrences are not
asserted bounded; all actual means and individual zero weights remain.

SIX_CYCLE_ALTERNATING_DOUBLE_DIAGONAL_EXCLUSION.md excludes the entire
alternating-three-load width class with at least two diagonal
transmitters. Their endpoint side ownership forces one common loaded
frame and two perpendicular channels. A third diagonal is impossible;
the full remaining side-channel case gives a,b>1/3 and an exact
increasing circle-radius lower bound f(a+b)>f(5/4)>Q. Every physical
two-corner endpoint and transverse mean is retained. The zero-/one-
diagonal classes and the whole alternating-load parent remain open.

SIMPLE_CYCLE_CONVEX_FORCE_POLYGON.md now proves that every exact
simple positive cycle with at least three loads has a strictly convex
polygon of its proper loaded concurrences, with the origin strictly
inside. The actual exterior spokes prove the one-winding order; the
common moment is nonzero; all contracted channel reserves remain.
Physical radial concurrences may still lie outside their squares.
The theorem also supplies the complete local direct-edge and one-
transmitter angular bounds, without claiming completion localization.

SIX_CYCLE_ALTERNATING_UNIQUE_SINGLETON_EXCLUSION.md excludes the entire
all-side-transmitter alternating family when each loaded square has
one physical circle corner and all six loaded/transmitter contacts
are singletons. The full feature and equality cover forces adjacent
inner ports, turns in[90,135]degrees and a constant circle-corner choice.
Actual channel closure makes a convex six-point distance sum minimal.
TRIANGLE_SQUARE_CORNER_FERMAT_BOUND.md then gives
R<79/40, contradicting the window. Its exact uniform constant is
(1+sqrt(4+sqrt(3)))/sqrt(3)<79/40; the proof covers all triangle shapes.

The remaining all-side family has at least one genuine shared side
or one physical two-corner loaded mask. Both are full open features:
a shared side can shorten the actual port chord below1, and a radial
concurrence need not lie inside its square. Neither is included by
an unsupported limiting argument. Exactly one diagonal is the other
full alternating width alternative still open.

Positive chords retain their extra force equations and are not covered
by an exact simple-cycle proof. The complete chord/load cover in
Section6.1a records the additional whole short-chord bypass exit.
Every other listed full chord/load family remains open.

LONG_CHANNEL_ENDPOINT_MATCHING.md independently proves that the graph
of all actual center pairs at distance>=3 is a matching. A body cannot
be the endpoint of two long normal channels to distinct other bodies.
This applies at arbitrary endpoint degrees and without circle-load
premises. Two channels with the same endpoints are not excluded. In a
simple cycle with three loads it permits at most four unloaded bodies,
excluding every such cycle on at least eight bodies. The seven-body
three-load run pattern(2,1,1) remains; the alternating six-body pattern
is one of the open rows above.

Finally TRIANGLE_THREE_BRIDGES_LONG_CHAIN_EXCLUSION.md closes the entire
first triangle/three-bridge attachment. It first proves the complete
load cover using the local all-bridge radial law, then retains both
leaf types and both transmitter widths. The root lies in a narrow western
center cap, while the two actual boundary-tip resultants sum west.
The full center-angle rectangle forces the touching tips to opposite
sides with gap>2acos(4/5)>acos(9/25), a contradiction. The later fork, double-leaf-root and distinct-arm exits bring the
current total to seven of seven closed; the complete whole-cell
assembly and both critical completion exits are specified in Section2.

Root and separate independent full audits passed all six sources above,
including every enlarged degree, physical-contact and selection scope.
These are complete whole-domain exits and uniform local restrictions,
not numerical graph or pose samples. None closes an entire six-body
coarse row on its own.

### 9.1. Uniform triangle support and radial-aggregate structure

END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md proves h_A(M/|M|)<d for
any physical positive triangle whose two tips have exact degree two
and positive circle load. The root A may carry arbitrary additional
forces. Its proof retains every physical corner mask and actual
application mean; it does not replace the tip pair by one leaf.

Its purely physical proper-port lemma also feeds
RADIAL_TRIANGLE_CONCURRENCE.md. For any pairwise-touching triangle with
three genuine noncollinear radial external aggregates summing to zero
and nonzero common cycle moment, every nonparallel root has a strictly
positive radial concurrence. The exact parallel-root alternative uses
its two original opposite-sign wall means. The zero-moment case remains
an explicit application obligation, fulfilled separately by the complete
distinct-arm proof. Root and independent full audits passed all eight
sources introduced in this checkpoint.

### 9.2. The entire D-leaf tip-attached bowtie alternative

TIP_LEAF_BOWTIE_D_EXCLUSION.md combines two complete source proofs.
In the nonparallel articulation, the simultaneous A-star selection
uses its three true forces and allows arbitrary degree at H. Every
BH side-axis owner, actual shared mean and physical radial free
alternative is excluded by a full scalar projection or torque bound.
The exact bounds exceed37/35 or sqrt(6/5), contrary to the strict
end-triangle support h_H(Mhat)<d for the untouched C,E petal.

In the parallel articulation, B,H share their actual supporting
wall. This supplies nonparallel B forces without a boundary-neighbor
assumption. Pure physical triangle ports and H's actual degree-four
torque put the full petal resultant in a controlled sector. Every H
frame then has support at least2sqrt(1+sqrt(2)-R)>2/sqrt(3)>d.
Both full source audits and the complete assembly audit passed.
All three extras remain, and the S-leaf alternative remains open.

## 10. Exact exit contracts and status

Each listed layout must retain the original square containment and
nonoverlap conditions, the full physical touching graph, every actual
circle mask and zero corner weight, the compatible pre-stress normal
choices, every positive body force and torque, and all three extras.
Separate physical holes require an actual barrier proof; face labels
in the plane graph are not sufficient on their own.

The next mathematical exit is a whole-core contradiction, a sharp
radius inequality, or a joint capacity of at most two extras over the
entire relevant continuous domain. Any surviving case at Q must pass
its exact necessity and sufficiency conditions to the equality gate.

The two original common-articulation layouts and the complete length-three
chain are excluded. Section6.3 excludes the entire five-spoke pentagon
domain and one complete four-spoke load subfamily. Section9 records
the additional whole simple-cycle and local-motif load-family exits.
**C1.3.b3 is CLOSED hand; the other five six-body coarse rows remain
open.** All five-body cells are closed, and six remains the first
unresolved size. The authoritative count is eight whole cells closed
and50 open. No numerical graph enumeration,
angle grid, Lean compilation or CI is a premise of this cover.
