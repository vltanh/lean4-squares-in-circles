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

| Coarse row | Cyclic blocks | Bridges | All remaining physical squares |
| --- | --- | ---: | ---: |
| C1.3.b3 | One triangle | 3 | 3 |
| C1.4.b2 | One four-body block | 2 | 3 |
| C1.5.b1 | One five-body block | 1 | 3 |
| C1.6.b0 | One six-body block | 0 | 3 |
| C2.33.b1 | Two triangles | 1 | 3 |
| C2.34.b0 | A triangle and a four-body block | 0 | 3 |

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
force. Thus three of the seven whole layouts are closed and four remain:
the fork, mixed arms at one root, a two-edge arm plus a different-root
leaf, and one leaf at every triangle vertex. These four retain their
whole load, contact and completion domains. In particular an internal vertex of an attached tree is not
assigned a radial-leaf formula merely because its edges are bridges.
The exact degree-one S/D law applies at an actual leaf; any broader
terminal or transmission reduction must establish its own premises.

For each surviving layout, the full next gate is to combine the radial
bridge cut equations, the physical central bridge cover, the actual
cyclic-body equations and the three-extra joint completion problem.
Removing the three leaf squares from its occupied geometry is not an
allowed reduction.

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
ONE_ARTICULATION_TRIANGLE_LEAF_EXCLUSION.md. The other two remain.
For a leaf at a former bowtie tip, that body's degree is3, so the
bowtie pressure theorem cannot treat it as an unchanged degree2 tip.
For two disjoint triangles joined by a bridge, each triangle has two
true degree2 tips, so its separate end-triangle pressure implication
does apply at its own articulation. The articulations are different;
their two positive projections are not projections onto one common
center and do not by themselves contradict bridge balance.

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
| Three alternating loads | Three single-transmitter channels; every width and physical corner mask |
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

Positive chords retain their extra force equations and are not covered
by an exact simple-cycle proof. All chord/load combinations remain in
their full graph gates except the explicit opposite-ear three-load exit.

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
sides with gap>2acos(4/5)>acos(9/25), a contradiction. Thus exactly
two of the seven triangle/three-bridge layouts are now closed; five remain.

Root and separate independent full audits passed all six sources above,
including every enlarged degree, physical-contact and selection scope.
These are complete whole-domain exits and uniform local restrictions,
not numerical graph or pose samples. None closes an entire six-body
coarse row on its own.

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
**All six coarse six-body rows remain open.** All five-body cells are now
closed, so six is the first unresolved size. The authoritative count is
seven whole cells closed and51 open. No numerical graph enumeration,
angle grid, Lean compilation or CI is a premise of this cover.
