# The entire five-body biconnected cell reduces to three graph families

**Status: complete hand graph and load reduction; independent hand audit passed.** For the selected positive five-body biconnected component in the declared radius window, the only surviving positive graphs are:

1. the five-cycle C5;
2. the house graph: a four-cycle with a triangular roof on one edge;
3. the fan over a four-vertex path: one vertex joined to all four path vertices.

All physical circle/load masks and all four completion squares remain. This is an exhaustive reduction of C1.5.b0, not its sharp metric or completion theorem. No numerical graph or pose search is a premise of the proof below.

## 1. Inputs and the positive-graph complement

Let G be the simple positive body graph. It is biconnected on five vertices, planar in the selected physical embedding, and has at least three loaded vertices. All physically circle-touching vertices lie on its unbounded face.

Write L for the set of positive circle-loaded bodies. The physical noncontact graph on L is connected, by ACUTE_LOADED_CONTACT_GRAPH.md and the subsequent global reductions. Every positive edge is an actual physical contact. Therefore the physical noncontact graph is a subgraph of the graph complement \(\overline G[L]\), and

\[
                |L|\ge3,\qquad \overline G[L]\text{ is connected}.
\tag{1}
\]

In particular L lies in a single connected component of \(\overline G\). This implication only enlarges the noncontact graph; it never identifies a missing positive edge with a physical noncontact.

We also use:

- NO_POSITIVE_K4_SUBGRAPH.md: G contains no K4.
- NO_THREE_BOUNDARY_COMMON_NEIGHBORS.md: two body vertices cannot have three common positive neighbors all touching the circle.
- Every positive degree-two triangle vertex is loaded, because a clear degree-two transmitter cannot have physically touching neighbors.
- Three physically circle-touching bodies cannot form a physical triangle; a boundary body has at most two boundary-touching neighbors.

## 2. Exhaustive hand classification by the number of edges

Biconnectivity implies minimum degree at least two, so G has at least five edges. There are ten possible pairs. Its complement has maximum degree at most two whenever all original degrees are at least two. These elementary facts give the complete classification below.

### 2.1. Five edges

The degree sum is ten. Every degree is at least two, hence every degree equals two. Connectivity makes G exactly C5.

### 2.2. Six edges

The complement has four edges and maximum degree at most two. A graph of maximum degree two is a disjoint union of paths and cycles. On five vertices with four edges, the only possibilities are

\[
 P_5,\qquad C_4\sqcup K_1,\qquad K_3\sqcup K_2.
\]

Indeed, an acyclic graph with five vertices and four edges is a connected tree, and maximum degree two makes it P5. If there is a cycle, it has length three or four; the remaining single edge in the three-cycle case must join the two remaining vertices because an attachment to the triangle would create degree three.

The complements are respectively the house graph, two triangles sharing one articulation, and K2,3. The middle graph is not biconnected and is discarded. Thus the biconnected possibilities are exactly the house and K2,3.

### 2.3. Seven edges

The complement has three edges and maximum degree at most two. The only possibilities are

\[
 K_3\sqcup2K_1,\qquad P_4\sqcup K_1,\qquad P_3\sqcup K_2.
\]

If it has a cycle it is the displayed triangle. Otherwise it is a path forest with two components, whose nontrivial size partitions are 4+1 or 3+2; a matching of three edges would require six vertices.

The complements are:

- the book graph consisting of a common hub edge and three common degree-two neighbors;
- the fan over a four-vertex path;
- K4 with one edge subdivided once.

All three are biconnected. These are the complete seven-edge possibilities.

### 2.4. Eight, nine or ten edges

At eight edges the complement consists of either two adjacent edges or two disjoint edges. In the adjacent case it is P3 plus two isolated vertices; the two path endpoints and the two isolated vertices form a K4 in G. In the disjoint case G is the four-rim wheel: a universal hub joined to a four-cycle.

At nine edges, omitting one endpoint of the sole missing edge leaves a K4. At ten edges G is K5 and contains K4. The K4 theorem therefore excludes the adjacent-missing-edge case and all nine-/ten-edge cases.

This gives ten abstract biconnected isomorphism types in total: one with five edges, two with six, three with seven, two with eight, one with nine and one with ten. Their enumeration above is a hand proof from the complement degree bound.

## 3. Exclude the remaining nonlisted graphs uniformly

### 3.1. The wheel is impossible by load connectivity

The complement of the four-rim wheel is two disjoint edges and one isolated vertex. Every component has at most two vertices. Equation (1) has no solution, since at least three loaded vertices must lie in one connected complement component. Thus the entire wheel graph is excluded, for every physical load mask and completion.

### 3.2. K2,3 and the book graph are impossible

For K2,3, the complement is K3 disjoint from K2. Equation (1) forces L to be exactly the three-vertex part of the original bipartition. Those three loaded bodies all physically touch the circle and have the two vertices in the other part as common positive neighbors. NO_THREE_BOUNDARY_COMMON_NEIGHBORS.md gives a contradiction.

For the book graph, the complement is K3 and two isolated vertices. Again the three degree-two page vertices are exactly the possible loaded set from (1). They have the two hubs as common positive neighbors, giving the same contradiction. The extra edge between the hubs does not evade the subgraph obstruction.

### 3.3. The subdivided K4 is impossible

Label the complement as the path b--a--c and the disjoint edge d--e. Equation (1) forces

\[
                         L=\{a,b,c\}.
\]

In G both d and e are adjacent to all three of a,b,c. Thus the three loaded boundary bodies have two common positive neighbors, once more contradicting NO_THREE_BOUNDARY_COMMON_NEIGHBORS.md. The positive edge b--c is harmless to this subgraph argument.

Combining Sections 2--3 leaves exactly C5, the house and the four-path fan. These are surviving semantic families; the statement does not claim every allowed mask or pose is physically realizable.

## 4. Exact necessary loaded-set covers in the three surviving graphs

Additional zero-stress physical contacts may prune these covers further. None is discarded from the actual completion problem.

### 4.1. C5

The complement of C5 is another five-cycle. With exactly three loaded vertices, connectivity in (1) makes their induced complement a three-vertex path. Equivalently they have exactly one positive edge among them in G, and the two unloaded vertices are nonadjacent in G. All such patterns are one dihedral orbit.

With four loaded vertices there is one unloaded vertex, again one orbit. Five loaded vertices would make all five bodies physically circle-touching, contradicting the theorem that an all-boundary positive component is C7. Thus the full necessary positive-load cover is exactly these three-load and four-load patterns. Physical circle contacts with zero multiplier remain separate labels.

The subsequent FIVE_CYCLE_POSITIVE_COMPONENT_EXCLUSION.md closes both
complete load orbits. Its full three-load angle-sum and four-load
endpoint-separation proofs retain every physical mask, actual mean and
all four extras. The domain, both orbits and assembly passed root and
separate independent full hand audits. No C5 component remains.

### 4.2. The house graph

Label its complement as the path

\[
                         1--2--3--4--5.
\]

In G, vertex3 is the degree-two roof vertex, with touching neighbors1 and5, so3 is loaded. Equation (1) makes every possible loaded set a consecutive interval of this complement path. With at least three loads, the possibilities are

\[
 \{1,2,3\},\quad\{2,3,4\},\quad\{3,4,5\},
 \quad\{1,2,3,4\},\quad\{2,3,4,5\}.
\]

The five-vertex interval is excluded because1,3,5 form a physical triangle and cannot all touch the circle. Reflection identifies the first and third masks and the two four-load masks; the middle triple is separate. All five labeled masks are retained in the cover.

HOUSE_HOLE_EMPTY.md subsequently proves that every house load mask has empty triangular and quadrilateral holes; all four completion squares are exterior. The key cross obstruction uses an unloaded exact degree-three hub and does not restrict the roof's contact owner. RADIAL_BOUNDARY_NEIGHBOR_PRESSURE.md, Section3, also excludes the complete all-radial physical mask in either end triple: the opposite clear hub touches all three loads. The middle and four-load physical masks are not removed by that corollary.

### 4.3. The fan over a four-vertex path

Write its path as u1--u2--u3--u4 and its universal hub as H. Vertices u1 and u4 are positive degree-two triangle tips and therefore loaded. The hub is not loaded: in the positive-graph complement it is isolated, incompatible with (1). In fact it is physically circle-clear, because it positively touches at least three loaded boundary bodies while a boundary body has at most two boundary neighbors.

The complement on the four path vertices is the path

\[
                       u3--u1--u4--u2.
\]

The complete necessary loaded-set list is therefore

\[
 \{u1,u2,u4\},\qquad\{u1,u3,u4\},
 \qquad\{u1,u2,u3,u4\}.
\]

The two triples are exchanged by reversing the original path. The two inner path vertices retain their possible zero-weight physical circle contacts wherever geometry allows them.

The subsequent NO_UNLOADED_DIAMOND_HUB.md, Section6, excludes both entire three-load masks. Each inner path vertex has exact positive degree3, and its universal-hub neighbor physically touches both other path neighbors. The radius-free selected-star theorem therefore forces both inner path vertices to carry positive circle load. Thus every surviving fan now has **all four path vertices loaded**, with H physically circle-clear. RADIAL_BOUNDARY_NEIGHBOR_PRESSURE.md, Section3, further excludes the all-radial physical mask, so at least one path vertex has a unique physical circle corner. The earlier three-mask list remains the exhaustive combinatorial cover before this geometric refinement.

### 4.4. Subsequent whole house/fan restrictions

FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md proves that a balanced
four-body boundary path has endpoint center distance>1+sqrt(2).
Every pair of actual endpoint applications on a common hub has
distance>1, including all shared means. It applies to the four-load
fan and to house path3--1--4--2 with hub5. Two endpoint hub vertices
must therefore be opposite. The later fan assembly closes its full feature
cover; the house retains its separate true three-spoke equations.

HOUSE_END_TRIPLE_PARALLEL_BYPASS_EXCLUSION.md excludes every end-triple
house whose clear bypass shares its transmitter's frame. Both point
and shared hub contacts, every actual mean and both endpoint circle
masks are covered. The genuinely tilted bypass remains.
HOUSE_MIDDLE_TRIPLE_SHARED_HUB_EXCLUSION.md excludes every middle-triple
hub force owned by both clear hubs, including all shared hub sides,
by strict support separation of its lower endpoint pair. Singleton
one-owner and free-hub contacts remain. Root and separate full audits
passed all three sources. These are subfamily/domain conclusions,
not by themselves a closure of the house or C1.5.b0. The complete fan
closure is supplied separately below.

### 4.5. Full fan endpoint owner cover and further house domains

FAN_ENDPOINT_OWNER_REDUCTION.md now proves exactly one fan endpoint
normal is H-owned. FAN_HUB_OWNED_ENDPOINT_EXCLUSION.md excludes both
H-owned axes; FAN_NON_HUB_OWNED_ENDPOINT_EXCLUSION.md excludes every
pair with neither H-owned, including unique-free/shared and radial-free
masks. The exact remaining families are the mixed tip-owned,
unique-free/shared, and physical radial-free endpoint domains, each
with its entire H-side mean and all four extras. The subsequent
FAN_MIXED_TIP_ENDPOINT_EXCLUSION.md,
FAN_UNIQUE_FREE_SHARED_ENDPOINT_EXCLUSION.md and
FAN_HUB_OWNED_RADIAL_FREE_ENDPOINT_EXCLUSION.md now exclude all three.
FOUR_LOAD_FAN_EXCLUSION.md combines the full cover and all positive
load masks to close the entire fan graph. Root and separate independent
full audits passed every source and the assembly.

THREE_BOUNDARY_PATH_RESULTANT_CONE.md gives the whole positive-cone
identity and excludes the all-radial hub-neighbor mask of house4,
as well as a fan's sole-internal-unique mask.
HOUSE_FOUR_LOAD_TIP_OWNED_ENDPOINT_EXCLUSION.md closes the house's
two-tip-owned endpoint family using only its three actual hub forces.
HOUSE_END_TRIPLE_TILTED_BYPASS_DOMAIN.md retains both tilt signs while
making its endpoint/bypass contacts singleton and excluding two
bypass-owned endpoint normals.
HOUSE_MIDDLE_TRIPLE_UNIQUE_FREE_HUB_SELECTION.md removes free AD only
in the full all-physical-unique mask, without fixing any shared mean.
Every radial and one-owner middle-triple alternative remains explicit.
Root and separate full audits passed all eight source implications.

## 5. Exact remaining whole-cell work

**Theorem 5.1.** Under the stated selected-certificate inputs, every five-body biconnected positive component belongs to one of the three graph families in Section 4, with one of its stated necessary load masks. The seven other abstract biconnected graph types are completely excluded, and no completion square is discarded.

The subsequent complete C5 and fan assemblies exclude the eighth and
ninth of the ten graph types. Every surviving five-body biconnected
component is therefore a house in one of its three load-mask orbits.
Its full contact owners, actual means, physical masks, zero-weight
contacts and four extras remain. A C5 or fan subgraph with extra positive
edges does not inherit either exact-component theorem.

C1.5.b0 remains OPEN until the whole house family is excluded or receives
a full sharp completion theorem. The current coarse count is six closed
and52 open. The house holes are empty, but its joint exterior bound
remains open. No Lean compilation or CI was run.
