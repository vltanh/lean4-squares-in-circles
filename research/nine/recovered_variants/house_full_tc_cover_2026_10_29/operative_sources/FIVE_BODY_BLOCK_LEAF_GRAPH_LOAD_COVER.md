# Every rooted five-body block with one leaf: complete necessary load domains

**Status: complete hand graph/load cover and whole load-family exits;
root and separate independent full hand audits passed.**
Use the common selected certificate in
79/40 <= R <= sqrt(1105)/16. The exact six-body positive graph consists
of a biconnected five-body block and one genuine radial leaf L at its
root R. The three other physical squares remain fixed and arbitrary.

The root R is physically circle-clear by the radial bridge endpoint
theorem. L is positively loaded, with its full S or D geometry. The
positive component has at least three noncollinear loaded bodies, so
at least two block vertices other than R are loaded. The table below
lists only the loaded block vertices; the actual leaf L is always
included in the complete loaded set.

SIX_BODY_CYCLIC_FRONTIER.md gives sixteen rooted types from the seven
five-body block types without a positive K4. The book-hub and wheel-hub
roots are already entirely excluded by
ROOTED_BLOCK_ATTACHMENT_OBSTRUCTIONS.md. This manuscript supplies the
complete necessary positive-load cover for the other fourteen types.
It does not remove a root's additional leaf force to apply an isolated
five-body theorem.

## 1. Graph labels and the full table

Use the following exact positive block graphs.

* C5 has cyclic order0,1,2,3,4, and root0.
* The house has roof T, hubs A,D, and lower vertices B,C; its edges
  are AT,DT,AD,AB,BC,CD.
* K2,3 has hubs H,K and tips A,B,C, with all six hub--tip edges.
* The three-page book adds edge HK to that K2,3.
* The fan has hub H and path1--2--3--4, with H joined to all four.
* The subdivided K4 has original vertices A,B,C,D and subdivision
  vertex X on the former AB edge. Its edges are AX,XB,AC,AD,BC,BD,CD.
* The wheel has rim0--1--2--3--0 and hub H joined to every rim vertex.

A word such asTDC denotes the set {T,D,C}. Each representative includes
all graph automorphisms fixing the displayed root. Every actual circle
mask, zero individual circle weight, contact owner, shared-side mean
and additional zero-weight physical contact remains in its full domain.

| Block | Leaf root | Forced loaded block vertices | Remaining complete load representatives |
| --- | --- | --- | --- |
| C5 | 0 | None | 13; 23; 123; 124; 1234 |
| House | T | None | BC; AB; AC; ABD; ABC |
| House | A | T | TC; TB; TDC; TDB; TCB; TDCB |
| House | B | T | TA; TD; TAC; TDC |
| K2,3 | H | None | AB; KAB |
| K2,3 | A | None | BC; HB; HKB; HBC |
| Three-page book | H | A,B,C | None; whole rooted type already excluded |
| Three-page book | A | B,C | BC; HBC |
| Fan | H | 1,2,3,4 | 1234 |
| Fan | 1 | 2,3,4 | 234 |
| Fan | 2 | 1,3,4 | 134 |
| Subdivided K4 | X | C,D | CD |
| Subdivided K4 | A | C,D | CD |
| Subdivided K4 | C | D | DA; DX; DAB; DAX |
| Wheel | H | 0,1,2,3 | None; whole rooted type already excluded |
| Wheel | 0 | 1,2,3 | 123 |

After the full local exits proved below, the fourteen open rooted types
have38 necessary whole block-load orbits. This does not assert any orbit
is physically realizable. Four entire S-leaf mask families are further
excluded in Section8; those table entries retain their D alternatives.
No whole additional rooted type is declared closed by the load cover.

## 2. Necessary rules with their exact degree premises

An exact degree-two triangle tip is loaded, since its two neighbors
physically touch and a zero-load transmitter cannot have that property.
An exact degree-three vertex whose neighbors contain two physical edges
is loaded by NO_UNLOADED_DIAMOND_HUB.md. Both rules use each body's
actual total positive degree, including the additional root leaf.

The physical boundary-contact graph is a path forest, so any positive
triangle or four-cycle on loaded vertices is forbidden. Two endpoints
cannot have three common physical circle-touching positive neighbors,
by NO_THREE_BOUNDARY_COMMON_NEIGHBORS.md.

A two-transmitter channel cannot have a unit bypass. The full
UNIT_BYPASS_NORMAL_CHANNEL.md theorem allows arbitrary endpoint and
bypass degrees and all actual means.

More basically, any positive-width normal channel makes its endpoint
units physically disjoint: their supporting half-planes are separated
by its strictly positive reserve. Hence an unloaded degree-two path
cannot have an additional physical contact between its two endpoints.
This follows from the actual transmitter equations, regardless of the
endpoints' other forces or the values of the original side means.

TWO_PARALLEL_TRANSMITTERS_NO_THIRD_BYPASS.md gives a further local
restriction: two distinct unloaded exact-degree-two transmitters with
the same endpoints exclude any third physical unit bypass. Their two
original channels and the existing strict point normals are retained;
no third force is dropped to create a transmitter.

The positive-graph complement on the full loaded set is automatically
connected once the leaf is included: its sole positive neighbor is the
clear root, so the leaf has a complement edge to every block load.
Thus the old whole-five-body complement exclusions cannot be transferred
to an attached block. The other necessary rules remain fully applicable.

## 3. The rooted C5: two complete channel exits

The four nonroot vertices induce the path1--2--3--4. Before the channel
exits, its subsets of size at least two have seven orbits under the
reflection i -> -i modulo5 fixing0:

    two loads:   12,13,14,23;
    three loads: 123,124;
    four loads:  1234.

For two loads12, vertices3,4 are unloaded exact-degree-two bodies.
The actual path2--3--4--0 is a two-transmitter channel, and body1
is a unit bypass touching both endpoints through12 and01. The full
bypass theorem excludes this family, including its reflected34.

For two loads14, the actual path1--2--3--4 has two unloaded exact-
degree-two transmitters2,3, while root0 is its physical unit bypass.
The root retains its genuine degree three and its leaf force. The
same theorem excludes the entire14 family.

Both exits hold for every S/D leaf, endpoint load, physical mask and
actual mean, with all three extras retained. The five displayed C5
entries are exactly the remaining necessary positive-load cover.

## 4. The three rooted house types

### 4.1. Leaf at the roof T

No nonroot vertex is initially forced loaded. The four possible
block loads form the positive C4 with order A,D,C,B. All four cannot
be loaded because that would be a physical boundary four-cycle.
Every two- or three-element subset is otherwise retained by the
necessary path-forest test.

The root-preserving reflection exchanges A with D and B with C.
The six two-element subsets give representatives AD,BC,AB,AC. The
four triples give ABD,ABC. These are the six initial necessary
representatives. The entire AD family is impossible: B,C are both
unloaded exact-degree-two transmitters on A--B--C--D, whereas A,D
physically touch along the positive edge AD. Their channel's positive
reserve separates A and D, contradicting that actual contact. This
excludes both full S/D leaf alternatives and leaves the five table
entries BC,AB,AC,ABD,ABC.

### 4.2. Leaf at a hub A

The roof T is an unchanged degree-two triangle tip and is loaded.
The other nonroot vertices induce the path T--D--C--B. No other
vertex is initially forced by the exact local degree rules.
The full house has no nontrivial automorphism fixing A.

Every nonempty subset of {D,C,B} can accompany T without violating
the retained path-forest condition. The seven possibilities are
TD,TC,TB,TDC,TDB,TCB,TDCB. The entire TD family again leaves the
actual B,C channel unloaded between the physically touching endpoints
A,D. The same positive-reserve contradiction excludes it for both
full leaf types, leaving the six table entries. The root has genuine
degree four; the unused degree-three-root theorem is not applied to it.

### 4.3. Leaf at a lower vertex B

Again T is a forced loaded triangle tip. At most one of A,D can be
loaded, since A,D,T form a physical triangle. Among the nonroot
vertices T,A,D,C, the complete subsets of size at least two with
these properties are

    TA, TD, TC, TAC, TDC.

The entireTC alternative is already excluded by
SIX_BODY_MIDDLE_MOTIF_CONSEQUENCES.md: both true degree-three house
hubs A,D would be unloaded with their exact degree-two common roof T,
yet their distinct external neighbors B,C physically touch. The
uniform source allows B's genuine additional leaf force and all
its possible loads. Thus exactly TA,TD,TAC,TDC remain.

## 5. K2,3 and the book: both root orbits

### 5.1. K2,3 with the leaf at hub H

At most two of the degree-two tips A,B,C can be loaded, by the
three-common-boundary-neighbor theorem. The other hub K is optional.
At least two block loads are required. The hub-root symmetry permits
all permutations of A,B,C. Before the new local exit, the complete
necessary possibilities are AB,KA,KAB.

The entireKA family is excluded: the other two tips B,C are true
unloaded degree-two transmitters between H and K, and A is a third
physical bypass. TWO_PARALLEL_TRANSMITTERS_NO_THIRD_BYPASS.md applies
without using a force equation at the degree-four leaf root H.
Thus precisely AB and KAB remain, for both original leaf types.

### 5.2. K2,3 with the leaf at tip A

The four nonroot vertices H,K,B,C induce a positive C4. All four
cannot be loaded. The independent root-preserving swaps H<->K and
B<->C give three two-load representatives HK,BC,HB, and two
three-load representatives HKB,HBC.

The entireHK family is excluded: B,C are true unloaded degree-two
transmitters with common endpoints H,K and root A is a third unit
bypass. The root retains its leaf and genuine degree three; the
new local theorem uses only A's physical contacts. This leaves
exactly BC,HB,HKB,HBC for both full S/D leaf alternatives.

### 5.3. The three-page book

With a leaf at a hub, all three unchanged degree-two page tips
are loaded common neighbors of the hubs. The whole rooted type is
already excluded by ROOTED_BLOCK_ATTACHMENT_OBSTRUCTIONS.md.

With the leaf at page A, the other pages B,C remain loaded degree-two
triangle tips. Both hubs cannot be loaded because they and B would
form a physical boundary triangle. Up to exchange of the hubs,
the only possibilities are BC and HBC. Neither hub is assigned a
degree-three equation: both have actual degree four.

## 6. All three fan root orbits and the two wheel roots

In the fan, every unchanged endpoint of the path is a degree-two
triangle tip and is loaded. Every unchanged inner path vertex has
exact degree three, and its hub neighbor touches both of its other
neighbors. It is therefore loaded too.

With a leaf at H, all four path vertices1,2,3,4 are consequently
loaded, giving exactly1234. H retains degree five.
With a leaf at endpoint1, vertices2,3,4 are loaded; H is physically
circle-clear because H,3,4 cannot be a boundary triangle. This gives
exactly234. With a leaf at inner vertex2, vertices1,3,4 are loaded,
and the same triangle H,3,4 makes H physically clear. This gives
exactly134. No unmodified whole-fan equation has been used at a root.

For the wheel, a leaf at H leaves all four rim vertices with exact
degree three and a two-edge path among their neighbors. They are all
loaded, making a forbidden boundary four-cycle. This is the already
closed hub-root type.

With a leaf at rim0, the other three rim vertices1,2,3 are forced
loaded by that same exact-degree rule. H cannot physically touch
the circle, since it forms a triangle with1,2. Thus the only block
load set is123. The clear leaf root retains degree four.

## 7. Every root of the subdivided K4

Recall the exact edges AX,XB,AC,AD,BC,BD,CD. The automorphisms exchange
A with B and C with D, giving the three root types X,A,C.

At root X, both C,D retain degree three and each has two edges among
its neighbors. They are loaded. A is physically clear because A,C,D
form a triangle; B is clear for the same reason. Hence CD is the only
block load set.

At root A, C,D again retain degree three and are loaded. B is physically
clear by its triangle with C,D. If X were loaded, then C,D,X would be
three common positive circle-touching neighbors of A,B, impossible.
Thus X is unloaded and CD again is the only positive block load set.
The actual root A has degree four, so it is not subjected to an
unchanged degree-three test.

At root C, the vertex D is still forced loaded by its exact degree-
three neighbor pattern. The other nonroot vertices A,X,B,D induce
C4 in that order. All four cannot be loaded. Requiring D and taking
orbits under A<->B gives exactly

    two loads:   DA, DX;
    three loads: DAB, DAX.

These four are the complete remaining necessary masks. The other
vertices' loads are not silently forced by the old whole-block
complement condition; Section2 explains why that condition changes
when the actual loaded leaf is included.

## 8. Four further whole S-leaf mask families have no balance

S_LEAF_CONNECTED_BOUNDARY_NEIGHBORS.md is a full geometric and
force-balance theorem with no root-degree restriction. If every
loaded body other than the S leaf belongs to one connected physical
graph of boundary neighbors of its root, the whole component is
impossible. It retains arbitrary frames, physical zero-weight
boundary vertices and every circle-corner weight split.

Each row below satisfies that theorem using only positive edges
of the actual block; no extra physical contact is assumed.

| Block and root | Entire S-leaf positive block-load family | Actual connected boundary-neighbor graph |
| --- | --- | --- |
| Fan, root H | 1234 | Path1--2--3--4; all neighbors of H |
| Subdivided K4, root A | CD | Edge C--D; both neighbors of A |
| Subdivided K4, root C | DA | Edge D--A; both neighbors of C |
| Subdivided K4, root C | DAB | Path A--D--B; all neighbors of C |

In each case the displayed set is the entire positive block-load
set and L is the only remaining loaded body. Thus every premise
holds for all physical mask and contact-mean choices. These four
whole S alternatives are excluded. Their D alternatives remain in
the full table. In particular the whole S type of the fan-hub root
and of the subdivided-K4 endpoint root is closed, but neither whole
rooted graph is declared excluded.

## 9. Live scope and remaining exits

The sixteen rooted graph types are fully covered: two are already
closed by uniform local-degree theorems, and the other fourteen
have the38 exact necessary load representatives in Section1. The
new whole both-leaf-type exits are the two C5 channel families, the
two house channels whose endpoints touch, and the two K2,3
double-transmitter families. Section8 gives four further
entire S-leaf mask exits without changing a D leaf into an S leaf.

Every retained gate must still prove a whole core contradiction,
a sharp radius bound or a joint capacity result excluding all
three arbitrary extra squares. All positive root forces, original
mean intervals, physical zero-weight contacts and actual circle
masks remain. This cover does not give a physical realization of
any entry, close C1.5.b1, or import an isolated five-body theorem
into a graph carrying the additional leaf force.

No numerical graph enumeration, sampled pose, post-extraction
normal change, Lean compilation or CI is used.

## 10. Current complete graph exclusions, house detours and the C5 channel fork

The earlier tables record the necessary load cover before the
subsequent whole-graph theorems.
SPANNING_K23_LEAF_BLOCK_EXCLUSION.md, its complete original-gate
assembly and independent review now exclude every genuine-leaf
root of K2,3, the three-page book, the subdivided K4 and the
wheel. These statements retain the original root degrees and
every force. Together with the earlier local exits, nine of the
sixteen rooted five-body types are entirely closed.

LEAF_ROOT_BOUNDARY_DETOUR_HOUSE_LOAD_EXCLUSIONS.md now excludes
the full house-hub load orbit TDC and the full house-lower load
orbit TA, for both S and D leaves. The actual channels are
A--B--C and B--C--D respectively; their physical boundary
detours are D and A. The far endpoint D in the second case
retains its true unloaded degree three. The inherited
central-channel theorem uses no endpoint-degree equation.

The full saved-source joins passed independent reviews in
REVIEW_LEAF_ROOT_HOUSE_DETOURS_ROOT_2026_10_26.md and
REVIEW_LEAF_ROOT_BOUNDARY_DETOUR_HOUSE_C6_2026_10_26.md.
RADIAL_LEAF_TWO_BOUNDARY_CHANNEL_FORK_EXCLUSION.md further
excludes the complete C5 load23 orbit for both genuine S and D
leaves. The actual root0 has degree3, and the real channels
0--1--2 and 0--4--3 pass through true unloaded degree2 bodies.
Their distinct boundary endpoints and all three arbitrary extras
are retained. Full reviews are
REVIEW_RADIAL_LEAF_FORK_ROOT_2026_10_26.md and
REVIEW_RADIAL_LEAF_TWO_BOUNDARY_CHANNEL_FORK_C6_2026_10_26.md.
Only the pre-existing M6.B5L.C5.L23.S and .D labels close.

The exact current load cover of the seven still-open rooted types
is therefore:

| Rooted type | Remaining necessary block-load orbits |
| --- | --- |
| C5, root 0 | 13; 123; 124; 1234 |
| House, roof T | BC; AB; AC; ABD; ABC |
| House, hub A | TC; TB; TDB; TCB; TDCB |
| House, lower B | TD; TAC; TDC |
| Fan, hub H | 1234, retaining only the D-leaf alternative |
| Fan, endpoint 1 | 234 |
| Fan, inner path vertex 2 | 134 |

These are 20 necessary open load orbits, down from 23 before the
two house exits and the C5 load23 exit. The original hub TD and lower TC exits
are distinct and are not counted again. No entire additional
rooted type or coarse C1.5.b1 cell closes here. The genuine leaf,
physical zero-weight circle contacts, full masks and means,
unchanged total degrees and all three arbitrary completion
squares remain in every open row.

