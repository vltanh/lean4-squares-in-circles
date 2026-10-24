# The nine exterior-hexagon graph types and their complete necessary load cover

**Status: complete hand finite cover and one additional whole load-family
exit; root and separate independent full hand audits passed.**
Work with the selected physical certificate in the declared radius window.
This is a refinement of the exterior-hexagon branch of
SIX_BODY_CYCLIC_FRONTIER.md. All six-body components retain three arbitrary
physical completion squares, all physical zero-weight contacts and all
continuous positions, frames, means and circle-weight splits.

Label the actual exterior face 0,1,2,3,4,5 in cyclic order. The six rim
edges are always present. Every additional positive edge is one of the
nine diagonals, and at most three can occur. All diagonal subsets below
are noncrossing in this actual plane embedding. A label such as02 means
the edge {0,2}; a load set such as014 means {0,1,4}. Labels are taken
modulo6. Reflections and rotations of the entire hexagon are permitted.

**Cover theorem.** There are exactly nine graph types in Section1.
After the full necessary reductions in Section2, their load sets have
exactly the representatives in Section3. The table is a necessary
domain cover, not a claim of geometric realizability. No entire chorded
graph in the table is closed by its enumeration alone.

## 1. Exactly nine graph types, by a hand chord count

With no diagonal there is one type. A single diagonal has cyclic
endpoint distance2 or3, represented by02 or03.

For two diagonals sharing a vertex, move that vertex to0. Its possible
diagonals are02,03,04. Up to reflection their two-element subsets are
{02,03} and {02,04}.

For two disjoint diagonals, neither can be a diameter. A diameter03
splits the hexagon into two quadrilaterals; every further diagonal on
either side shares0 or3. Thus move one of the short diagonals to02.
Of the diagonals disjoint from its endpoints, only35 does not cross02.
This gives exactly the third two-chord type {02,35}.

Finally a noncrossing three-diagonal set triangulates the hexagon.
One can enumerate its third diagonal from the preceding full two-chord
cover without appealing to a graph search:

| First two diagonals | Every possible noncrossing third diagonal |
| --- | --- |
| 02,03 | 04 or35 |
| 02,04 | 03 or24 |
| 02,35 | 03 or25 |

The two choices in the last row are related by a hexagon symmetry.
Thus the three complete three-chord types are the fan {02,03,04},
the path of chords {02,03,35}, and the central triangle {02,04,24}.
Together the counts are1+2+3+3=9. The types are distinct by chord
count, shared endpoint, chord length or chord-incidence graph.

## 2. Necessary reductions used in every row

The positively loaded set L has at least three vertices. It has at
most five here: all six boundary vertices would give a forbidden
physical boundary six-cycle. Zero circle load does not by itself
mean that a vertex is physically circle-clear.

The following conditions are applied only where their premises hold.

1. An exact positive degree-two vertex whose two neighbors physically
   touch is loaded, by the opposite-support transmission obstruction.
2. An exact positive degree-three vertex whose three neighbors induce
   two physical edges is loaded, by NO_UNLOADED_DIAMOND_HUB.md.
3. The positive graph induced by L is a path forest: the physical
   circle-touching graph is a path forest. In particular it has no
   triangle or four-cycle, and no vertex has three loaded neighbors
   while itself loaded.
4. The positive-graph complement induced by L is connected, since the
   physical noncontact graph on L is connected. This is a necessary
   graph condition only; an omitted positive edge is not asserted to
   be a physical noncontact.
5. For the opposite-ear graph {02,35}, the complete local theorem
   UNLOADED_TRIANGLE_HUB_EXTERNAL_SEPARATION.md requires at least one
   loaded hub in each of {0,2} and {3,5}. Both true degree-three hubs
   cannot be unloaded while their external neighbors physically touch.
6. A channel with two unloaded exact-degree-two internal vertices cannot
   have a unit-square bypass touching its two endpoints. This is the
   full UNIT_BYPASS_NORMAL_CHANNEL.md theorem; endpoint loads and
   degrees are arbitrary.

The last condition gives one additional whole positive-load-family
exit in the single-short-chord graph. With chord02 and loads013,
the actual path3--4--5--0 has the two unloaded exact-degree-two
transmitters4,5. Body2 physically touches both endpoints3 and0,
so is a unit bypass. The reserve is at least2, whereas the bypass
allows only one side transmitter. This excludes the entire013
orbit, including its reflected125 labeling, all transmitter widths,
all actual means and all three extra squares. No degree-three hub
is made a transmitter in this argument.

## 3. Complete necessary positive-load table

Every entry is a representative under the dihedral symmetries that
preserve the displayed graph. The complete domains obtained from it
include every image under those symmetries.

| Positive chords | Forced loaded vertices | Three loads | Four loads | Five loads |
| --- | --- | --- | --- | --- |
| None | None | 013,024 | 0123,0124,0134 | 01234 |
| 02 | 1 | 014,134,135 | 0134,0135,0145,1345 | 01345 |
| 03 | None | 014,024,124 | 0124,0125,0134,1245 | 01245 |
| 02,03 | 1,2 | 124,125 | 1234,1235,1245 | 12345 |
| 02,04 | 1,5 | 125,135 | 0135,1235,1245 | 12345 |
| 02,35 | 1,4 | None | 0134,0145 | None |
| 02,03,04 | 1,2,3,4,5 | None | None | 12345 |
| 02,03,35 | 1,2,4,5 | None | 1245 | None |
| 02,04,24 | 1,3,5 | 135 | 0135 | None |

Here "forced" records only the unconditional local degree rules.
Further dependencies between optional loaded vertices are retained in
the actual load columns. The next section verifies the complete finite
enumeration by hand.

## 4. Verification of every table row

### 4.1. No chord

For three loads, connected complement excludes two positive induced
edges. Their cyclic gap triples are therefore(2,2,2) or(1,2,3),
represented by024 and013. Four loads are classified by the cyclic
distance1,2,3 of their two omitted vertices, giving0123,0124,0134.
Five loads have one omitted vertex, giving01234. These are the six
bare-cycle orbits already proved in SIX_BODY_CYCLIC_FRONTIER.md.

The later complete simple-cycle theorems exclude013 and0123. Thus
the current bare-cycle residual consists of024,0124,0134,01234.
In024 the whole width class with at least two diagonal transmitters
is separately excluded by SIX_CYCLE_ALTERNATING_DOUBLE_DIAGONAL_EXCLUSION.md.
Zero or one diagonal remains in that complete load orbit.

### 4.2. One short chord02

Vertex1 is a degree-two triangle tip and is loaded. Vertices0,2
cannot both be loaded because012 is a physical triangle. The
reflection i -> 2-i exchanges0 with2 and3 with5 while fixing1,4.

For three loads, choose two more vertices from0,2,3,4,5. The pair02
is forbidden by the triangle. Pairs05 and23 give a loaded path of
length two and hence disconnected complement. Pairs03 and25 are
the full bypass exclusion of Section2. The remaining pairs are04,
24,34,35,45, giving exactly014,134,135 modulo the stated reflection.

For four loads, choose three of0,2,3,4,5 without including both0,2.
The seven possibilities pair under reflection into0134,0135,0145
and1345. Each satisfies the retained necessary graph conditions.
For five loads, precisely one of0,2 is omitted; the two possibilities
are reflected, giving01345. This proves the entire row.

### 4.3. One diameter03

The symmetry group is generated by i -> -i and i -> i+3.
For three loads, both0,3 cannot be loaded: every remaining vertex
is adjacent to one of them, giving at least two positive induced
edges. With exactly one of0,3 loaded, take it to be0. The other
pair is represented by14 or24; the other choices either give a
two-edge loaded path or reflect to these. With neither0 nor3
loaded, the three loads are any three of1,2,4,5, giving one orbit124.

For four loads with both0,3 loaded, pairs12 and45 create a boundary
four-cycle, and pairs15 and24 make a loaded branch degree three.
The remaining pairs14 and25 are equivalent, giving0134. With
exactly one of0,3 loaded, the four choices of three other vertices
give0124 and0125 modulo reflection. With neither loaded, the set
is1245. For five loads, a branch vertex0 or3 must be the omitted
one; otherwise the other branch has three loaded neighbors. This
gives01245 and proves the row.

### 4.4. Two chords02,03

The local degree rules force1,2. Vertex0 is physically circle-clear
because it completes their triangle012. Choose a nonempty subset
of3,4,5 as additional loads. The singleton3 gives a two-edge
loaded path123 with disconnected complement. The singletons4,5,
all three two-element subsets, and the three-element subset give
exactly the displayed six possibilities. No further symmetry
identifies the listed representatives.

### 4.5. Two chords02,04

The triangle tips1,5 are loaded. If0 is loaded, neither2 nor4 can
be loaded, because of triangles012 and045. The triple015 has
disconnected complement, leaving exactly0135 in this case.

If0 is unloaded, add a nonempty subset of2,3,4 to the forced1,5.
The reflection i -> -i exchanges2 with4 and1 with5. Singletons
give125 or135; pairs give1235 or1245; the full subset gives12345.
Together with0135 these are exactly the six displayed possibilities.

### 4.6. Opposite ears02,35

The true triangle tips1,4 are loaded. Each of the hub pairs{0,2}
and{3,5} has at most one loaded member, by its loaded-tip triangle.
Section2's unloaded-hub external-separation theorem forces at least
one member of each pair loaded. Thus there are exactly four loads:
1,4 and one hub from each pair. The selected hubs either are adjacent
along a rim edge, giving0145, or are not, giving0134. These are the
two complete load orbits of SIX_BODY_MIDDLE_MOTIF_CONSEQUENCES.md.

### 4.7. Three-chord fan02,03,04

The endpoint tips1,5 are loaded. Each of2,3,4 has exact positive
degree three and its hub neighbor0 touches its other two neighbors.
They are therefore loaded too. Vertex0 cannot physically touch the
circle, since it touches five loaded bodies. The unique load set is12345.

### 4.8. Three-chord path02,03,35

The ear tips1,4 are loaded. The true degree-three vertices2,5 each
have a neighbor touching their other two neighbors, so both are
loaded. Vertices0 and3 complete the respective loaded-tip triangles
012 and345, and are physically circle-clear. The unique load set is1245.

### 4.9. Three-chord central triangle02,04,24

The tips1,3,5 are loaded. Any two central vertices0,2,4 share a
triangle with one of those loaded tips, so at most one central vertex
can be loaded. There is a symmetry permuting the three central
vertices. The only possibilities are therefore135 or0135.

## 5. Live proof obligations and exact limits

This supplies nine explicit whole graph domains for the exterior-hexagon
branch. With the five surviving exterior-pentagon graph domains of
SIX_BODY_CYCLIC_FRONTIER.md, it gives fourteen graph domains for the
remaining six-body biconnected cell before their complete metric and
completion exits are supplied.

The single-short-chord013 load family is now excluded in full by a
genuine two-transmitter channel and its actual unit bypass. The bare
cycle's previously closed families and the opposite-ears three-load
exit remain closed at their established scopes. Every table entry left
open retains all actual positive root degrees, its full continuous
contact and circle-mask domain, and all three extra physical squares.

This cover does not assert that any listed graph or load assignment is
realizable, nor does it declare any whole chorded graph closed. A
positive chord is never deleted to invoke an exact smaller-cycle
theorem. C1.6.b0 and all six six-body coarse rows remain open. There
is no sampled pose, numerical radius certificate, Lean compilation or CI
in the hand count or the bypass proof.
