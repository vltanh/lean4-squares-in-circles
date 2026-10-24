# The five interior-pentagon graphs and their complete necessary load cover

**Status: complete hand finite cover and two additional whole load-family
exclusions; root and separate independent full hand audits passed.**
Use the common selected certificate in the declared radius window
79/40 <= R <= sqrt(1105)/16. The entire six-body positive component
is biconnected, with exterior face 0,1,2,3,4 in cyclic order and its
one physically circle-clear interior body H. All three other physical
squares remain present. Every actual contact mean, positive force,
physical zero-weight contact and physical circle mask is retained.

SIX_BODY_CYCLIC_FRONTIER.md, Sections 5--6, proves that the five
surviving graph domains are exactly those in the table below. This
manuscript gives their full necessary positive-load cover. It also
excludes the entire no-chord/two-spoke load family0234 by the existing
balanced boundary-path theorem and the true H transmitter. The full
two-spoke/chord03 family024 is now excluded by two actual parallel
transmitters and a third physical unit bypass, with every force kept.

A word such as013 means the positive-load set {0,1,3}. Each listed
set includes all images under a dihedral symmetry preserving the
actual exterior pentagon, the displayed spokes and the displayed
outer chords. The table is a necessary cover, not an assertion that
any of its full physical domains is realizable.

## 1. The exact graph and load table

| H spokes | Outer chord | Forced rim loads from local degrees | Three loads | Four loads |
| --- | --- | --- | --- | --- |
| 0,2 | None | None | 013,023,134 | 1234,0124 |
| 0,2 | 03 | 4 | 124,134 | 1234,0124 |
| 0,1,3 | None | None | 013,023,024 | 1234,0134,0124 |
| 0,1,2,3 | None | 1,2 | 124 | 0124 |
| 0,1,2,3 | 03 | 1,2,4 | 124 | 0124 |

The first row's fourth-load set0234 is already excluded by Section 3.
The fourth row's all-four-spoke-loaded set0123 was already excluded
in SIX_BODY_CYCLIC_FRONTIER.md, Section 6.3. These are exclusions of
whole load families, not a deletion of their positive spoke forces.

The row counts are5,4,6,2,2: nineteen necessary whole graph/load orbits
remain after those complete exits. Every one retains all continuous
positions, frames, circle-corner weights, contact features and shared
means, all actual positive degrees and all three arbitrary extras.
None of the five whole graph domains is closed by this cover alone.

## 2. Common necessary load rules

H is physically circle-clear, hence has no circle multiplier. At least
three rim bodies are positively loaded. All five rim bodies cannot
physically touch the circle, because they form a physical boundary C5.
Thus the positive-load count is exactly three or four.

The positive-graph complement induced on the loaded set is connected.
For three vertices this means that at most one positive edge occurs
among them. Among the exterior pentagon's ten three-element subsets,
the complete surviving list before adding chords is

    013, 023, 024, 124, 134.

Indeed the five remaining triples012,014,034,123,234 each contain
two consecutive rim edges, so their complements are disconnected.
Every displayed triple has exactly one rim edge and a connected
complement. With four rim loads and no outer chord, the induced rim
graph is a four-vertex path, whose complement is connected. Every
omitted-vertex choice is initially retained.

An exact positive degree-two triangle tip is loaded, since its two
neighbors physically touch and a zero-load transmitter cannot have
that property. An exact positive degree-three body whose three
neighbors induce a two-edge path is loaded by
NO_UNLOADED_DIAMOND_HUB.md. These degree premises refer to the actual
whole graph; no spoke or chord is deleted in their application.

Additional physical zero-weight contacts can only impose further
restrictions. An absent positive edge is never asserted to be a
physical noncontact merely from this table.

## 3. Two spokes0,2 and no outer chord

The actual H is an unloaded exact-degree-two transmitter between
0 and2. Rim body1 is a unit bypass touching both endpoints. The
complete theorem UNIT_BYPASS_NORMAL_CHANNEL.md forces H to be a
side-normal transmitter of reserve1, including all actual transverse
application means. Its two endpoint applications p_0,p_2 satisfy

    |p_0-p_2| = 1.

If the loaded set were0234, the four boundary units form the actual
three-edge path2--3--4--0. H and1 are unloaded, so all four positive
circle-resultant vectors on that path sum to zero. The full physical
FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md theorem therefore gives

    |c_0-c_2| > 1+sqrt(2).

On the other hand, p_i belongs to the actual unit square i. Its
distance from that square's center is at most1/sqrt(2). The actual
H channel consequently gives

    |c_0-c_2| <= |c_0-p_0| + |p_0-p_2| + |p_2-c_2|
               <= 1+sqrt(2),

which is a contradiction. The whole0234 load family is excluded.
The endpoint degrees need not be two, and their actual extra H/rim
forces have not been omitted. All three completion squares remain.

The graph-preserving exterior reflection is i -> 2-i modulo5.
It exchanges0 with2 and3 with4, and fixes1. In the three-load list,
it pairs013 with124, pairs023 with024, and fixes134. Thus the three
complete representatives are013,023,134.

For four loads, omitting0 is equivalent to omitting2, omitting3 is
equivalent to omitting4, and omitting1 is fixed. The last possibility
is exactly the excluded0234 family. The other two representatives
are1234 and0124, proving the first row in its entirety.

## 4. Two spokes0,2 and the outer chord03

The reflection above exchanges the choices of outer chord03 and24;
we fix03 for this row. Rim vertex4 is an exact positive degree-two
triangle tip with adjacent neighbors0,3, so4 is loaded.

From the complete three-load list in Section 2, chord03 adds a
second induced positive edge to each of013 and023, disconnecting
their loaded complements. The other three triples024,124,134 each
contain4 and retain a connected complement. These are the three initial
necessary representatives. No nontrivial exterior
pentagon symmetry preserves both the spokes0,2 and chord03, so
none of these three initial entries is identified with another.

The entire024 family is excluded by
TWO_PARALLEL_TRANSMITTERS_NO_THIRD_BYPASS.md. H and rim1 are true
unloaded degree-two transmitters with the same endpoints0,2. Rim3
is a third physical unit bypass via03 and23. Its genuine degree
three and every other force remain; no transmitter equation is
applied to it. The uniform local theorem is impossible for these
five actual bodies, so only124 and134 remain as three-load sets.
This is a full graph/load exclusion for every physical mask and
actual mean, retaining all three original extras.

For four loads, vertex4 cannot be omitted. Moreover0 and3 cannot
both be loaded, because0,3,4 would be a physical boundary triangle.
Thus the omitted vertex is0 or3, giving exactly1234 or0124. Both
induce a four-vertex boundary path; their complements are connected.
This proves the complete second row. H still has reserve1, but its
endpoints are not the endpoints of either displayed four-load path,
so Section 3's endpoint argument is not imported into this row.

## 5. Three spokes0,1,3 and no outer chord

No rim vertex is initially forced loaded by the local degree rules.
The positive graph induced on rim loads has only rim edges, so the
complete three-load list and the five omitted-vertex four-load
choices from Section 2 remain necessary possibilities.

The reflection i -> 1-i modulo5 preserves the spoke set. It fixes3
and exchanges0 with1 and2 with4. On the three-load list it fixes013,
exchanges023 with134, and exchanges024 with124. This gives exactly
013,023,024. For four loads, the omitted-vertex orbits are{0,1},
{2,4} and{3}, represented by1234,0134,0124 respectively.

These are all dihedral images preserving the displayed graph and
all entries of the third row. The actual H retains three positive
forces. No transmitted-path formula is applied to it by discarding
one of its spokes.

## 6. Four spokes, both full chord alternatives

Take the missing spoke to be4, so H is joined to0,1,2,3. Vertices1
and2 each have exact positive degree three, and their H neighbor
touches both of their other neighbors. They are therefore loaded.

First suppose the outer chord03 is absent. Among Section 2's five
three-load sets, only124 contains both1 and2. For four loads, only
0,3 or4 can be omitted. The omission of4 gives all four spoke
vertices0123 loaded. SIX_BODY_CYCLIC_FRONTIER.md, Section 6.3,
excludes this entire family: its true missing-spoke transmitter4
has the unit bypass H, so endpoint separation is at most1+sqrt(2),
whereas the balanced actual path0--1--2--3 requires more.

The reflection i -> 3-i modulo5 exchanges0 with3, exchanges1 with2
and fixes4. It identifies the other two omitted-vertex choices,
leaving representative0124. This proves the fourth row.
For precisely this no-chord row, the same source also proves H and4
physically closed-disjoint, including every possible zero-weight
contact. That additional full physical restriction is retained.

Now include chord03. The degree-two triangle tip4 is forced loaded
as well as1,2. At most one of0,3 can physically touch the circle,
because either combined with the other and4 would be a boundary
triangle. Hence the only three-load set is124, and a four-load set
adds exactly one of0,3. The same reflection identifies those two
choices, leaving representative0124. This proves the final row.
The no-chord physical H--4 noncontact conclusion is not transferred
to this graph without its premises. H and the chord endpoints keep
their true degree-four equations.

## 7. Exact remaining proof contracts

This finishes the hand load enumeration for every one of the five
surviving exterior-pentagon graph domains. Together with the nine
hexagon types in SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md, it gives
an explicit necessary graph/load cover for the entire six-body
biconnected cell C1.6.b0. The hexagon source has38 open whole load
orbits and this source has19; neither count is a completion percentage.

Each remaining row/set must receive a whole core contradiction,
a sharp radius theorem, or a complete joint capacity bound excluding
its three remaining physical squares. Physical holes require their
own barrier proof, actual circle masks retain zero individual weights,
and every genuine shared side retains its complete mean interval.
A positive chord, spoke or higher-degree root force cannot be removed
to apply an exact smaller-component theorem.

All five graph parents and C1.6.b0 remain open. The coarse ledger
is unchanged by this necessary cover and its two additional entire
load-family exits. No numerical graph enumeration, pose sampling,
Lean compilation or CI is used.
