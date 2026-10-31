# Every positive-chord outer hexagon has central capacity at most one

Date: October 26, 2026.

**Status: accepted complete geometric branch reduction after the full-source
reviews REVIEW_CHORDED_HEXAGON_CENTRAL_CAPACITY_ROOT_2026_10_26.md and
REVIEW_CHORDED_HEXAGON_CENTRAL_CAPACITY_GLOBAL_2026_10_26.md.**
No original graph/load parent is declared closed.

Put Q=1105/256. Keep six actual unit squares with pairwise disjoint
open interiors in the same disk D_R, R<=sqrt(Q), and the physical plane
embedding of their selected positive graph. Its exterior-face cycle is
0,1,2,3,4,5, and it has at least one of the original positive chords.
All actual chord forces and true degrees remain. No circle load or
physical circle mask is prescribed in the geometric argument below.

**Theorem.** The whole bounded free union inside the actual outer
hexagon contains at most one further physical unit square. If the graph
is one of the three triangulated types, that whole union contains none.

The conclusion counts all bounded physical free components together,
including subdivisions by further zero-weight contacts and all weak
contact-junction limits. All other actual packing squares are retained.

## 1. Actual face routing and the complete face list

The accepted physical uncrossing theorem supplies the selected plane
embedding with six actual vertices on the exterior cycle. The complete
noncrossing chord cover in
`SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md`, Section 1, gives exactly
these eight positive-chord types, up to a dihedral relabeling of all
physical data:

| Positive chords | Actual bounded face cycles |
| --- | --- |
| 02 | 012; 02345 |
| 03 | 0123; 0345 |
| 02,03 | 012; 023; 0345 |
| 02,04 | 012; 045; 0234 |
| 02,35 | 012; 345; 0235 |
| 02,03,04 | 012; 023; 034; 045 |
| 02,03,35 | 012; 023; 035; 345 |
| 02,04,24 | 012; 234; 045; 024 |

Each bounded face is a simple physical contact cycle. An extra's open
interior avoids every closed core unit and therefore every occupied
center/contact path of the graph. Connectedness puts it on one bounded
face side if it is central. At weak junctions, fix a compact inner part
of the extra first; it has positive distance from the closed core.
All sufficiently small physical routings preserve its face label and
winding. Closure gives its whole unit area on that face's bounded side.
This is exactly the compact-interior routing convention in
`CONTACT_RING_HOLE_AREA.md` and
`FOUR_CYCLE_THREE_BOUNDARY_HOLE_EMPTY.md`, Section 1.

Thus every actual central extra contributes its full unit area to one
of the face contact rings listed above. No chord is removed during this
assignment. Further physical contacts may subdivide these regions but
cannot merge them through an occupied barrier.

## 2. The triangle, pentagon and quadrilateral bounds

The uniform physical contact-ring area theorem gives

    area(free bounded region of an n-ring)
        <=(n/4) cot(pi/n).                              (1)

This bounds the whole free union, not one selected component. For n=3
the upper bound is sqrt(3)/4<1, so every triangular face is empty of
additional units. For n=5,

    cot(pi/5)^2=1+2sqrt(5)/5<2<(3/2)^2,

and therefore the bound in (1) is less than 15/8<2. A pentagonal face
has unit capacity at most one. The exact identity follows from the
usual cos(pi/5)=(1+sqrt(5))/4 formula; the comparison uses sqrt(5)<5/2.

For n=4, (1) is at most one, and any occupied quadrilateral forces
equality. The complete degree-free equality proof is Sections 1--2 of
`FOUR_CYCLE_THREE_BOUNDARY_HOLE_EMPTY.md` (the three-boundary hypothesis
enters only its later Section 3), and Section 2 of
`SPANNING_K23_LEAF_BLOCK_EXCLUSION.md`. It proves precisely:

    If a physical four-unit ring encloses a whole unit T, the four
    ring units and T are one aligned cross. T is the central unit,
    and the four ring units share its four full sides. Consecutive
    ring units meet at a single actual vertex of T.                 (2)

The equality proof retains all weak junctions. Its contact polygon
must have four distinct vertices and side lengths one, must be a unit
square, and each original ring chord must be a whole side. No loaded
body, force equation, leaf, secondary minimizer or chosen orientation
is needed for (2).

## 3. Two faces separated by a diameter chord cannot both be occupied

The only row whose individual face capacities could sum to two is
the single diameter chord 03, with faces 0123 and 0345. Suppose both
contain an additional unit. Apply (2) to the first actual ring. After
one rigid coordinate change, the first central unit is
[-1/2,1/2]^2 and the actual core centers in its cyclic order are

    c_0=(1,0), c_1=(0,1), c_2=(-1,0), c_3=(0,-1).       (3)

The shared original pair 0,3 has the unique physical intersection
p=(1/2,-1/2). The second ring must also be an aligned cross by (2).
Its common frame is already fixed by the unchanged actual units 0,3.
Its central unit has p as a vertex and lies on the other side of the
original chord 03 from the first face. Equivalently, at p the northeast
and southwest quadrants are occupied by 0 and 3, and the northwest
quadrant is occupied by the first central unit. The second central
unit must be the southeast unit

    [1/2,3/2] times [-3/2,-1/2], center (1,-1).

Its remaining actual cross neighbors consequently have centers

    c_4=(1,-2), c_5=(2,-1).                              (4)

Reflection or a reversed rim orientation gives the same distances.
In particular (3)--(4) force

    |c_1-c_4|^2=10.                                     (5)

Every actual contained unit center has norm less than 91/60 about
the unchanged original disk origin, since

    (91/60)^2+91/60+1/2-Q=31/57600>0.

Therefore every center pair has distance less than 91/30. This is
incompatible with (5), because

    10-(91/30)^2=719/900>0.

The coordinate change used to display the two crosses changes neither
that pair distance nor the common disk-origin center bound. Hence the
two quadrilateral faces cannot both contain a unit. Their combined
central capacity is at most one.

## 4. Whole eight-type conclusion and exact scope

For a single short chord, the triangle is empty and the pentagon has
capacity at most one. Section 3 handles the single diameter chord.
Each two-chord row has two empty triangles and one quadrilateral of
capacity at most one. Every three-chord row has four empty triangles.
These are all eight complete graph types in Section 1, with every
actual physical pose and load mask still present. This proves the
stated whole central-capacity theorem.

Consequently, in any nine-square completion of a positive-chord outer
hexagon, at least two of the three extra units must be exterior. For
each of the three triangulated graph types all three must be exterior.
This necessary allocation conclusion is uniform over the complete
34 graph/load orbits in the accepted eight-type load table. It does
not exclude any whole load orbit by itself.

No simple-cycle force equation is applied at a chord endpoint, no
unloaded higher-degree hub is called a transmitter, and no positive
chord is discarded. The full exterior joint-capacity problem for every
graph type remains to be proved. In particular this source closes no
HEXAGON graph/load parent, no HEXAGON.BOUND parent and no coarse
C1.6.b0 cell. The non-hexagonal six-body embeddings are separate.

No computational certificate, sampled physical pose, Lean compilation,
CI, remote write or shared-ledger edit is used.
