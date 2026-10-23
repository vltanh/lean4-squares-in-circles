# Seventeen coarse interleavings for three cores and eight rings

Work in the three-core/eight-ring case at `q<=49013/10000`, using core
radius `41/40` and auxiliary circle radius `27/20`. The ring squares have
eight connected closed arcs of positive length, each with its center ray
in the arc interior. Label them in cyclic order.

[CORE_SPLIT_GAP_EXCLUSION.md](boundary/CORE_SPLIT_GAP_EXCLUSION.md) proves
that a core circle intersection has at most two components and that no ring
arc can pass between those two components. Its angular hull is therefore
disjoint from every ring arc's open interior. Thus every core whose circle
intersection has positive angular measure belongs to **one** of the eight
gaps between consecutive ring arcs. A core with zero angular measure is
called inactive for this word only; all of its physical geometry remains.

To justify the assignment even for split intersections, if its two components
lay in different ring gaps, the short gap separating them would contain a
whole ring arc. The split-gap theorem forbids this. The ring arcs all have
positive length, so there is no zero-length ring to bypass this argument.
Tangency-only core intersections may be ignored in this coarse assignment,
which only enlarges the cover; their original physical constraints remain.

For each ring gap let `w_i` be the number of active cores assigned to it.
Then

\[
w_i\in\{0,1,2,3\},\qquad \sum_{i=0}^7w_i\le3.
\]

The raw weak occupancy list has `binom(11,3)=165` words. Rotation of the
ring labels and reversal of their cyclic listing give 17 dihedral classes.
The exact enumerator `enumerate_three_core_interleavings.py` visits every
integer word in `{0,1,2,3}^8` with sum at most three. It checks the raw count,
the 17 classes, and that each class receives exactly the size of its full
dihedral orbit. Its complete machine-readable result is
`THREE_CORE_INTERLEAVINGS.json`.

| Number of active cores | Number of dihedral rows |
| ---: | ---: |
| 0 | 1 |
| 1 | 1 |
| 2 | 5 |
| 3 | 10 |

The canonical words are:

| Active cores | Canonical words |
| ---: | --- |
| 0 | `00000000` |
| 1 | `00000001` |
| 2 | `00000002`, `00000011`, `00000101`, `00001001`, `00010001` |
| 3 | `00000003`, `00000012`, `00000102`, `00000111`, `00001002`, `00001011`, `00010002`, `00010011`, `00010101`, `00100101` |

These rows are a geometric necessary cover. They do not claim every word
is realizable, determine the order of multiple core components inside one
gap, fix any square frame, or replace any corner or pair constraint.
The continuous ring poses, all three core poses, all 44 corner inequalities,
and all 55 physical pair conditions remain part of each row. The reversal
is a choice of listing order; an equality classification must still retain
the actual orientation or reflection data of the physical packing.

The known candidate illustrates two rows: its permanently visible core 4
lies in the ring-5/ring-3 gap, while core 8 has no auxiliary-circle arc.
Core 1 is invisible for one portion of its slider range and enters the
ring-2/ring-0 gap for another portion. In the eight-ring cyclic order those
two gaps have distance two, giving `00000001` and `00000101` respectively.
At the transition the new intersection is a point and belongs to the first
coarse row under the convention above. This observation identifies target
rows; it is not an exhaustive capture theorem for either row.

All 17 rows still need a sharp lower-bound or reduction theorem. The point of
the list is to expose actual finite interleaving alternatives after a proved
continuous geometric reduction, rather than to infer the candidate word from
a numerical picture.
