# A four-unit ring with opposite boundary units has an empty central region

Date: October 28, 2026 UTC. Author: root continuation.

**Status: new reconstructed complete force-free hand proof, awaiting a
fresh independent review.** The original lost manuscript had SHA256
`644666e13c3dfc2f68ccd311be643ccac50af2f10cfeff8f51dada83899e6f77`.
These are new bytes; no historical review is transferred to this pin.

## 1. Full physical theorem

Keep four actual interior-disjoint unit squares in one containing disk,
with an actual physical contact ring in the common compatible plane
embedding. Suppose two opposite ring units physically touch the circle.
If R^2 is not 5/2, the entire bounded free region of that ring has
unit-square capacity zero.

True degrees and all forces outside the ring are arbitrary. Physical
circle contact, including a zero individual or zero total selected
multiplier, is sufficient. Every original application, side mean,
weak contact junction, and other square remains present. The argument
does not choose new normal directions or alter the force certificate.

## 2. The complete occupied-ring equality case

The already proved physical contact-ring area theorem gives at most
one unit of free area on the bounded side of a four-ring. Its complete
equality proof, including all weak junctions, says that the presence
of an actual central unit forces the five actual squares to be one
aligned cross: each ring square shares a whole side of the central
unit, and consecutive ring squares meet at a central vertex.

For clarity, the equality statement uses no boundary hypothesis.
Its proof is Sections 1--2 of
`FOUR_CYCLE_THREE_BOUNDARY_HOLE_EMPTY.md`; the three-boundary hypothesis
is used only in that source's Section 3. The same degree-free export
is stated and justified in Section 2 of
`CHORDED_HEXAGON_CENTRAL_CAPACITY_ONE.md`.

In detail, if the four unchanged contact-chord lengths are ell_i,
the free area satisfies

    area <= sum_i [ell_i^2/4
                     -sqrt(max(ell_i^2-1,0))/2] <=1.

Every summand reaches 1/4 only at ell_i=1. An enclosed unit forces
all four lengths to equal one and equality in the polygon area
inequality. Hence the contact polygon is a unit square. Its interior
has zero area occupied by the four ring squares. Each original chord
must lie on a ring side, and its length one makes it that complete
side. Each ring unit lies on the exterior side of the contact polygon.

Coincident contacts do not supply an exception. An opposite coincidence
gives retraced segments with zero winding; an adjacent coincidence
gives a triangle of area at most sqrt(3)/2<1. At a weak junction, first
retain a compact inner square of the alleged central unit, then shrink
the compatible routing disks. Its winding and full unit-area assignment
persist in the limit. These are the exact existing physical-ring
arguments, with no prescribed new shared mean.

## 3. Two opposite boundary units already force R^2=5/2

Suppose, for contradiction, that a central unit exists. Use the common
frame of the forced actual cross but keep the circle origin unchanged.
Let (x,y) be the central unit's center. Relabel and rotate the cross
so the two prescribed opposite boundary centers are

    (x-1,y), (x+1,y).

For an aligned unit centered at (u,v), the largest squared corner norm
about the original origin is

    M(u,v)=(|u|+1/2)^2+(|v|+1/2)^2.                     (1)

The two physical boundary equalities give M(x-1,y)=M(x+1,y)=R^2.
Strict monotonicity of t -> (t+1/2)^2 for t>=0 yields
|x-1|=|x+1| and hence x=0. Therefore

    R^2=y^2+|y|+5/2.                                   (2)

The other two actual ring centers are (0,y-1),(0,y+1). The farther
one has absolute vertical coordinate |y|+1, so its containment and
(1) give

    y^2+3*|y|+5/2<=R^2.                                (3)

Comparing (2),(3) gives |y|=0. Thus x=y=0 and R^2=5/2,
contrary to the theorem's sole radius exclusion. The whole bounded
free region is empty of additional units.

The exact exception is real: the aligned central unit and its four
side neighbors at the origin fit in radius sqrt(5/2). The proof does
not claim emptiness at that radius.

## 4. Six literal original hexagon load domains get empty central regions

The accepted outer-hexagon cover fixes its actual rim as 012345 and
retains all positive chords. Its complete bounded face list and the
physical assignment of every central extra to a bounded face are
already proved in `CHORDED_HEXAGON_CENTRAL_CAPACITY_ONE.md`.

For the following original full load orbits, every nontriangular
bounded face has two opposite physically boundary vertices:

| Original load family | Actual four-faces | Opposite boundary vertices |
|---|---|---|
| M6.B6.HEXAGON.D03.L024 | 0123; 0345 | 0,2; 0,4 |
| M6.B6.HEXAGON.D03.L0124 | 0123; 0345 | 0,2; 0,4 |
| M6.B6.HEXAGON.D0203.L1235 | 0345 | 3,5 |
| M6.B6.HEXAGON.D0204.L0135 | 0234 | 0,3 |
| M6.B6.HEXAGON.D0204.L1245 | 0234 | 2,4 |
| M6.B6.HEXAGON.D0235.L0134 | 0235 | 0,3 |

All other bounded faces in these rows are triangles, whose unit
capacity is zero by the same ring-area theorem. The original radius
window has R>2, so R^2 differs from 5/2. Consequently all three actual
completion squares in each listed nine-square domain must be exterior.

This is an entire-domain allocation theorem, not a whole-family
exclusion. The exterior joint capacity remains to be proved. No
original fine gate or coarse cell is closed by this consequence alone.
In particular the full D0235.L0134 sibling is not excluded by merely
emptying its central face.

## 5. Exact operative source pins

| Source | SHA256 | Use |
|---|---|---|
| CONTACT_RING_HOLE_AREA.md | 50034e7eabf4812c6a9f87a801f07dabe7a444d723c62fdc63d096c6ceb0ec6f | Full area and winding theorem |
| FOUR_CYCLE_THREE_BOUNDARY_HOLE_EMPTY.md | f4995aed33273c00c6695d96ff0a6a3b2723779784fcd719f29d9f40e047a752 | Sections 1--2 only: full occupied-ring equality and weak junctions |
| CHORDED_HEXAGON_CENTRAL_CAPACITY_ONE.md | 0b787eae6efe36d2ca6c40dbb079d3262192125fffe58026bacbfd657d1a9a34 | Literal face list and whole central routing |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Original graph and load labels |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | Common physical embedding and weak-junction convention |

The complete mathematical proofs of the first three inputs were
reread for this reconstruction. Every square, chord force, true
degree, contact mean, circle mask, and completing unit remains.
There is no numerical pose search, Lean compilation, CI, ledger
edit, or remote write in this manuscript.
