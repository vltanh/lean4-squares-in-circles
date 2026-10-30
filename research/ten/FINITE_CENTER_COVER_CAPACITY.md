# A common completion-capacity criterion for arbitrary core patterns

**Status:** reviewed exact general geometric criterion; root and independent
mathematical reviews passed on 2026-10-30.
This introduces no new case count or progress denominator. A whole
signature is excluded only after every realization has been reduced to
the stated certificate hypotheses.

The criterion depends on positions of existing square centers, not on
their circle-load count, graph degrees, or square orientations. It can
therefore be applied to any of the remaining finite cycle signatures.

## 1. Cover by excluded cells and small remaining regions

Consider m specified unit squares in a packing contained in a disk of
radius `R≤3/sqrt(2)`. Let their centers be `c_1,...,c_m`. Suppose:

1. Each `c_i` belongs to a specified compact convex polygon K_i.
2. A polygon P contains the disk of radius `25/16` about the origin.
3. P is covered by finitely many excluded compact convex polygonal cells E_j and q
   remaining regions H_1,...,H_q.
4. Each excluded cell E_j has an assigned core index i(j), and
   `|v−w|²<1` for every vertex v of E_j and every vertex w of K_i(j).
5. Each H_k is a finite union of convex polygons. Every pair of vertices
   from all its constituent polygons has squared distance strictly below 1.

**Theorem.** At most q further unit squares can be added. The total
packing size is at most `m+q`.

Every square center has norm below 25/16, by the universal center bound,
so it belongs to P. Distinct square centers have distance at least 1:
their open inscribed disks of radius 1/2 have disjoint interiors.

For an excluded cell, convexity of squared distance first in one
argument and then in the other extends condition 4 to every point of
E_j and every allowed actual core center. Thus no additional center
can belong to E_j.

Condition 5 places each H_k inside a convex hull of diameter strictly
below 1. Indeed, squared distance between two convex combinations is
bounded above by the maximum squared distance between their generating
vertices. Hence no H_k can contain two distinct added centers.
Assign each added center to any H_k containing it. The assignment is
injective, proving the bound. Overlap between cover cells or between
remaining regions causes no difficulty.

For an n=10 exclusion it suffices to prove `q≤9−m`. The full square
orientations need not be recovered once the center-region hypotheses
are established.

## 2. Exact finite verification

All data may be rational. It is enough to check polygon containment,
coverage, the assigned vertex-pair distances in condition 4, and the
within-region vertex-pair distances in condition 5. Each of these is
a finite exact calculation; no optimizer is a premise.

Two useful coverage constructions already have examples in this research:

* A complete finite quadtree subdivision of an outer polygon, with each
  cell assigned either to one existing center or to a remaining region.
* Nearest-midpoint polygons for the K_i, intersected with the exterior
  of prescribed remaining regions. The nearest-midpoint polygons cover
  P because every point has a nearest midpoint; ties may be included
  in every applicable cell.

The first construction is used in
[SIX_BODY_CENTER_COVER.md](SIX_BODY_CENTER_COVER.md), with q=0.
The second is used in
[SEVEN_BODY_CENTRAL_HOLE_EXCLUSION.md](SEVEN_BODY_CENTRAL_HOLE_EXCLUSION.md).
The next corollary extracts its orientation-independent capacity bound.

## 3. Seven center regions already imply total capacity at most eight

Suppose seven distinct unit-square centers lie in the following regions,
with no orientation hypotheses on any of those squares:

```text
A: [−1.55,−1.54]×[−0.16,−0.15],
B: [ 1.54, 1.55]×[−0.16,−0.15],
C: [−0.01, 0.01]×[ 1.40, 1.42],
U: {(-1/2,-1)},             V: {(1/2,-1)},
S: [−0.75,−0.74]×[0.74,0.75],
T: [ 0.74, 0.75]×[0.74,0.75].
```

These are exactly the regions of the rational 28-cell cover in
[seven_body_central_hole_cover.json](seven_body_central_hole_cover.json).
Its largest assigned squared-distance bound is `197/200<1`. Therefore
all added centers belong to

```text
H=(−1/5,1/5)×(−1/5,1/10).
```

The closure of H has squared diameter

```text
(2/5)²+(3/10)²=1/4<1.
```

Apply the theorem with m=7 and q=1. The total packing has at most eight
squares. This conclusion needs neither the axis-parallel SS-row geometry
nor the 45-degree upper diamonds used for the stronger no-eighth-square
result in the cited note. It uses only the seven center regions and
the containing radius.

## 4. What remains to make this a shared whole-case argument

A numerical core may suggest useful regions, but it does not establish
condition 1 for another realization. The missing step is to derive
uniform center regions from geometric restrictions common to the
remaining cycle signatures, with finitely many parameter families when
necessary. Such families may retain arbitrary circle-load splits,
endpoint orientations, and transmitter slides. Every family must have
its own complete cover certificate or a single cover valid uniformly
over that family's center regions.

This criterion is independent of the number of loaded bodies. It does
not by itself assert that the existing signatures satisfy any particular
center boxes, nor does it promote either numerical component candidate
to an exact realization theorem.
