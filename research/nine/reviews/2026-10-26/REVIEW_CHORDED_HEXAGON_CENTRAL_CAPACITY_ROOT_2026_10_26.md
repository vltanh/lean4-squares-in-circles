# Root review: the entire bounded region of every chorded outer hexagon

Date: October 26, 2026.

**Decision: ACCEPT the complete eight-type central-capacity theorem.**
It closes no exterior allocation, whole graph/load orbit, original
HEXAGON parent or coarse C1.6.b0 cell by itself.

Reviewed source: `CHORDED_HEXAGON_CENTRAL_CAPACITY_ONE.md`.
Exact mathematical source pin before status-only acceptance edits:

    bf4d69e73cdb008f093b47c6e86dc3d7c767a5c0d03bd24d046aef62a314f1b8

I read the complete source, the complete original noncrossing graph/load
cover, the contact-ring winding and area scope, and the degree-free
four-ring equality proof. In the latter, the three-boundary premise is
used only after the aligned-cross equality has already been proved.

## 1. All eight original chord sets and actual face routing

The eight rows are exactly the two one-chord, three two-chord and three
triangulated types in the accepted original cover. Their face cycles
match those chord sets. A central extra's connected open interior avoids
all actual closed core units and therefore all occupied graph paths.
It belongs to one actual bounded face. Compact inner squares justify
this statement at arbitrarily small junction routings; the winding
argument then assigns its whole unit area to the face's free region.

Every positive chord is retained during this routing. Additional physical
contacts can subdivide a region but cannot let an extra's open interior
cross an occupied barrier. Thus summing capacities over all bounded
faces counts the entire central free union, including weak junctions.

## 2. The full face bounds and equality inheritance

The uniform ring theorem applies at the needed sizes three, four and
five. A triangular ring has free area at most sqrt(3)/4<1. The exact
identity cot(pi/5)^2=1+2sqrt(5)/5<2 gives a pentagonal free area less
than 15/8<2. These imply capacities zero and at most one respectively.

An occupied quadrilateral forces equality throughout the entire winding,
chord-cut and polygon-energy argument. Every contact chord has length
one, the contact polygon is a regular unit square, and each ring unit
occupies the exterior of one full polygon side. The enclosed unit is
the polygon itself. Thus all five actual units form an aligned cross.
Coincident contacts are separately excluded by their smaller area or
zero winding; no positive-area weak-junction case is omitted.

This equality argument uses no force, degree, circle load, leaf or
origin-containment premise. The later radius contradiction for a cross
with three boundary units is not imported into the new theorem.

## 3. The only potentially additive two-unit case

Only the single diameter chord 03 has two potentially occupied
quadrilateral faces. If both are occupied, align the first forced cross
with centers c0=(1,0), c1=(0,1), c2=(-1,0), c3=(0,-1). The physical
intersection of unchanged units 0 and 3 is the unique point
(1/2,-1/2). The second forced cross has the same frame because those
actual two units already have that frame. Its center must be (1,-1):
the other three local quadrants are occupied by 0, 3 and the first
central unit. Its remaining core centers are (1,-2) and (2,-1), with
their order fixed by the second face (or reversed by a global reflection).

The resulting actual core pair has squared distance 10. Every contained
unit center has norm less than 91/60 about the unchanged disk origin.
The latter follows from the minimum own-axis corner formula and

    (91/60)^2+91/60+1/2-1105/256=31/57600>0.

Thus every center pair has distance less than 91/30, whereas

    10-(91/30)^2=719/900>0.

This is a metric contradiction unaffected by the translation used to
display the two crosses. It excludes simultaneous occupancy of the two
faces without deleting the shared chord or identifying distinct units.

## 4. Complete assembly and original remaining obligations

The short-chord row has one empty triangle and one capacity-one pentagon.
The diameter row is covered by Section 3. Each two-chord row has exactly
two empty triangles and one capacity-one quadrilateral. Every triangulated
row has four empty triangles. This proves central capacity at most one
for all eight types, and zero for all three triangulations, independently
of their original load assignments.

The accepted load cover has 8+8+6+6+2+1+1+2=34 chorded load orbits.
All remain covered by the geometric theorem, but the theorem merely
forces at least two of the three completion units to be exterior (all
three for a triangulation). Higher-degree hubs and loaded chord endpoints
retain their full force systems. The full exterior bound and all non-
hexagonal six-body embeddings remain separate obligations.

The exact center and pair-distance reserves were independently checked
with Fraction arithmetic. No sampled pose, finite interval certificate,
Lean compilation, CI, remote mutation or shared-ledger edit was used in
this review.
