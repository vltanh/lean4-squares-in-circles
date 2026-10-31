# Independent review: spanning K2,3 leaf blocks and the radius-free book obstruction

Date: October 25, 2026. Reviewer: root, independently of `abc_review`.

**Verdict: PASS** for the complete sources
`SPANNING_K23_LEAF_BLOCK_EXCLUSION.md` and
`NO_THREE_PAGE_BOOK_SUBGRAPH.md`. The former excludes four entire
five-body graph types with a genuine leaf at any root, while keeping
every additional positive chord. The latter is a separate radius-free
forbidden-subgraph theorem. Neither introduces a scalar certificate.

## 1. Genuine exterior access is preserved

I read the original selected physical embedding theorem, including its
simultaneously preserved circle spokes and arbitrarily small routing.
A physically boundary vertex is on the unbounded face even if its
circle multiplier is zero. A genuine leaf has positive circle load
by its real one-force balance. Its degree-one vertex has just one
incident face, so its bridge and root are on that same unbounded face.
This reasoning uses the actual leaf; an arbitrary edge to a boundary
vertex would not suffice.

Deleting drawing edges preserves access to infinity. Consequently both
the root and every physically boundary member remain exterior in the
retained K2,3. This is a topological subgraph restriction only: no force
equation of the full component is replaced by a smaller-degree equation.

## 2. Four-ring equality is valid without load or degree premises

I separately read `CONTACT_RING_HOLE_AREA.md` and the full
`FOUR_CYCLE_THREE_BOUNDARY_HOLE_EMPTY.md`. The latter's first two
sections prove the required equality statement before using its
three-boundary hypothesis. The new source reproduces those steps.

An enclosed original unit contributes its entire open unit area, because
the original contact chords and their homotopies avoid its interior.
Winding is first preserved at its center, then on its entire connected
open interior. Coincident applications give retraced segments or a
triangle of area at most `sqrt(3)/2`, so cannot enclose that unit area.
For four distinct applications the original center/contact ring is
Jordan and the limiting contact polygon has only winding zero or one.

The exact scalar chord contribution
`x/4 - sqrt(max(x-1,0))/2` reaches `1/4` only at `x=1`.
Equality of the full free-area chain forces all four chord lengths to
be one and polygon area one. The finite Fourier polygon inequality has
only its first positive mode at the maximal ratio; equality therefore
makes the polygon a unit square. No occupied ring area may lie inside
it. Each chord is a full boundary side of its actual ring unit, and
that unit lies outside the polygon. The enclosed unit is the polygon
itself. This is the exact aligned five-square cross, including weak
junctions and original shared means. No initial common frame is assumed.

## 3. Exact circle comparison and the radial-root contradiction

For the forced cross centered at `(x,y)`, I independently used
`M(a,b)=(|a|+1/2)^2+(|b|+1/2)^2` for each actual corner maximum.
Two opposite boundary members force the transverse coordinate to be
zero; containment of the remaining opposite pair forces the other
coordinate to be zero. Thus `R^2=5/2`, below the declared window.

With two adjacent boundary members, comparison with their contained
opposites gives `x,y>=0`, after relabeling them right and top. Equality
of their two corner maxima gives `x=y=t`. Their common squared radius
is `2t^2+4t+5/2`. Since its value at `2/5` exceeds `1105/256` by
`663/6400`, one has `t<2/5`. Every point of either clear ring member
then has norm greater than `1/10`.

The complete radial-bridge source makes the actual leaf root physically
circle-clear and puts a point of it in radius `max(R-2,0)`. The identity
`(25/12)^2-1105/256=55/2304` gives that radius strictly below `1/12`.
Thus neither clear ring member can be the genuine leaf root. The other
two are boundary and cannot be that root either. The proof needs neither
the leaf's S/D subdivision nor any equation at a truncated block vertex.

## 4. K2,3 topology and all original rooted types

Every plane K2,3 has a simple outer four-cycle containing both hubs and
two pages; the third page is strictly inside. All its physical boundary
members and its genuine leaf root must belong to that outer cycle by
Section 1. With at least two boundary members, the enclosed third page
contradicts the cross-and-root obstruction just reviewed.

The graph/load cover gives at least three circle-loaded bodies for the
whole six-body component. The genuine leaf is one and its root is clear,
so at least two of the five block bodies are physically boundary. This
establishes the required count for this exact application. The source
explicitly does not transfer that count to an arbitrary larger subgraph.

The displayed spanning subgraphs are exact: K2,3 itself; the book with
extra hub edge; subdivided K4 with hubs A,B, pages C,D,X and extra CD;
and the wheel with opposite rim hubs 0,2, pages 1,3,H and extra H1,H3.
Every possible root is retained in its spanning K2,3. Thus all four
graph types and every S/D leaf pose are excluded with all three original
completion squares still present. The seven previously open whole
rooted types close; the C5, three house, and three fan root types remain.

The 34 exact existing obligations in the source were checked against
the unchanged roadmap. Five overlap the separately reviewed boundary-hub
diamond result and are counted only once. Together with its three
two-tip-diamond obligations, the union discharges 37 existing labels.
This leaves C1.5.b1 with nine of sixteen whole rooted types closed,
seven open, and 23 necessary block-load orbits. No coarse cell closes
from this assembly alone.

## 5. The separate radius-free three-page-book theorem

`NO_POSITIVE_K4_SUBGRAPH.md` supplies the genuine no-enclosed-center
result for every embedded positive three-cycle, independently of radius.
Its bounded interior contains no graph edge either: a simple graph
cannot add another edge between the triangle's three existing vertices,
and any other edge there would need another vertex or cross its boundary.
Therefore each positive triangle bounds an empty bounded face.

An edge has two local sides and at most one face on each side. Distinct
common neighbors give distinct bounded triangular faces containing it,
so there are at most two. A three-page book would give three. This proof
retains arbitrary true degrees, all extra positive forces, and all zero
circle weights at its vertices. It uses the already selected physical
graph and does not add unselected zero-stress edges.

## 6. Retained limits

All conclusions concern the original selected certificate. The radial
leaf must be genuine; a long bridge arm is not contracted into it.
Neither source adds a secondary minimizer or changes actual normals.
The unrestricted radius theorem, equality classification and remaining
coarse cases still require their original proofs and prerequisite audits.
No Lean compilation, CI or workflow dispatch was used.
