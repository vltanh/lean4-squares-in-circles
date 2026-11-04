# A common point for narrow ring sectors

Let `U = 49013/10000`. A unit square is contained in the disk of squared
radius `U`, and its centre has norm at least `11/10`. If its intersection
with the circle of radius `5/4` lies in a closed sector of angular width
`27/20` radians, then the point at radius `3/2` on the sector's bisector
lies strictly inside the square.

The hypotheses apply to every ring in the remaining four-core case once
the separate shell exclusion has proved that ring centres exceed `11/10`.
The statement below does not itself prove that shell exclusion.

## Exact finite certificate

`SECTOR_POINT135_COVER.json` is a closed two-dimensional box cover, replayed
by `check_sector_point135_cover.py`. It has 4079 nodes and 2040 leaves:
1061 prove strict common-point containment, 24 lie below the centre-radius
threshold, 14 violate canonical coordinate order, and 941 violate disk
containment. Maximum depth is 28. The replay imports the interval arithmetic
in `sector_point135_bounds.py` and the existing `exact_arcs.py`; it imports
neither the generator nor any optimizer. All proof arithmetic is rational.

Put the sector bisector on the positive horizontal axis. Rotations and
reflection across that bisector preserve the assertion and the candidate
point `(3/2,0)`. In the square's own frame we may therefore take its centre
as `(a,b)` with `a ≥ b ≥ 0`. Its full closed domain is

`a²+b² ≥ 121/100`, `(a+1/2)²+(b+1/2)² ≤ U`.

Both coordinates are less than `7/4`, so the cover starts with the square
`[0,7/4]²`. Every non-discarded terminal box has `a ≥ 3/4`, hence the upper
first-coordinate face lies at or beyond the test circle's radius.

Write `r=5/4` and let `[l,u]` be the circle arc's angle interval in the
square's own frame. Its endpoints are

`A = acos((a−1/2)/r)`,

`l = max(−A, asin((b−1/2)/r))`,

`u = min(A, asin(min(1,(b+1/2)/r)))`.

These follow directly from the two coordinate intervals. The connectedness
lemma in `RING_CIRCLE_GAP_CAPACITY.md` ensures that this is the complete
positive-length arc. If the own frame is rotated through angle `ψ` from
the sector frame, fitting the arc inside the sector requires

`−27/40−l ≤ ψ ≤ 27/40−u`.

The radial direction of the square centre belongs to its arc. Indeed,
centre radius `ρ` satisfies `3/4 < ρ < 7/4`, and therefore its inscribed
radius-`1/2` disk contains the test-circle point on that radial ray. The
own-frame radial direction is in `[0,π/4]`. Consequently every admissible
rotation also satisfies

`−27/40−π/4 ≤ ψ ≤ 27/40`.

For each terminal box, the checker obtains a closed rational interval
containing all possible `ψ` from these formulas. It then bounds the
own-frame coordinates of `(3/2,0)`, namely

`((3/2) cos ψ, −(3/2) sin ψ)`.

It verifies that both coordinate intervals lie strictly inside the
coordinate intervals of every square represented by that box. The
arcsine/arccosine bounds use `exact_arcs.py`. Sine and cosine use twelve
terms of their alternating Taylor series on `|ψ| < 3/2`, with the next
term bounding the remainder; outward rounding is rational. Sine is
monotone on this angle interval, and cosine extrema follow from the
smallest and largest absolute angle. Each midpoint split includes its
shared boundary in both children, so no equality case is omitted.

## Consequences for two or more rings in one gap

Two unit squares with disjoint interiors and centre norms at least `11/10`
cannot have their two test-circle arcs contained in any closed sector of
width `27/20`: both squares would contain the same interior point.
Their combined enclosing angular span is therefore strictly greater than
`27/20`.

Together with the independently certified single-ring width `63/100`,
this improves the capacity of a complementary core gap. If a gap of
length `g` contains `k` ordered ring arcs, group consecutive arcs into
`floor(k/2)` disjoint pairs and, when `k` is odd, one singleton. The paired
spans occupy disjoint subintervals of the gap. Thus

`g ≥ 63/100` for `k=1`, and

`g > (27/20)*floor(k/2) + (63/100)*(k mod 2)` for `k≥2`.

The first thresholds for `k=1,...,7` are consequently
`0.63, 1.35, 1.98, 2.70, 3.33, 4.05, 4.68`; all except the singleton
threshold are strict. Summing the resulting capacities over the cyclic
gaps is a necessary condition for extending four cores by seven rings.
No universal bound on that total capacity is claimed in this note.

Run `python check_sector_point135_cover.py` with the two arithmetic modules
installed alongside it. The generator `generate_sector_point135_cover.py` is
provided for reproducibility and is not a proof input.
