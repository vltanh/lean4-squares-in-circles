# A common-point marker on the radius-27/20 circle

Let a unit square lie in the disk of squared radius `U=49013/10000`, with
centre norm at least `11/10`. If its intersection with the circle of
radius `r=27/20` lies in a closed angular sector of width `36/25`, then the
point at radius `57/40` on that sector's bisector lies strictly inside the
square. Consequently two squares with disjoint interiors cannot have their
circle arcs contained in the same sector of that width.

This certificate is independent of the separate statement that split
core-arc internal gaps on this circle cannot contain ring squares. It
proves only the common-point assertion above.

`NATIVE_SECTOR_POINT_COVER.json`, replayed by
`check_native_sector_point_cover.py`, has 2459 nodes and 1230 leaves:
1061 strict common-point leaves and 169 discarded boxes. Maximum depth is
17. All arithmetic is rational; the replay uses
`native_sector_point_bounds.py` and the existing `exact_arcs.py`. It does
not import the generator or any optimizer.

Place the sector bisector on the positive horizontal axis. By choosing the
square's own frame and, if necessary, reflecting across that bisector, its
centre coordinates may be written `(a,b)` with `a≥b≥0`. The admissible
closed domain is

`a²+b²≥121/100`, `(a+1/2)²+(b+1/2)²≤U`.

Both coordinates are less than `7/4`. Every non-discarded terminal box has
`a>1/2`, and either `a≥r−1/2=17/20` or `b≥1/2`.

Write `A=acos((a−1/2)/r)`. In the square's own frame its circle arc has
upper endpoint

`u=min(A,asin(min(1,(b+1/2)/r)))`.

When `a+1/2≥r`, the lower endpoint is

`l=max(−A,asin((b−1/2)/r))`.

When `a+1/2<r`, the upper first-coordinate face also restricts the arc.
The centre-radius hypothesis then implies `b>1/2`: otherwise
`a²+b²<(17/20)²+1/4=389/400<121/100`. All its arc angles are positive,
and the correct lower endpoint is

`l=max(−A,asin((b−1/2)/r),acos((a+1/2)/r))`.

The checker retains that additional term, including boxes crossing its
activation boundary. These formulas also prove connectedness. The arc
has positive length because the inscribed radius-`1/2` disk meets the test
circle: the centre radius is at least `11/10>r−1/2`, and disk containment
implies it is less than `7/4<r+1/2`.

If the own frame is rotated by `ψ` from the sector frame, sector containment
requires

`−18/25−l≤ψ≤18/25−u`.

The radial direction of the centre lies in the arc and in `[0,π/4]` in the
canonical own frame. Thus also `−18/25−π/4≤ψ≤18/25`. This is contained in
`(−π/2,π/2)`, where sine is monotone. For each terminal box the checker
bounds the full possible rotation interval, then proves that

`((57/40)cosψ,−(57/40)sinψ)`

lies strictly inside every represented square. Exact arcsine/arccosine
bounds come from `exact_arcs.py`; sine and cosine use twelve alternating
Taylor terms with the next term bounding the remainder, followed by
rational outward rounding. Here `|ψ|<8/5`, and the actual global angle
restriction keeps sine in its monotone interval. Cosine extrema are
obtained from the smallest and largest absolute angle.

Midpoint splits retain both copies of shared boundaries. Discarded boxes
violate a displayed domain constraint by a strict exact inequality.
Therefore the entire closed domain is covered, including all ties.

Run `python check_native_sector_point_cover.py` with both arithmetic
modules alongside it. `generate_native_sector_point_cover.py` is a
reproducibility helper and is not a proof input.
