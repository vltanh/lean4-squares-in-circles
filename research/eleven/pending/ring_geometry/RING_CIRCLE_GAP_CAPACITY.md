# Connected ring arcs and the cyclic gap capacity condition

Assume every unit square lies in the disk of squared radius
`U = 49013/10000`, and square interiors are pairwise disjoint. A ring square
has centre norm at least `r0 = 41/40`. Use the test circle of radius
`r = 5/4`. Equalities at the core threshold are harmless for these lemmas.

## Every ring square cuts one nonzero connected arc

Rotate and reflect into the square's own coordinates and write its centre
as `(c,d)`, where `c ≥ d ≥ 0`. Then the square is
`[c−1/2,c+1/2] × [d−1/2,d+1/2]`. Since
`2c² ≥ c²+d² ≥ (41/40)² > 1/2`, we have `c > 1/2`.
Thus all its points have positive first coordinate, and all circle
intersection points have a unique angle `θ ∈ (−π/2,π/2)`.

The second-coordinate restriction gives an interval of angles, since
`sin θ` is increasing there. The lower first-coordinate restriction also
gives an interval: `cos θ ≥ (c−1/2)/r`.

Only the upper first-coordinate restriction can potentially disconnect
that interval. If `c+1/2 ≥ r`, it imposes no restriction. Otherwise
`c < 3/4`. The core threshold then forces `d > 1/2`, because
`d ≤ 1/2` would give `c²+d² < 9/16+1/4 = 13/16 < (41/40)²`.
Hence the second-coordinate restriction forces `θ > 0`. On these positive
angles `cos θ` is decreasing, so `cos θ ≤ (c+1/2)/r` again gives an
interval. In all cases the circle intersection is connected or empty.

It is nonempty and has positive length. Writing `ρ = sqrt(c²+d²)`, the
farthest vertex bound gives

`ρ² + ρ + 1/2 ≤ ρ² + c+d + 1/2 ≤ U`.

This implies `ρ < 7/4`, while `ρ ≥ 41/40 > 3/4`. Thus
`|ρ−5/4| < 1/2`, and the radius-`1/2` disk inscribed in the square meets the
test circle in a positive arc. Consequently each ring square cuts exactly
one connected, positive-length arc.

## Exact uniform arc width

`RING_WIDTH_COVER.json`, replayed by `check_ring_width_cover.py`, proves that
every such ring arc has angular length at least `63/100` radians. The
checker uses only Python integer/rational arithmetic and the existing
`exact_arcs.py` bounds. It does not import the generator or an optimizer.

In own-frame coordinates the full closed domain is

`0 ≤ d ≤ c ≤ 7/4`, `c²+d² ≥ (41/40)²`,
`(c+1/2)²+(d+1/2)² ≤ U`.

The cover has 915 nodes, 228 arc leaves and 230 discarded leaves; maximum
depth is 22. Each discarded box violates one displayed domain condition
by a strict exact inequality. At each arc leaf, the checker takes the
rectangle contained in every square represented by the box and proves
its circle-intersection length at least `63/100`. Midpoint splits cover
both children with their shared boundary retained. The whole closed
domain is therefore covered, including ties.

When the files are installed together, run:

`python check_ring_width_cover.py`

The generator `generate_ring_width_cover.py` is a reproducibility helper,
not a proof input. Both the complete cover and the replay are deterministic.

## Necessary gap capacity condition for seven rings

For each of four core squares, take the positive-length components of its
intersection with the test circle. Let `B` be the union of their closures;
ignore isolated tangency points, which have zero length. Merge touching
components. Let `g_1,...,g_m` be the angular lengths of the complementary
cyclic gaps. If `B` is empty, use one gap of length `2π`. If `B` is the
entire circle, use no gaps.

A ring arc cannot cross the interior of a core arc: a positive circle arc
shared by two squares would contain a point interior to both squares,
since each square boundary meets a circle in only finitely many points.
Thus each connected ring arc lies in the closure of a single gap, up to
endpoints. The same argument makes distinct ring arcs disjoint in angular
interior. A gap of length `g_j` can therefore hold at most
`floor(g_j/(63/100))` ring arcs. Seven ring squares require

`sum_j floor(100*g_j/63) ≥ 7`.

In particular, any four-core configuration for which this sum is at most
six cannot extend to an eleven-square packing at squared radius `U`.
This is a necessary condition only. No universal four-core bound on this
sum is claimed here; proving or finitely classifying that bound is an
additional gate.
