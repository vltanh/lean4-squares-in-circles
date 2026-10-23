# Three unrestricted core and ring count cases

Let eleven pairwise open-interior-disjoint unit squares lie in a disk
centered at the origin with squared radius `q<=49013/10000`. Their frames
are arbitrary. Partition their centers at `r_*=41/40`: a core center has
norm `<r_*`, and a ring center has norm `>=r_*`.

The complete necessary count list is

| Core count | Ring count |
| ---: | ---: |
| 3 | 8 |
| 4 | 7 |
| 5 | 6 |

This follows from two independent geometric restrictions:

- [RATIONAL_CORE_RADIUS.md](boundary/RATIONAL_CORE_RADIUS.md) gives at
  least three core centers. Each ring square occupies a connected arc
  longer than `7/10` on the circle of radius `27/20`, and nine such arcs
  exceed its angular budget.
- [FIVE_CORE_CENTER_BOUND.md](boundary/FIVE_CORE_CENTER_BOUND.md) gives
  at most five centers even in the closed radius-`41/40` disk. Its proof
  first uses [SIX_CORE_CENTER_BOUND.md](boundary/SIX_CORE_CENTER_BOUND.md)
  to obtain a unique origin-containing square in a hypothetical six-core
  family. Necessary center distances pin that square's center within
  `3/40`; five neighbors then cannot fit in the four available regions
  outside its radius-`1/2` offset.

The detailed circle-contact and cyclic-order conclusions of
[CORE_RING_FOUR_CASES.md](CORE_RING_FOUR_CASES.md) apply unchanged to these
three surviving rows. Every core square is strictly inside the containing
circle, even at a closed center-threshold endpoint. Every ring center ray
lies strictly inside its connected radius-`27/20` circle arc. The ring
therefore has an actual cyclic order with consecutive arcs disjoint in
angular interior and each arc longer than `7/10`.

For a compact finite cover, allow assigned core center norms `<=41/40`
and assigned ring center norms `>=41/40`; the strict partition above
supplies a covering assignment. The overlapping threshold charts preserve
the same at-most-five theorem, strict circle-unloaded core property, and
all original geometry.

This note supersedes the four-row count list after a genuine exclusion of
its six-core row. The older five-row list used a different threshold and
remains a historical reduction. No central square is assumed in a general
eleven-square configuration: one was deduced only in the now-excluded
six-core case.

All eleven square frames, all forty-four corner containment inequalities,
and all fifty-five pair constraints remain required. The three count rows
are necessary alternatives, not solved terminal cases or realizability
claims. A complete unrestricted lower bound still has to exclude or
sharply solve all three rows, including every physical core-to-ring
completion. The construction's global sharpness and equality classification
remain unproved by these reductions.
