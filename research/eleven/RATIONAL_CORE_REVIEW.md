# Independent review of the rational-radius four-case reduction

Reviewer: the `n8_lessons` research agent, independently of the author of the
two arc/count manuscripts. This is a mathematical source review, not Lean
kernel verification.

Reviewed source snapshots:

- `boundary/RATIONAL_CORE_RADIUS.md`: SHA-256
  `9689dcc4981ebe051b4387716bf1fedb6de0b7f66c74e45a28bffec178fa4177`.
- `boundary/SIX_CORE_CENTER_BOUND.md`: SHA-256
  `aefbbcd689784029604e5a0c827bc2b94b8aa5aad6537d5850ed5a66bffa4a3e`.
- `CORE_RING_FOUR_CASES.md`: the combined extraction written in this review.

The rational-radius arc proof passes. I checked the own-frame reduction,
the near-corner interior bound, the extra far-side branch when `A<rho`, and
that all four endpoint differences really are included. The near- and
far-side derivative factorizations have the stated signs on their full
comparison paths. The rational Taylor residues were independently recomputed
with exact fractions as `1698553901/1280000000000` and
`2639837/2560000000`. Endpoint tangencies and threshold equality are included;
nine qualifying arcs give a strict angular-budget contradiction.

The six-center bound passes. The unit-circle arc formulas remain valid at
`a=1/2` and at side tangencies. The near-side derivative comparison may pass
through an origin-containing hypothetical square at the diagonal, but all
radicals remain positive and the comparison function stays defined, so this
does not restrict its validity. The near-side length is strictly above
`pi/3`; equality of the actual arc therefore forces the parallel-strip
case with `b=0`. Six such arcs must tile the circle with center-ray gaps
`pi/3`. I checked all four unsigned own-axis projections of consecutive
squares: the bounds `31/40<1` and `41sqrt(3)/80<1` exclude every separating
axis because each required support distance is at least one. Thus at most
five origin-avoiding squares, plus at most one origin-containing square,
are possible in the closed center disk.

The combined extraction preserves the radius window and the actual squares.
It uses only those two lemmas, area, the farthest-corner center bound, and the
inscribed disk. All core squares are circle-unloaded even at the closed
threshold; every ring center ray lies strictly inside its auxiliary arc.
The four rows are an exhaustive necessary cover. No row is thereby solved
for the desired sharp unrestricted radius, and no candidate optimality or
orientation classification follows from these counts.
