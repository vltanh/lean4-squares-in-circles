# Independent review of the unconditional q > 9/2 certificate

Review outcome: **PASS** for the theorem and exact finite pose-domain
certificate. Every eleven-square packing in a disk has squared radius
strictly greater than `9/2`, with independent square orientations allowed.
This improves an auxiliary global lower bound; it does not attain the sharp
candidate value near `4.9012064`.

The mathematical reduction and all new source code were inspected
independently of the author. The elementary rational arc routine is the
unchanged version already reviewed in `WEIGHTED_ARC_INDEPENDENT_REVIEW.md`.
Direct execution of `check_universal_bound.py` also passed all 2,385 nodes
and all 980 arc inequalities with the stated counts.

The five radii and five positive rational weights in the manuscript match
the generator, replay script, and data. Their weights sum exactly to one.
The individual-square pose domain is exhaustively reduced to
`a>=b>=0` and `(a+1/2)^2+(b+1/2)^2<=9/2`; the initial closed box covers it.
Only strict diagonal or containing-disk violations permit rejection. Thus
no tangent, equal-coordinate, or containing-disk boundary case is lost.

Each accepted box uses a rectangle contained in every square represented by
that box. The exact quadrant arc enclosures therefore prove a lower bound
for all its poses, rather than only for its midpoint. The replay reconstructs
both children of every rational midpoint split and recomputes every accepted
leaf's five-circle inequality. It checks all schema parameters, node formats,
and complete counts. The generator is not imported by the replay script.
Optimized Python mode is rejected by the elementary module and checker.

For a physical packing the sum of occupied angular measures is at most
`2*pi` on each circle: square boundaries have zero circle measure and their
open interiors are disjoint. The finite certificate proves the common
single-square bound `W>=23/40`. Therefore eleven squares would require

    sum W >= 253/40 > 44/7 > 2*pi,

which is impossible. The strict rational margin `253/40-44/7=11/280` is
correct and excludes the boundary value `q=9/2` as well.

The tree contains 2,385 nodes, with 980 accepted arc leaves and 213 discarded
leaves, at maximum depth 21. No numerical optimizer output is used to accept
a leaf or infer the global contradiction.

## SHA-256 bindings

| File | SHA-256 |
| --- | --- |
| `UNIVERSAL_LOWER_BOUND.md` | `b70883a3debd1a04b03c95d350a490241f43cf30e673a35802cb37eac6dea9ee` |
| `check_universal_bound.py` | `b7acd6c2f5db2d327bd079088e51a374c3fc9f54b57f3fb6599d7a542043e8a7` |
| `generate_universal_bound.py` | `ca7b849cdef954210e5926ec547ab41aeb347e76046755d26b0468dc0f0f7c0b` |
| `UNIVERSAL_BOUND_COVER.json` | `658f7e257ecfa48930290e3c73051e47461889c1a8b64528839078348f94c2d7` |
| `exact_arcs.py` | `ff36dd0473037002496d319d09f3e1b15c0fad3f3c576e126baa3f5f0f69db73` |
