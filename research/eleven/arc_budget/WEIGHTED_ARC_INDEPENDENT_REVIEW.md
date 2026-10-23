# Independent review of the weighted-circle core exclusion

Review outcome: **PASS** for the mathematical reduction, exact arithmetic,
and complete-domain cover in the six files identified below. The result is
that an eleven-square packing with squared containing radius at most
`49013/10000` has at most four centers in the closed radius-`41/40` disk.
It excludes every configuration with five or more such centers, regardless
of individual square orientations. It does not prove the candidate radius
optimal or solve the remaining three- and four-core cases.

This review was performed independently of the author of the certificates.
It includes direct source inspection and replay with the supplied checker.
The separate implementation used by the parent researcher for a second
arithmetic replay is additional evidence, not a premise of this review.

## Mathematical reduction checked

1. A square can be expressed in its own frame with center coordinates
   `a>=b>=0`: reflections and exchange of the frame axes preserve every
   concentric-circle angular measure. The canonical pose domains in the
   manuscript are therefore exhaustive for arbitrary orientations.
2. The farthest-corner constraint is exactly
   `(a+1/2)^2+(b+1/2)^2<=U`. It implies the claimed ring root box because
   `U<81/16`, while the core root box follows directly from the center norm.
3. For a center box `[a,A] x [b,B]`, the rectangle
   `[A-1/2,a+1/2] x [B-1/2,b+1/2]` lies inside every corresponding square.
   Its arc measure is consequently a uniform lower bound throughout that
   pose box. Using a containing rectangle here would have reversed the
   necessary inequality; the code uses the correct contained rectangle.
4. In each reflected first quadrant the circle coordinates are
   `(r cos(theta),r sin(theta))`. The two maximum/minimum inverse-trigonometric
   endpoint formulas in the manuscript and source are exact. Subtracting an
   upper bound on the lower endpoint from a lower bound on the upper endpoint
   gives a safe lower arc bound, even when the actual interval is empty.
   Repeated axis endpoints have measure zero.
5. Square boundaries meet a positive-radius circle in finitely many points.
   Interior-disjointness therefore bounds the sum of their circle measures
   by `2*pi`. The positive weights sum exactly to one. Five core estimates
   and six ring estimates give `317/50>44/7>2*pi`; any additional core only
   increases that lower bound. No unproved independence or realizability of
   the individual pose minima is needed for this contradiction.

## Directed arithmetic and cover checked

The integer-square-root enclosure is checked by exact squaring. The
alternating arctangent remainder has the correct direction for both parity
cases. The Machin identity gives the stated pi bounds, and all uses of the
half-angle and complementary-angle arcsine identities select outward
endpoints. The complementary argument after the `z>3/4` branch is below
`3/4`, including the specified square-root rounding, so the recursion and
the arctangent argument bound are valid. Arccosine subtraction uses the
correct pi and arcsine endpoints.

Every rejection predicate is strict and excludes the entire relevant box
from the required closed domain. In particular, equality at the center
threshold, diagonal, or disk boundary is never discarded. Every nonterminal
node has exactly two children that cover its parent by a midpoint split.
The replay reconstructs those boxes from the root and independently checks
each rejection, rather than trusting stored box coordinates or rejection
labels. It validates the schema, parameters, weights, target bounds, root
boxes, node formats, and complete node counts. Each accepted arc leaf
recomputes its rational lower bound; no floating-point value or stored
numerical bound is trusted.

The final library and replay script explicitly reject optimized Python
execution, so `python -O` cannot silently disable their proof assertions.
The final manuscript also consistently states counts at the radius-`41/40`
threshold; it does not identify these with earlier counts at other thresholds.

The certified trees contain 4,367 core nodes and 423 ring nodes, including
1,933 and 104 accepted arc leaves respectively. These are covers of the
continuous two-dimensional pose domains, not finite samples of poses.

## SHA-256 bindings

The following names refer to the files as supplied in the `arc-budget`
directory. Renaming a file does not change its hash; modifying its contents
requires a new review binding.

| File | SHA-256 |
| --- | --- |
| `exact_arcs.py` | `ff36dd0473037002496d319d09f3e1b15c0fad3f3c576e126baa3f5f0f69db73` |
| `generate.py` | `d5f6e67b72e16f9269842a4fe7fe8eb9d08ee688d88b20e079e2d3f05c407f22` |
| `check_weighted_arc_cover.py` | `77e22501ce81e5738c57c2b894deea1c64dac6a161bb0aebfabe441df841a074` |
| `CORE_ARC_COVER.json` | `3fde0312138fb276cf09726b81aeb3780f444296142130bd02ce9334f45babaf` |
| `RING_ARC_COVER.json` | `acbd2eceb857bf93e26008640a8a536f0d5c68235afa7728ec107b519373b37a` |
| `WEIGHTED_ARC_EXCLUSION.md` | `99d7b3213a3cbfdf30e6559c765e18bf7a0d4e3ab4d2ae84fdd853b278624b88` |
