# Four core centers force every other center beyond 6/5

Assume eleven unit squares with disjoint interiors fit a disk of squared
radius at most \(U=49013/10000\). If four centers have radius at most
\(41/40\), then every other center has radius strictly greater than \(6/5\).
This strengthens the earlier \(11/10\) empty-shell theorem. It does not
eliminate the four-core branch.

As proved in `WEIGHTED_ARC_EXCLUSION.md`, there cannot be five centers at
radius at most \(41/40\). Thus the hypothesis leaves exactly seven ring
centers. We use a new positive weighted sum \(W\) of concentric-circle
angular intersection measures. Its radii are the following integers divided
by 20, in the listed order:

```
6, 8, 9, 11, 13, 15, 16, 17, 18, 19, 20, 21, 22, 24, 25, 26, 27, 28
```

The corresponding weights are the following integers divided by 100000:

```
4427, 2133, 1608, 11791, 194, 14736, 1004, 2536, 2824,
3126, 1987, 1643, 1603, 4453, 18670, 10064, 8320, 8881
```

All weights are positive and their sum is one. Three exact closed covers
prove:

| Center and containment condition | Weighted arc lower bound |
| --- | --- |
| \(\lVert p\rVert\le41/40\) | \(W\ge847/1000\) |
| \(41/40\le\lVert p\rVert\le6/5\) | \(W\ge133/200\) |
| \(\lVert p\rVert\ge41/40\), square contained in the disk of squared radius \(U\) | \(W\ge187/500\) |

If any of the seven ring centers had radius at most \(6/5\), these bounds
would imply

\[
\sum W\ge4\frac{847}{1000}+\frac{133}{200}+6\frac{187}{500}
=\frac{6297}{1000}>\frac{44}{7}>2\pi.
\]

The first strict difference is \(79/7000\). This contradicts the angular
circle budget \(\sum W\le2\pi\). The budget follows because square
boundaries meet each circle in finitely many points, so disjoint square
interiors imply disjoint arc interiors up to measure zero.

The cover geometry is precisely the one in `FOUR_CORE_EMPTY_SHELL.md`, with
the middle radius changed to \(6/5\). Canonical own-frame centers satisfy
\(a\ge b\ge0\). Initial boxes are \([0,41/40]^2\), \([0,6/5]^2\), and
\([0,7/4]^2\). Discard tests use strict inequalities for the diagonal,
core-radius boundary, middle outer-radius boundary, and exact farthest-corner
disk containment. Every nondiscarded terminal box certifies its lower bound
using the rectangle contained in every square in that box. All other boxes
split at an exact midpoint into two closed recorded children.

The elementary-function bounds are unchanged from `exact_arcs.py`. To keep
large weighted rational sums efficient, this certificate additionally rounds
each circle's already certified arc lower bound **down** to the grid
\(10^{-12}\), before multiplication by its positive weight. This only
weakens the lower bound. The scale is included in the certificate metadata
and checked by replay. No floating-point arithmetic is used in generation
or checking.

| Certificate | Nodes | Arc leaves | Discard leaves | Maximum depth |
| --- | ---: | ---: | ---: | ---: |
| `WIDE_SHELL_CORE_COVER.json` | 17,847 | 8,438 | 486 | 20 |
| `WIDE_SHELL_MIDDLE_COVER.json` | 857 | 307 | 122 | 18 |
| `WIDE_SHELL_RING_COVER.json` | 1,701 | 442 | 409 | 20 |

Run `python generate_wide_shell.py` to regenerate all three trees and
`python check_wide_shell.py` to replay them. The replay checks every domain
predicate, midpoint split, and all 9,187 accepted weighted arc bounds. It
imports only the audited elementary-function module, not the generator.
Both reject Python `-O` through the elementary-function guard, and the replay
also contains its own explicit guard.
