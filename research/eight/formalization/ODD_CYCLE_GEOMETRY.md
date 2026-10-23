# A short odd-cycle proof of the four-type walk bound

## Implemented replacement

`SquaresInCircles/Eight/Frames.lean` now proves
`four_type_seven_walk_numerator` by alternating vertex potentials. The
previous proof evaluated the proposition for all `4^7 = 16,384` label words.
The replacement checks 32 integer inequalities for the sixteen directed
matrix entries, then adds seven inequalities. It is an uncompiled Lean
source replacement, not a measured compilation result.

The continuous four-type pair bounds are unchanged. This argument proves
the weighted-graph statement used after those geometric bounds have been
established; it does not prove a pair inequality for actual squares.

## Proof

The four types are C, L, M, H, and the matrix of integer edge weights is

| | C | L | M | H |
|---|---:|---:|---:|---:|
| C | 9200 | 9100 | 9005 | 8833 |
| L | 9100 | 9100 | 9005 | 8833 |
| M | 9005 | 9005 | 8912 | 8926 |
| H | 8833 | 8833 | 8926 | 9099 |

Subtract the common baseline 8833 from every edge. Give each vertex two
potentials, according to its parity along a walk:

| Type | Even potential E | Odd potential O |
|---|---:|---:|
| C | 265 | 0 |
| L | 265 | 0 |
| M | 172 | 93 |
| H | 0 | 265 |

Direct comparison of the sixteen entries gives, for every pair of types,

\[
w(i,j)\ge 8833+O(j)-E(i),\qquad
w(i,j)\ge 8833+E(j)-O(i).
\]

Follow any closed walk of length seven. Use the first inequality on even
edges and the second on odd edges. All intermediate potentials cancel,
leaving

\[
\sum w\ge 7\cdot8833+O(i_0)-E(i_0).
\]

Interchanging the two parities gives the same statement with E and O
exchanged. If the walk contains a C, L, or H vertex, start there and choose
the parity that leaves a positive difference. The difference is 265, so

\[
\sum w\ge 7\cdot8833+265=62096.
\]

If every vertex is M, the sum is instead `7·8912 = 62384`, which is larger.
This includes loops, repeated labels, and all closed walks without listing
the words.

The bound is exact as a weighted-graph statement: the word
`H,C,H,C,H,M,M` has cost

\[
4\cdot8833+2\cdot8926+8912=62096.
\]

This word is only a sharpness witness for the graph calculation; no
geometric realization of it is asserted.

## Validation and scope

An exact integer check confirmed the 32 edge inequalities and the two final
integer sums. The smallest edge slack is zero. No complete word enumeration,
Lean compilation, CI, or certificate execution was run. The proof script
uses `norm_num` for the small edge comparisons and linear arithmetic for
telescoping. It removes the global `by decide` search and its unbounded
heartbeat setting from this theorem.
