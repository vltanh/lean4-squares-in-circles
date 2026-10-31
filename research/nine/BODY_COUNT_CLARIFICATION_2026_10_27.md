# Interpreting 6–9-body cyclic cases in the n=9 proof

Date: October 27, 2026. Basis: accepted PR #11 checkpoint `50c0cd6`.
This note explains the inventory; it proves no additional gate and changes
no accepted checkbox.

## One nine-square problem, not four old optimization problems

The packing always has **nine actual unit squares**. A chosen sparse,
torque-balanced contact certificate has one connected **positive-force
component** with `m` participating squares. The remaining `9-m` squares are
still part of the same packing. They may make physical contacts of zero
selected force, and their possible circle touches are retained.

A six-body row means `m=6` and **three more squares** to place. It is not
the separately proved optimum-packing theorem for six squares. The latter
cannot simply be transplanted to the former: the radius window, global
certificate, contact features and nine-square completion requirement differ.

For each row the selected positive graph has a tree of nontrivial cyclic
blocks of sizes `k_1,...,k_t` and `b` selected bridges. The block-cut count
is

`m = 1 + sum_i (k_i - 1) + b`.

Examples:
- `C1.4.b2`: one four-vertex block plus two bridges, `m=4+2=6`;
  three extra physical squares remain.
- `C2.33.b2`: two triangle blocks plus two bridges,
  `m=1+2+2+2=7`; two extra physical squares remain. This row is closed.
- `C3.333.b2`: three triangles plus two bridges,
  `m=1+2+2+2+2=9`; no additional squares. This row is closed.

## Exact accepted open counts at the checkpoint

| Positive component bodies | Extra physical squares | Open coarse cells |
|---:|---:|---:|
| 6 | 3 | 3 |
| 7 | 2 | 7 |
| 8 | 1 | 11 |
| 9 | 0 | 18 |
| **Total open** | | **39** |

There are **19 closed coarse cells of 58**, including cells with fewer
positive bodies. Independently, the historical fine checklist has
**2,271 checked IDs of 2,513**, with 242 unchecked. Neither counter is
a percentage of the mathematical proof.

Exactly the three open six-body coarse rows are `C1.4.b2`, `C1.5.b1`,
and `C1.6.b0`. Closing their *entire original continuous domains* does
not alone close their seven-, eight- and nine-body extensions. A useful
common geometric exclusion should retain all original positive neighbors,
forces, application-point means, physical contacts, and completion squares,
rather than discarding them to invoke a smaller-body theorem.

For each open coarse row, the unchanged proof contract is: exhaustive
graph and load cover; exact all-frame geometry; completion with all
`9-m` physical units; strict sharp exclusion or a retained equality
branch; then the equality audit and Lean formalization. See
`CYCLIC_CELL_LEDGER.md` and `DEEP_GATED_ROADMAP.md`.

## Status of the October 25 candidate supplement

`TWO_LEAF_CONNECTED_BOUNDARY_BLOCK_EXCLUSION.md` is an author-checked
**draft**, not an accepted universal closure. It treats two genuine
radial leaves at one hub, at least one of type S, when all other loaded
boundary neighbors of the hub lie in one connected physical contact graph.
It leaves DD, disconnected groups and any unverified application open.
Its companion `TWO_LEAF_CONNECTED_BOUNDARY_CHECK.py` passes 24 exact
strict comparisons plus nine identities but does not certify the geometry.
No accepted gate count is changed without independent review.

The global nine-square sharp bound `R^2 >= 1105/256`, its complete
equality classification, dependency audit and Lean integration remain open.
