# Use the full-angle positive-D row terminal before small-angle subdivision

November 4, 2026. This is an exact implementation and complete complementary
cover for an existing physical theorem. It adds **zero original-cell or
mask closures**. The current register remains **216 CLOSED / 15 OPEN**;
the mask ledger remains **8 CLOSED / 24 OPEN**. No Lean, Lake or CI.

## Physical caller and retained theorem

Keep the unchanged original-nine `001/00` caller, the normalized transverse
CD gap at least 2/3, all nine original frames, 36 corners and 36 physical
pairs, the five original center cones, actual AB, BC, EF, FG, and strictly
weak CD. In addition, prove that the original signed D frame is
nonnegative. This sign already holds on the A and D fixed families.

Sections 1–4 of
[the positive-D total-variation theorem](WEAK_OUTER_NUMERIC_POSITIVE_D_TOTAL_VARIATION_ROW_HAND_TERMINAL.md)
prove the following implication for either retained extra X=H or X=I:

\[
x_B\le x_X\le x_D,\qquad
|y_X-y_B|+|y_D-y_X|\le\tfrac12
\quad\Longrightarrow\quad\text{the original strict caller is impossible}.
\]

The theorem allows every original angle of B, X and D compatible with
D's sign and every genuine separating-axis owner. It imposes no angle
bounds on A, E, F, G or the other extra. The existing caller gives the
upward original D/G separating-axis condition used by its signed cap.
No replacement original receives a new center-cone comparison.

The weak horizontal order is sufficient. If either horizontal gap is
zero, its vertical gap is at most 1/2. The corresponding original centers
would be at distance at most 1/2, contradicting the disjoint open incircles
of radius 1/2. Thus the theorem's strict horizontal order follows.

The accepted proof also treats the closed-Q equality face: equality in
the cap and row estimates forces B,X,D aligned, and the retained original
BC and CD geometry forces C aligned with CD gap exactly one. This
contradicts the original strictly weak CD bit. A proof for radii merely
bounded away from Q is not being substituted for this argument.

## Complete six-domain complement

Fix one of the two original extras X. Define
`v=y_X-y_B` and `w=y_D-y_X`. Every failure of the row guard lies in at
least one of these six **closed** domains:

| Index | Exact conditional inequality |
| --- | --- |
| 0 | `x_X <= x_B` |
| 1 | `x_D <= x_X` |
| 2 | `-v-w >= 1/2` |
| 3 | `-v+w >= 1/2` |
| 4 | `v-w >= 1/2` |
| 5 | `v+w >= 1/2` |

This is exhaustive because
`|v|+|w| = max(-v-w,-v+w,v-w,v+w)`.
All shared equality faces are retained. If an ancestor already proves
strict horizontal order, the first two domains can be excluded directly,
leaving exactly four signed height domains. They cannot be removed from
another caller without proving the corresponding order inequalities.

The two choices of X are separate valid guards. A branch in one fixed
cover may be closed by the theorem for the other extra, provided every
hypothesis is derived there. This does not justify dropping a branch or
combining independent configurations of H and I.

## Exact guard implementation and review

The helper intersects coordinate differences with certified pair-difference
intervals, reversing `[l,u]` to `[-u,-l]` when the original pair is reversed.
It bounds each of the four signed height forms separately. For the two
telescoping forms it also uses the certified B–D difference. The sum of
the two absolute-difference upper bounds gives a second valid variation
bound; taking their minimum retains validity.

The signed D component is local scalar coordinate 12 in the retained
layout of nine alpha, nine signed beta, nine absolute beta and nine inset
variables. Its nonnegative lower bound, or a nonnegative original D slope
interval, proves the sign premise. The helper never treats an unproved
numerical state as a valid physical caller.

A separate exact evaluator and mathematical source review passed **499
rational checks**, including all twelve conditional rows for H and I,
all four signed expressions, telescoping and reversed differences, and
negative-D rejection. The root repeated that evaluator from the delivered
relative-path package, with identical helper bytes.

- [Exact guard](computer_assisted/positive_d_row_terminal/shared_terminal/positive_d_row_guard.py).
- [Independent evaluator](computer_assisted/positive_d_row_terminal/a_family/review_positive_d_row_guard.py).
- [Independent mathematical review](computer_assisted/positive_d_row_terminal/a_family/POSITIVE_D_ROW_GUARD_INDEPENDENT_REVIEW.md).
- [Exact replay report](computer_assisted/positive_d_row_terminal/a_family/POSITIVE_D_ROW_GUARD_INDEPENDENT_REVIEW.json).
- [Byte inventory and conditional scope](computer_assisted/positive_d_row_terminal/MANIFEST.json).

The checker does not reconstruct an original ancestor or certify a whole
cover. Each application must replay its ancestor, prove every conditional
row, exclude all retained complementary domains, and assemble the same
unchanged original predicate before a cell is marked CLOSED. There are no
new mandatory roadmap gates or new original cells.
