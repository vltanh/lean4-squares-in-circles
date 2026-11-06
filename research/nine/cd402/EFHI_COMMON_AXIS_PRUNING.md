# Exact common-axis pruning in the Cd402 stacked frontier

Status: a complete conditional hand terminal for the saved node-480 caller;
not a proof of node 480, the Cd402 original, or the whole mask. The original
231-cell ledger is unchanged. This terminal is intended only to remove
explicitly impossible children of a complete physical separator cover.

## Exact physical input and rational containing box

Retain the four original unit squares E,F,H,I from the original-nine
Cd402 cell, with all four corners of each in the closed Q-disk,
Q=1105/256, and pairwise disjoint open interiors. All nine originals
remain in the calling theorem. The saved node-480 state supplies the
weaker rational F-center box

    -103/500 <= x_F <= 17/64,
    -71/200 <= y_F <= 11/1000.

The source is the archived `cd402_opposite_507` checkpoint. These rounded
endpoints contain its certified F intervals; this note does not claim a
fresh replay of that archived attachment. A new complete table must verify
that attachment before invoking the terminal on the original cell.

Every original center has norm strictly less than rho=91/60, even at
closed Q. Indeed its farthest original corner has squared norm at least
|c|^2+|c|+1/2, and

    rho^2+rho+1/2-Q = 31/57600 > 0.

The F box gives the exact positive comparison

    (29/60)^2 - (17/64)^2 - (71/200)^2
      = 853159/23040000 > 0.

Therefore |c_F|<29/60. For every other original X, the triangle inequality
now gives

    |c_X-c_F| < 91/60+29/60 = 2.                 (1)

## Complete terminal

There cannot be two genuine physical separations along the same signed
unit direction n, in the successive order F,Y,X or X,Y,F, for three
distinct original squares. For the first order, such separations would be

    n.(c_Y-c_F) >= h_F(n)+h_Y(n),
    n.(c_X-c_Y) >= h_Y(n)+h_X(n).

Each unit-square support halfwidth is at least 1/2. Summing gives

    n.(c_X-c_F) >= h_F(n)+2h_Y(n)+h_X(n) >= 2,

contradicting (1) and Cauchy-Schwarz. Reversing n proves the other order.
Contacts and all orientation signs are included. No selected cone link
is promoted to an actual projection comparison.

## Literal implementation in a separator table

A selected SAT alternative for the unordered local pair i<j is encoded
as `(i,j,o,a,s)`, with actual owner o in {i,j}, actual local side axis
`a in {0,1}`, and sign `s in {-1,+1}`. Group alternatives only when
both their actual owner and local side axis agree. In the positive
owned-axis direction, orient the pair edge i->j when s=+1, and j->i
when s=-1. A two-edge directed path with F at one end and two other
distinct labels at the remaining vertices is impossible by the theorem.

This grouping never identifies merely nearby angles, unrelated owners,
or arbitrary coordinate axes. It concerns the identical original frame
variable in both pair inequalities. Every other SAT child remains in
the cover. Thus the rule is an exact finite pruning operation, not an
approximate geometric test.

## Current validation boundary

The displayed arithmetic is an exact rational identity. The geometric
proof is fully printed above. The numerical four-square exploration is
still a discovery calculation; its LP statuses and contracted floating
boxes are not accepted proof certificates. No original-cell closure,
independent review, Lean compilation, Lake or CI is claimed by this note.
