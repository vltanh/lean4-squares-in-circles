# A common physical box for the Cd402 stacked branches

**Scope:** this is a hand derivation of a four-original caller, not a complete
Cd402 original-cell exclusion. The positive-H four-original table has now
passed fresh exact arithmetic locally, including all bound deductions. Its
complete compact certificate publication is in progress; this note alone
must not be used as a substitute for that table. The negative-H counterpart
is still under construction at this checkpoint. No original-cell ledger
entry is promoted.

## The same original squares and the exact caller

Retain the unchanged original squares E,F,H,I, their independent frames,
all their corners in the closed Q-disk, Q=1105/256, and all physical pairs.
Put rho=91/60 and g_S=1/(4h_S). Each center has norm strictly below rho,
and g_S >= 1/(2 sqrt(2)). Suppose EF is an actual horizontal projection
link with its marked positive-horizontal center-cone comparison, and

    y_H-y_F >= g_F+g_H,
    y_I-y_H >= g_H+g_I,
    x_H <= x_I.

The saved Cd402 leaf 468 supplies these conditions, H's nonnegative
canonical tangent, and the following weaker original coordinate bounds:

    -131/100 <= x_E <= -47/64,     5/8 <= y_E <= 63/50;
    -9/40 <= x_F <= 17/64,       -3/8 <= y_F;
    -141/100 <= x_H.

These are rational enlargements of its accepted incoming state, not
constraints inferred from a plotted pose. The archived source is
`a2_00100_c_finite_frontiers_v2/covers/cd402_opposite_507/MANIFEST.json`,
Git blob `12b58e41d467daeac461e246055ce7aca7aec421`, at commit
`6a9a45e0ad997c8e143b0f22a0de88370d9d7adb`.
The prior derivation of that incoming state remains an explicit dependency;
it has not been freshly replayed in this continuation.

## All the remaining root-box bounds follow by hand

Since 707^2 < 500000, every pair of inset halfwidths has sum greater
than 707/1000. The two upward comparisons therefore imply

    y_H > -3/8+707/1000 = 83/250 > 33/100,
    y_H < 91/60-707/1000 = 2429/3000 < 81/100,
    y_I > -3/8+707/500 = 1039/1000 > 103/100,
    y_F < 91/60-707/500 = 77/750 < 21/200.

The center bound for I and y_I>103/100 give |x_I|<9/8, because

    (9/8)^2+(103/100)^2-(91/60)^2 = 9449/360000 > 0.

The unchanged extra order x_H<=x_I then gives x_H<9/8. Consequently
every original caller belongs to this complete rational rectangle:

| Original | Horizontal interval | Vertical interval |
|---|---|---|
| E | [-131/100,-47/64] | [5/8,63/50] |
| F | [-9/40,17/64] | [-3/8,21/200] |
| H | [-141/100,9/8] | [33/100,81/100] |
| I | [-9/8,9/8] | [103/100,91/60] |

No E/H horizontal inset comparison is assumed in this broader caller.
This is the principal difference from the already published leaf-480
four-square table. Every original orientation of E,F,I remains allowed.

The small-F common-axis terminal remains valid: the F rectangle gives

    (29/60)^2-(17/64)^2-(3/8)^2 = 20671/921600 > 0.

Thus |c_F|<29/60 and every other center is at distance <2 from F.
Two successive genuine separations along one identical owned axis, with
F at an end, would force projected span at least two. Both owners, local
axes, signs and contact faces are retained unless this exact common-axis
argument rules out their complete chosen alternative.

## Complete positive-H table: local validation record

The completed local table covers H tangent in [0,1] and the eight closed
independent sign roots for E,F,I. Every internal split retains both closed
angle halves or all eight original owned-axis alternatives. Its fixed
full-tree SHA-256 is

`cae1d1214cd7ed552e8d262a7856507cab2ec01b5e484f0043bea836d4a71640`.

Fresh solver-free reconstruction has checked all 2,358 nodes, all 21,452
exact bound deductions, 819,328 weighted bound-row occurrences and 44,139
weighted terminal-row occurrences. The tree has 842 complete internal
splits and 1,516 terminal exclusions, with zero unresolved domains.
The terminals comprise 1,465 exact weighted contradictions and 51
common-axis contradictions. The physical rows use the same elementary
four-square rules as `four_exact.py`, with the broader rectangle above
and without the E/H inset premise; imported pair-cap, tilt-toll and
three-square-energy slots are not used.

This supplies an exclusion of the saved leaf 468 once the full table and
its attachment are assembled. The adjacent negative-H four-square domain
is not claimed excluded at this checkpoint. The whole Cd402 original,
C887, and the 001/00 mask remain open. No Lean, Lake, CI, proof-kernel
verification or independent human review is claimed.
