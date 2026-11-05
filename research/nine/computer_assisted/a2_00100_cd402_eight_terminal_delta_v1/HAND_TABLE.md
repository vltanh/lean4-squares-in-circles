# Cd402: eight exact exclusions on the unchanged frontier

This table concerns original `negative-d4021ade840b985c` in mask `001/00`,
at squared radius `1105/256`. It excludes eight existing pending domains;
it does not exclude the whole original. The unchanged original path is
`angle D nonpositive; angle A nonnegative; alternate_four_escape(B,H) case 2`.
The precise original path, all original-square state intervals, and each
additional closed branch predicate are retained literally in
`SOURCE_MANIFEST.json` and the eight node records.

## Complete-domain substitution

The frozen source manifest has SHA-256
`7141479669891c5f7d804d0979ce74bb1fbaa468b43345817bc764733c0f3867`.
It contains 478 processed nodes and 25 pending alternatives. Substitute the
following exact exclusions at the same eight pending indices, retaining
every inherited node and every other pending alternative.

| Existing frontier index | Exact terminal | Printed physical rows |
|---:|---|---:|
| 40 | Positive rational contradiction | 20 |
| 41 | Three-row cancellation displayed below | 5 |
| 471 | Empty propagated original-center interval | 0 |
| 472 | Empty propagated original-center interval | 0 |
| 478 | Positive rational contradiction | 23 |
| 479 | Incompatible effective D/G separating angle | 0 |
| 486 | `0 <= -156759/524288` | 1 |
| 487 | `0 <= -32484263336032101291/36893488147419103232` | 1 |

`NEW_TERMINALS_EXACT_REPLAY.json` freshly reconstructs and checks all 50
printed physical rows and all three interval/angle terminals with the
independent verifier. It imports no numerical producer. The same check
verifies all 141 inherited complete child covers, their exact child choices,
unique parents, and complete reachability after substitution. The resulting
`GRAFTED_MANIFEST.json` retains 17 pending alternatives. No equality face,
unprocessed alternative, original corner or original square is removed.

The initial local substitution check did not rerun inherited ancestor
arithmetic. The delivered `NATIVE_REPLAY.json` now independently reconstructs
the original, replays its three original-bound rounds, and freshly checks
all ten ancestor records needed for these eight starting states. Together
with the new terminals, it checks 1,628 deductions and 4,053 printed rows.
Those ten records are preserved byte-for-byte in the compressed delta.

Arithmetic on the other old branches is outside this delta's fresh replay.
Their exact input identities remain bound by `INHERITED_NODE_SHA256.json`;
a final whole-original acceptance must retain their existing proofs and
resolve the remaining seventeen alternatives. The delivered replay uses
the explicitly hash-bound native checker runtime and published legacy
bases; no cold standalone proof is claimed.

## The short cancellation for domain 41

Write `X = x_A - x_E` and `Y = y_A - y_E`. Define

```
alpha = 373215911805039/281474976710656
beta  = 421946968507931/140737488355328
```

The existing stronger-altitude row on originals A,H,E, followed by the
two pairs of existing correlated rotated unit-gap rows on A,H and E,H,
gives the following three inequalities. Each paired gap row cancels H's
coordinates, so the same physical original H is used in both terms.

| Row | Left side | Right side |
|---|---|---|
| Altitude | `alpha X + beta Y` | `-8265533890605533673167952639/1237940039285380274899124224` |
| Gap direction `(12/13,-5/13)` | `-5X/13 - 12Y/13` | `-270238891077447/281474976710656 - 132105246255949/140737488355328` |
| Gap direction `(15/17,-8/17)` | `-8X/17 - 15Y/17` | `-16477546619077/17592186044416 - 135974435438119/140737488355328` |

Take the nonnegative multipliers

```
1,
lambda = 13(8 beta - 15 alpha)/21
       = 14987866647667043/5910974510923776 > 0,
mu     = 17(12 alpha - 5 beta)/21
       = 2202530680939843/2955487255461888 > 0.
```

Direct substitution gives

```
alpha - 5 lambda/13 - 8 mu/17 = 0,
beta  - 12 lambda/13 - 15 mu/17 = 0.
```

Their sum is therefore the exact contradiction

```
0 <= -21478438766846792412400225022071
     /1663791412799551089464422957056 < 0.
```

This version has exact coefficient cancellation and needs no residual
coordinate error payment. `NODE41_HAND_CANCELLATION.json` preserves all five
independently reconstructed physical row literals, the exact multipliers,
and the checked zero coefficients. The original LP-produced terminal is
retained unchanged alongside this shorter hand table.

## The other rational sums

For domains 40 and 478, the node files print every rational coefficient,
nonnegative dyadic multiplier, and absolute variable bound. If the weighted
rows have sum `c.z <= b` and the saved bounds give `|z_k| <= M_k`, then
`-sum_k M_k |c_k| <= c.z <= b`. Each recorded exact reserve
`-b-sum_k M_k |c_k|` is strictly positive, which is impossible. The
independent replay recomputes the row literals, coefficients, right side,
residual payment and positivity from exact fractions.

The one-row contradictions for 486 and 487 have no variable coefficients.
The three interval/angle exclusions use the existing original-square
propagation rules on the exact closed saved states. Consequently all eight
substitutions cover their entire original closed frontier domains.

**Whole-original accounting remains unchanged: Cd402 is OPEN.**
