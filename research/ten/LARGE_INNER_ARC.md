# A large inner centre uses more than one twelfth of the circle

This is a hand-proved restriction. It replaces one part of the computational
radial-count localization, but does not close the unrestricted ten-square
proof.

Put

```text
rho = sqrt(1+1/sqrt(2)),
H = rho² = 1+1/sqrt(2).
```

Here `rho` is the radius of the test circle, not the radius of the containing
disk `D_(9/2)`.

## One-square statement

Let `S` be any unit square, with arbitrary orientation and centre `c`.
If

```text
9/10 ≤ |c| ≤ 1,
```

then its intersection with the circle `C_rho` has total angular length
**strictly greater than `pi/6`**. The total includes both components when
the intersection is disconnected.

Write `t=|c|²` and `L` for this angular length. The centre-radius theorem
settles `t=1`, since then `L≥pi/4`. Suppose therefore that
`81/100≤t<1`. The inner arc-moment theorem gives `L>0`. If `L≥pi/4`, there
is again nothing to prove.

For `0<L<pi/4`, Sections 2 and 3 of
[INNER_ARC_MOMENT.md](INNER_ARC_MOMENT.md) prove the stronger intermediate
reduction

```text
t ≤ max(T_D(L), T_B(L)),

T_D(ell) = 2(rho cos(pi/4-ell/2)-1/2)²,
T_B(ell) = H-k/2-(1-k)X,
k = tan(ell/2),
X = sqrt(H/(1+k²)-1/4).
```

This reduction includes the one-arc and two-arc cases. We show that
`L≤pi/6` makes both terms strictly smaller than `81/100`.

For the diagonal branch, `T_D` is increasing on `[0,pi/6]`: both
`rho cos(pi/4-ell/2)-1/2` and its derivative are positive. Hence

```text
T_D(L) ≤ T_D(pi/6) = (sqrt(3H)-1)²/2 < 81/100.
```

The final strict inequality follows from the exact identity

```text
(1+9sqrt(2)/10)² - 3H = (15sqrt(2)-19)/50 > 0.
```

For the boundary branch, `0≤ell≤pi/6` gives

```text
0 ≤ k ≤ tan(pi/12) = 2-sqrt(3) < 2/7 < 1/3,
17/10 < H < 12/7.
```

The rational comparisons follow by squaring positive quantities:
`sqrt(3)>12/7`, `1/sqrt(2)>7/10`, and `1/sqrt(2)<5/7`.
In particular,

```text
X² = H/(1+k²)-1/4
   > (17/10)/(10/9)-1/4
   = 32/25
   > 81/64,
```

so `X>9/8`. Since `1-k>0`, this yields

```text
T_B(L) < H-k/2-(1-k)(9/8)
       = H-9/8+(5/8)k
       < 12/7-9/8+(5/8)(2/7)
       = 43/56
       < 81/100.
```

Thus `L≤pi/6` contradicts `t≥81/100`, proving the one-square statement.

## Consequences for ten squares

Assume ten pairwise interior-disjoint unit squares lie in `D_(9/2)`.
Call a centre *inner* when its norm is strictly less than `1`.
Every non-inner square occupies at least `pi/4` of `C_rho`, by
[CENTER_RADIUS_REDUCTION.md](CENTER_RADIUS_REDUCTION.md). Circle arcs of
different squares have disjoint interiors, up to finitely many endpoints,
so their total angular length is at most `2pi`.

If exactly four centres are inner, the other six squares use at least
`6pi/4=3pi/2`. Three inner centres of norm at least `9/10` would use
strictly more than `3pi/6=pi/2`, which is impossible. Therefore at most two
of the four inner centres have norm at least `9/10`; at least two have norm
strictly less than `9/10`.

If exactly three centres are inner, the other seven squares use at least
`7pi/4`. Two inner centres of norm at least `9/10` would use strictly more
than `2pi/6=pi/3`, exceeding the remaining budget `pi/4`. Thus at most one
of the three inner centres has norm at least `9/10`.

These are analytic necessary conditions. They do not exclude all packings
with three or four inner centres.
