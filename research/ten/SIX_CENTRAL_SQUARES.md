# Six squares can meet the central half-unit disk

This exact example rules out the proposed shortcut that at most five
pairwise interior-disjoint unit squares in `D_(9/2)` can meet the open disk
`B(0, 1/2)`. It consists of only six squares; it is **not** a ten-square
packing or a counterexample to the target lower bound.

For each row below, let

```text
u(t) = ((1-t²)/(1+t²), 2t/(1+t²)),
v(t) = (-u_y(t), u_x(t)),
S = p + [-1/2,1/2] u(t) + [-1/2,1/2] v(t).
```

The vectors `u(t),v(t)` are an orthonormal pair, so `S` is a unit square.
Every coordinate and direction in this construction is rational.

| Square | Centre p | t |
| --- | --- | --- |
| 1 | `(1167/1000, -19/100)` | `2/5` |
| 2 | `(587/1000, 801/1000)` | `11/20` |
| 3 | `(-103/250, 111/100)` | `11/20` |
| 4 | `(-293/250, 91/500)` | `13/50` |
| 5 | `(-763/1000, -463/500)` | `1/20` |
| 6 | `(51/125, -223/200)` | `29/40` |

Put `a = |p·u|` and `b = |p·v|`. The exact squared distances to the nearest
and farthest points of this square are

```text
d_min² = max(a-1/2,0)² + max(b-1/2,0)²,
d_max² = (a+1/2)² + (b+1/2)².
```

For every row, direct rational substitution gives

```text
d_min² < 49/200 < 1/4,
d_max² < 15/4 < 9/2.
```

Thus all six squares meet the **open** central disk, with room to spare,
and all lie in the substantially smaller containing disk `D_(15/4)`.

For squares `i,j`, write `d = p_j-p_i` and

```text
w_ij = (1 + |u_i·u_j| + |u_i·v_j|)/2.
```

The following separating-axis choices satisfy
`|d·axis| - w_ij > 9/1000`. Therefore even the closed squares are disjoint.

| Pair | Separating axis | Pair | Separating axis | Pair | Separating axis |
| --- | --- | --- | --- | --- | --- |
| 1,2 | `v_1` | 1,3 | `v_1` | 1,4 | `v_1` |
| 1,5 | `u_5` | 1,6 | `u_1` | 2,3 | `v_2` |
| 2,4 | `u_4` | 2,5 | `u_2` | 2,6 | `u_6` |
| 3,4 | `u_3` | 3,5 | `v_5` | 3,6 | `v_3` |
| 4,5 | `v_4` | 4,6 | `v_6` | 5,6 | `v_6` |

The standalone checker [`check_core_obstruction.py`](check_core_obstruction.py)
checks all these strict inequalities with Python's exact `Fraction`
arithmetic. It uses no floating-point calculations or optimization.

Consequently, the central-disk reduction needs an interaction between
central and exterior squares; a claimed central capacity of four or five
would be false.
