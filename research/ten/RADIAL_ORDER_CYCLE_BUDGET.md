# Radial order excludes 206 larger-cycle signatures

**Status:** exact hand theorem; two independent full mathematical reviews
passed on 2026-10-29. The explicit batch was independently reconstructed
from cyclic loaded-position intervals, including all 206 stable IDs.

Use a hypothetical strictly subcritical ten-square packing, the physical
positive stress, and a whole mixed simple-cycle component of length
`6<=m<=10`. Let k be its number of loaded bodies. The fixed
[cycle inventory](cycle_cases.json) retains `3<=k<=7`.

The [diagonal-path uncrossing theorem](DIAGONAL_PATH_UNCROSSING.md), together
with the reviewed side-path theorems, proves that the loaded bodies follow
their radial circular order after the unloaded runs are contracted. Unlike
the earlier [single-side batch](SINGLE_SIDE_TRANSMISSION_UNCROSSING.md),
there is no restriction on the number of diagonal transmitters here.

**Theorem.** All 206 signatures in
[radial_order_cycle_batch.json](radial_order_cycle_batch.json) are excluded.
They include every previously closed signature and add 88 new exclusions.
The fixed inventory therefore has 73 entries not excluded by these results.

## 1. The exact angular budget

Let t,s,d denote the numbers of SS, single-S, and single-D transmission
runs. The remaining `k-t-s-d` edges are direct loaded contacts. Thus

```text
m=k+2t+s+d,       t+s+d<=k.
```

Use the same exact half-angle constants as in
[SHARED_ENDPOINT_CYCLE_ANGLE_BUDGET.md](SHARED_ENDPOINT_CYCLE_ANGLE_BUDGET.md):

```text
a=asin(24/25), v=asin(16/25),
b=asin(328/425), c=asin(8/25).
```

Every radial neighbor gap exceeds twice its corresponding half-angle.
Since the gaps sum to `2pi`, a necessary condition is

```text
Omega=t a+s v+d b+(k-t-s-d)c < pi.                    (1)
```

The reviewed angular-budget note proves

```text
a>2pi/5, v>pi/5, b>pi/4, c>pi/10,
b>v>2c,      b+v>pi/2,      a+b+3c>pi.               (2)
```

In particular its coarse bound is now valid for every d:

```text
Omega>(m+t+d/2)pi/10.                               (3)
```

## 2. Two hundred signatures from the existing inequalities

Equation (3) excludes all cases with `m=10`, all cases with `m=9,t>=1`,
all cases with `m=9,d>=2`, all cases with `m=8,t>=2`, and all cases with
`m=8,t>=1,d>=2`.

If `m=9,t=0,d=1`, then `k+s=8`. Since `k<=7`, at least one S run
exists. The sharper sum gives

```text
Omega=(v+b)+(s-1)v+(k-s-1)c
 > pi/2+[2(s-1)+(k-s-1)]pi/10
 = pi/2+(k+s-3)pi/10=pi.
```

Each multiplicity is nonnegative because it counts actual runs or direct
contacts. Thus every nine-body case with at least one D is excluded.

If `m=8,t=d=1`, then `k+s=5`, and

```text
Omega=a+b+s v+(k-s-2)c
      =a+b+3c+s(v-2c)>pi.
```

Consequently these arguments give the following excluded selection

```text
m=10; or
m=9 with (t>=1 or d>=1); or
m=8 with (t>=2 or (t>=1 and d>=1)).                  (4)
```

There are 200 fixed-inventory signatures in (4). This count is bookkeeping
only; the preceding inequalities exclude every physical realization of
each selected signature.

## 3. One additional elementary angle inequality

We also have

```text
3b+2c>pi.                                           (5)
```

Indeed `pi/4<b<pi/3`: the lower bound is in (2), while the upper bound
follows from `4*328^2<3*425^2`. Since

```text
cos(b)=sqrt(73041)/425,
cos(3b)=-249711 sqrt(73041)/76765625,
```

the exact bound `sqrt(73041)>270` gives

```text
cos(3b)<-249711*270/76765625<-81/100.
```

The second strict comparison has positive rational gap

```text
249711*270/76765625-81/100=4193451/61412500>0.
```

Also `cos(pi/5)=(1+sqrt(5))/4<81/100`, using `sqrt(5)<56/25`.
Thus `cos(3b)<cos(4pi/5)`. Both angles are in `(0,pi)`, so strict
decrease of cosine implies `3b>4pi/5`. The bound `2c>pi/5` from (2)
then proves (5).

## 4. Six further eight-body signatures

Suppose `m=8,t=0`. The following additional run counts contradict (1):

| `(k,s,d)` | Angular contradiction |
| --- | --- |
| `(4,0,4)` | `Omega=4b>pi` |
| `(4,1,3)` | `Omega=3b+v=2(b+v)+(b-v)>pi` |
| `(5,0,3)` | `Omega=3b+2c>pi` by (5) |
| `(4,2,2)` | `Omega=2(b+v)>pi` |

These four count patterns contain six fixed-inventory signatures. They
are disjoint from (4). The first three are exactly all possible eight-body
patterns with `t=0,d>=3`: since `s+d<=k` and `k+s+d=8`, one has
`d<=4`; if `d=3`, then `s<=1`. Thus the full 206-signature selection is

```text
(4), or
m=8,t=0 with [d>=3 or (d=2 and s=2)].                 (6)
```

Every condition is an integer condition on the fixed cyclic word. No
floating-point angle comparison is used to select or prove a case.

## 5. Finite coverage and the remaining count

The explicit IDs and run counts are in
[radial_order_cycle_batch.json](radial_order_cycle_batch.json). The small
[batch builder](build_radial_order_cycle_batch.py) reads the unchanged
279-case manifest, reconstructs its cyclic runs, and applies (6).

| Length | Inventory cases | Excluded by this theorem | Remaining |
| --- | ---: | ---: | ---: |
| 6 | 15 | 0 | 15 |
| 7 | 23 | 0 | 23 |
| 8 | 45 | 17 | 28 |
| 9 | 71 | 64 | 7 |
| 10 | 125 | 125 | 0 |
| Total | 279 | 206 | 73 |

The 118 previous exclusions form a subset of this selection; hence this
theorem adds 88 cases to that earlier checkpoint. A remaining case is not
claimed feasible merely because it survives the angular budget. Its
continuous contact ownership, geometry, and positive stress constraints
still require exclusion or a completion-capacity theorem.

In particular, no claim about branching mixed components is made here:
the new D-D uncrossing argument uses a degree-two loaded endpoint of the
whole simple cycle.
