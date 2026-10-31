# The cap bound excludes 234 larger-cycle signatures

**Status:** exact hand theorem. The cap theorem, its angular-budget
consequence, and the selection of stable case IDs received two independent
mathematical reviews on 2026-10-29. The explicit inventory count is
bookkeeping, not a numerical geometric premise.

Work in a hypothetical strictly subcritical ten-square packing, with
`79/40<=R<3/sqrt(2)`, the physical positive stress, and a whole mixed
simple-cycle component of length `6<=m<=10`. The fixed
[cycle inventory](cycle_cases.json) has `3<=k<=7` loaded bodies.

**Theorem.** Every signature in
[sharp_transmission_cycle_batch.json](sharp_transmission_cycle_batch.json)
is impossible. There are 234 such signatures, including all 206 excluded
by the previous [radial-order budget](RADIAL_ORDER_CYCLE_BUDGET.md).
This adds 28 exclusions and leaves 45 entries in the fixed 279-case
inventory unresolved by these results.

## 1. Radial order and the improved gap bounds

Contract each unloaded run. The reviewed side-path uncrossing results and
[diagonal-path uncrossing theorem](DIAGONAL_PATH_UNCROSSING.md) show that
the resulting cycle follows the radial circular order of its loaded
centers. This step uses that the whole positive component is a simple
cycle. It is not assumed for arbitrary branching components.

Let `t,s,d` count the SS, single-S, and single-D runs. There are
`k-t-s-d` direct loaded-loaded contacts, and

```text
m=k+2t+s+d,       t+s+d<=k.
```

Every nonempty run supplies parallel endpoint support lines separated
by its total width, by
[CYCLIC_STRESS_REDUCTIONS.md](CYCLIC_STRESS_REDUCTIONS.md), Section 2.
The [cap angle theorem](TRANSMISSION_CAP_ANGLE_BOUND.md) therefore gives
these strict lower bounds for the corresponding minor center angles:

```text
SS: 9pi/10,       S: pi/2,       D: 3pi/5.
```

Every pair of loaded centers has minor angle greater than
`2 asin(8/25)>pi/5`, as proved in
[SHARED_ENDPOINT_CYCLE_ANGLE_BUDGET.md](SHARED_ENDPOINT_CYCLE_ANGLE_BUDGET.md),
Sections 2 and 3. Apply that bound to each direct contact.

A successive radial gap is at least the minor angle between its endpoint
rays, including when the radial gap exceeds pi. The k radial gaps sum
to `2pi`, so they satisfy

```text
2pi > t(9pi/10)+s(pi/2)+d(3pi/5)+(k-t-s-d)(pi/5)
    = (2k+7t+3s+4d)pi/10
    = (2m+3t+s+2d)pi/10.                            (1)
```

Consequently the exact integer condition

```text
2m+3t+s+2d >= 20                                    (2)
```

excludes a signature. Every comparison in this selection is integral;
no floating-point angle estimate is used.

## 2. The preceding 206 exclusions are retained

The previous selection was:

```text
m=10; or
m=9 with (t>=1 or d>=1); or
m=8 with (t>=2 or (t>=1 and d>=1)); or
m=8,t=0 with [d>=3 or (d=2 and s=2)].
```

Each condition implies (2). For `m=10` this is immediate. For `m=9`,
either `3t>=3` or `2d>=2`. For the first eight-body condition, either
`3t>=6` or `3t+2d>=5`. For its last condition, either `2d>=6` or
`s+2d=6`. Thus no previously closed signature reopens.

## 3. Finite coverage and the remaining cases

The [batch builder](build_sharp_transmission_cycle_batch.py) reads the
unchanged 279-case manifest, reconstructs every cyclic unloaded run,
and applies (2). It also checks that every stable ID in the preceding
206-case batch is retained. An independent reconstruction by intervals
between successive loaded positions gives the same selected IDs.

| Length | Inventory cases | Excluded by this theorem | Remaining |
| --- | ---: | ---: | ---: |
| 6 | 15 | 0 | 15 |
| 7 | 23 | 4 | 19 |
| 8 | 45 | 34 | 11 |
| 9 | 71 | 71 | 0 |
| 10 | 125 | 125 | 0 |
| Total | 279 | 234 | 45 |

The 28 newly excluded IDs are recorded explicitly in the batch JSON.
All nine- and ten-body cases in this simple-cycle inventory are now
excluded. The surviving six-, seven-, and eight-body signatures still
carry continuous geometry, ownership, and stress constraints. Survival
of this inequality does not imply a physical realization exists.

This result does not close the full larger-cycle family C20, any
branching family, or the unrestricted n=10 theorem.
