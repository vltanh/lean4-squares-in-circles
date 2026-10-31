# Exact radial localization conditional on four inner centers

**Status: computer-assisted, not a hand proof.** The integer checker completed
all four cases during this session. This is a necessary condition for a
hypothetical packing, not an exclusion of that packing.

Suppose ten independently oriented unit squares have disjoint interiors and
lie in the origin-centered disk of squared radius at most `9/2`. Suppose
exactly four centers lie in the open unit disk. Then precisely two of those
four centers have norm at most `13/20`; the other two have norm strictly
greater than `9/10`. In particular none of the four has norm in
`(13/20,9/10]`.

## Four density certificates

For a cut `c`, divide the squares into three classes: center norm at most
`c`, center norm strictly between `c` and `1`, and center norm at least `1`.
Let `k` be the first count; the other counts are `4-k` and `6`.

Each certificate specifies a nonnegative radial density, equal to
`w_j/1000` on the annulus `[j/20,(j+1)/20]`, for `j=0,...,27`, and zero
outside radius `7/5`. The exact integers `w_j` are stored in
[radial_count_certificate.json](radial_count_certificate.json).

The checker verifies that the integral of this density over any single
allowed square is at least `alpha/1000`, `beta/1000`, or `gamma/1000`
according to its center class. It simultaneously verifies

```text
(22/7) sum_j w_j (2j+1) / 400
  < m alpha + (4-m) beta + 6 gamma.
```

Since `pi < 22/7`, the left side strictly exceeds the total available
density integral, after multiplication by `1000`. Interior-disjoint squares
cannot consume more than that total integral.

| Cut | Branch excluded | `(alpha,beta,gamma)` | Certified boxes |
| --- | --- | --- | --- |
| `13/20` | `k<=1` | `(1641,1931,997)` | 297,949 |
| `13/20` | `k>=3` | `(3580,2670,990)` | 126,591 |
| `9/10` | `k<=1` | `(0,1100,980)` | 23,645 |
| `9/10` | `k>=3` | `(2660,2260,990)` | 607,068 |

For the `k<=1` branch, `m=1` and `alpha<=beta`, so the consumption is
minimized at `k=1`. For `k>=3`, `m=3` and `alpha>=beta`, so it is minimized
at `k=3`. The budget comparison therefore excludes the entire indicated
branch. Applying both comparisons at each cut forces `k=2` at each cut,
which proves the stated localization.

## Continuous coverage and exact arithmetic

Run from the repository root:

```sh
python3 research/ten/check_radial_count_localization.py
```

The checker uses only Python's standard library. It uses the same signed
disk-rectangle area bounds and coordinate monotonicity explained in
[RADIAL_WEIGHT_EXCLUSION.md](RADIAL_WEIGHT_EXCLUSION.md), now with integer
scale `D=20*2^15` and all 28 circle radii.

In a square's own axes its center can be written `(a,b)` with `a>=b>=0`.
Containment is equivalent to
`(a+1/2)^2+(b+1/2)^2<=9/2`. A complete dyadic cover of `[0,2]^2` is
discarded only outside that containment region or outside the symmetry
wedge. For every remaining box, circle-area monotonicity and signed density
jumps give a lower bound valid throughout the box. A box crossing a center
class boundary must meet the maximum of all applicable targets, so no
boundary case is omitted. An unresolved box raises an assertion; successful
termination certifies every relevant parameter.

All primitive integrals are enclosed by integer Riemann sums using `isqrt`.
All area bounds, target comparisons, and total budget comparisons use exact
integers. The four successful runs used maximum dyadic depth at most 15;
the checker raises if it cannot close a box by depth 18. It neither samples
orientations nor relies on a floating-point optimizer.

The resulting two-small/two-large split remains compatible with four-square
cores. For example the parallel centers `(+-1/2,-1/5)` and `(+-1/2,4/5)`
are disjoint and have the required radial split. Six additional squares
still have to be excluded by a separate argument.
