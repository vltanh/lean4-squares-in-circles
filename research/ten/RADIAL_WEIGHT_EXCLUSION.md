# Computer-assisted exclusion of five inner centres

**Status:** a finite integer certificate proves the reduction below. This is
computer-assisted supporting research. It does **not** close the unrestricted
ten-square lower bound by hand; the hand proof remains open.

## Certified statement

Suppose ten unit squares have pairwise disjoint interiors and are contained
in the disk `D_(9/2) = {x : |x|² ≤ 9/2}`. At most four of their centres can
belong to the **closed** disk `B(0,1)`.

Together with the separate strict-radius reduction that a hypothetical
packing in `D_q`, `q < 9/2`, has at least three centres in the open unit disk,
this leaves three or four inner centres. This document establishes only the
upper bound of four, by the certificate described below.

The standalone checker is
[`check_radial_weight_exclusion.py`](check_radial_weight_exclusion.py).
It uses Python's standard library, exact integers, and integer square roots.
It does not use numerical optimization, floating-point arithmetic,
transcendental function evaluation, or an external numerical library.

## The radial weight

Let `w(x)` depend only on `r = |x|`:

| Radius | Weight |
| --- | --- |
| `0 ≤ r ≤ 1/2` | `21/10` |
| `1/2 < r ≤ 4/5` | `17/5` |
| `21/20 ≤ r ≤ 27/20` | `4` |
| All other radii | `0` |

Values on boundary circles do not affect area integrals. For a unit square
`S`, define `W(S) = ∫_S w(x) dx`. The certified one-square inequalities are

```text
S ⊂ D_(9/2), |centre(S)| ≤ 1  ==>  W(S) ≥ 2,
S ⊂ D_(9/2), |centre(S)| ≥ 1  ==>  W(S) ≥ 1.
```

The total available weight is

```text
∫ w = π[(21/10)(1/4) + (17/5)(16/25 - 1/4)
          + 4(729/400 - 441/400)]
    = (4731/1000)π
    < (4731/1000)(22/7)
    < 15.
```

The last comparison is the integer inequality
`4731 * 22 < 15000 * 7`; `π < 22/7` is the classical Archimedean bound.
If `k ≥ 5` of ten squares have centre norm at most one, their total weight
is at least `2k + (10-k) = 10+k ≥ 15`. Interior disjointness and `w ≥ 0`
make this impossible.

## Reducing one square to two parameters

Rotate coordinates to the edges of `S`, reflect the two coordinates, and
exchange them if necessary. Rotations and reflections preserve every disk
and the radial weight. Thus it suffices to consider the axis-parallel square

```text
S(a,b) = [a-1/2,a+1/2] × [b-1/2,b+1/2],  0 ≤ b ≤ a.
```

Its containment and inner-centre conditions are exactly

```text
(a+1/2)² + (b+1/2)² ≤ 9/2,
a²+b² ≤ 1.
```

Containment implies `a,b < 2`, so `[0,2]²` covers the full parameter domain.
Write `I_R(a,b)` for the area of `S(a,b) ∩ B(0,R)`. Then

```text
10 W(S(a,b)) = 34 I_(4/5)(a,b) - 13 I_(1/2)(a,b)
                + 40 I_(27/20)(a,b) - 40 I_(21/20)(a,b).
```

For every fixed radius, `I_R(a,b)` is nonincreasing in each variable on
`a,b ≥ 0`. To see this for `a`, fix a horizontal line. Its intersection
with the disk is a symmetric interval about zero. The overlap of that
interval with `[a-1/2,a+1/2]` is nonincreasing as `a ≥ 0` increases.
Integrating those lengths over `[b-1/2,b+1/2]` proves the claim for `a`.
Vertical slices prove the same claim for `b`.

Consequently, on a parameter box
`[a0,a1] × [b0,b1]`, a valid lower bound for `10W` is

```text
34 lower(I_(4/5)(a1,b1)) - 13 upper(I_(1/2)(a0,b0))
+ 40 lower(I_(27/20)(a1,b1)) - 40 upper(I_(21/20)(a0,b0)).
```

The signs of the four coefficients determine which area bound is used.

## Exact disk-area bounds

All lengths use the integer scale

```text
D = 20 × 2^12 = 81920.
```

The four radii become integers `M = D R`. Define the scaled quarter-circle
primitive

```text
J_M(n) = ∫_0^n sqrt(M²-t²) dt,  0 ≤ n ≤ M.
```

This is `D²` times the corresponding physical area. Put
`h_j = floor(sqrt(M²-j²))`, computed by `math.isqrt`. Since the integrand
is decreasing, the following integer sums bound it:

```text
L_M(n) = sum_{j=1}^n h_j             ≤ J_M(n),
U_M(n) = sum_{j=0}^{n-1} (h_j+1)     ≥ J_M(n).
```

These are rectangle Riemann bounds on each unit interval. They require no
approximation of `π`, inverse trigonometric functions, or real square roots.
For scale: `U_M(n)-L_M(n) = h_0-h_n+n ≤ M+n`, so the physical area enclosure
has width at most `(M+n)/D²`.

For integer `x,y ≥ 0`, clip each at `M`, and let `F_M(x,y)` be `D²` times
the area in the first-quadrant rectangle `[0,x/D] × [0,y/D]`:

```text
x²+y² ≤ M²:  F_M(x,y) = xy,
x²+y² > M²:  F_M(x,y) = J_M(x)+J_M(y)-J_M(M).
```

For the first case the whole rectangle lies in the disk. In the second
case, the right and upper caps of the quarter disk are disjoint, because a
point lying strictly beyond both coordinates would be outside the disk.
Subtracting those two caps proves the formula. Therefore `L_M,U_M` give
integer lower and upper bounds for `F_M`, with the subtracted term bounded
in the opposite direction.

Extend `F_M` to signed coordinates by
`H_M(x,y) = sign(x) sign(y) F_M(|x|,|y|)`. Four-term inclusion-exclusion
at the corners `(Da ± D/2, Db ± D/2)` gives rigorous integer bounds for
`D² I_R(a,b)`. This is what `rectangle_cdf` and `square_cdf` implement.

## Finite parameter cover

The checker starts with `[0,2]²` and subdivides a box into its four dyadic
children whenever its current area bound is insufficient. Every endpoint
used is an integer multiple of `1/D`. It discards a box only when:

- `b0 > a1`, so the entire box is outside `0 ≤ b ≤ a`; or
- `2[(Da0+D/2)²+(Db0+D/2)²] > 9D²`, so every square in the box violates
  containment.

For every remaining box, if its lower corner satisfies
`(Da0)²+(Db0)² ≤ D²`, the checker requires the stronger bound `W ≥ 2`
throughout the box. This covers every box that could contain an inner
centre. Otherwise every centre in the box has norm greater than one, and
it requires `W ≥ 1`. A box is accepted only after the corresponding exact
integer comparison succeeds.

The maximum allowed subdivision depth is 13. Failure to certify any box
at that depth raises an error; no unresolved box is silently accepted.
The actual successful run uses depth at most 9 and reports:

```text
certified_inner:              1309 boxes
certified_outer:               645 boxes
outside_containing_disk:       174 boxes
outside_symmetry_wedge:        132 boxes

accepted boxes by depth:
3: 1, 4: 4, 5: 73, 6: 304, 7: 735, 8: 722, 9: 115
```

Subdivision preserves coverage, the two rejection rules remove no admissible
parameter, and every accepted box proves its required inequality. Thus a
successful execution certifies both one-square bounds on their full
continuous domains. The weighted-area argument then gives the stated
exclusion of five inner centres.
