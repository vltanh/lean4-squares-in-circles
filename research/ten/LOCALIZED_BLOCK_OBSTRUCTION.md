# A solid four-square block with two large inner centres has no six-square completion

This is a hand-proved conditional obstruction. The four core squares must
form a solid `2 by 2` block; the theorem does not assume that every four-core
packing has this form.

Suppose four unit squares tile a translated and rotated `2 by 2` square
block. Assume all four centres have norm at most `1`, and at least two have
norm strictly greater than `9/10`. Then at most five further unit squares
can simultaneously

- have pairwise disjoint interiors and avoid the core interiors;
- have centres of norm at least `1`; and
- lie in `D_(9/2)`.

Thus the exact two-large-centre localization from
[RADIAL_COUNT_LOCALIZATION.md](RADIAL_COUNT_LOCALIZATION.md) excludes a
solid block in the four-inner-centre branch of a hypothetical ten-packing.
That application uses the computational localization. The conditional
obstruction itself is proved below without computation.

## 1. Restrictions on the block translation

Rotate to the block's sides, and use its reflection and interchange
symmetries to write

```text
K = [-1,1]² + (s,t),    s ≥ t ≥ 0.
```

The four core centres are `(s±1/2,t±1/2)`. Put

```text
u=s²+t²,    a=s+t,    d=s-t.
```

The largest centre squared norm is `u+a+1/2`, and the second largest is
`u+d+1/2`. Therefore

```text
u+a ≤ 1/2,       u+d > 31/100.                     (1)
```

Subtracting gives `2t=a-d<19/100`, so `t<1/10`.
Also `0≤t<1` gives

```text
u+d = s²+s+t²-t ≤ s²+s.
```

Since `((sqrt(2)-1)/2)²+(sqrt(2)-1)/2=1/4`, (1) implies

```text
s > (sqrt(2)-1)/2.                                (2)
```

We also need

```text
2d-u ≥ 3/10.                                     (3)
```

If `u≤1/10`, (1) gives
`2d-u>62/100-3u≥32/100>3/10`.
If `u≥1/10`, then `u≤1/2` and `a≤1/2-u`. Using `a²+d²=2u`,

```text
d² ≥ 2u-(1/2-u)² = 3u-u²-1/4.
```

Consequently

```text
4d²-(u+3/10)² ≥ (57/5)u-5u²-109/100 ≥ 0.
```

The final polynomial is zero at `u=1/10` and has positive derivative
`57/5-10u` on `[1/10,1/2]`. Both `d` and `u+3/10` are nonnegative, so
`2d≥u+3/10`, proving (3).

## 2. The uncovered parts of the test circle

Let

```text
rho = sqrt(1+1/sqrt(2)).
```

We use the identities

```text
rho sin(pi/8)=1/2,
rho cos(pi/8)=(1+sqrt(2))/2.
```

Both left corners of `K` lie strictly inside `C_rho`. Indeed, the upper
left corner has the larger squared norm, namely

```text
(1-s)²+(1+t)² = 2-2d+u ≤ 17/10 < rho²,
```

by (3). Here `1/sqrt(2)>7/10` follows by squaring positive quantities.

Also `s<1` follows from (1), and `t<1/10`. Thus the block contains the
origin in its interior. On `C_rho`, the regions outside the top, left, and
bottom sides form three open arcs. Because both left corners are inside
the circle, the top and left outside arcs overlap, as do the left and bottom
outside arcs. Their union is one open arc

```text
(alpha, 2pi-beta),
alpha = asin((1+t)/rho),
beta  = asin((1-t)/rho).
```

The arguments are in `(0,1)`: `1+t<11/10<rho`. Moreover

```text
((1+t)/rho)² + ((1-t)/rho)² = (2+2t²)/rho² > 1.
```

For `alpha,beta` in `(0,pi/2)`, this says `sin(beta)>cos(alpha)`, hence
`alpha+beta>pi/2`. Therefore this large uncovered arc has length

```text
2pi-alpha-beta < 3pi/2.                            (4)
```

The region outside the right side is empty if `1+s≥rho`. Otherwise it is
an arc about angle zero, with half-length

```text
gamma = acos((1+s)/rho) < pi/8,                     (5)
```

by (2) and the identity for `rho cos(pi/8)`.
This small arc is disjoint from the large arc: `1-t>9/10>1/2` and
`rho sin(pi/8)=1/2` imply `alpha,beta>pi/8`, whereas `gamma<pi/8`.
Thus the complement of the block on the test circle consists of an arc of
length strictly less than `3pi/2` and, possibly, an arc of length strictly
less than `pi/4`.

## 3. Counting exterior squares

An additional square cannot have interior intersection with the interior
of `K`: otherwise that open intersection would meet the interior of one of
the four unit squares tiling `K`. Its circle trace must therefore lie in
the uncovered arcs above, apart from finitely many boundary contacts.

By [CENTER_RADIUS_REDUCTION.md](CENTER_RADIUS_REDUCTION.md), each additional
square whose centre norm is at least `1` and which lies in `D_(9/2)` meets
`C_rho` in a **single connected arc** of angular length at least `pi/4`.
The small gap in (5) cannot accommodate one such arc. Every additional
square must consequently use the large gap in (4). Interior disjointness
makes these arcs disjoint up to endpoints, so six would require angular
length at least `6pi/4=3pi/2`, contradicting (4).

At most five additional squares are possible, as asserted.
