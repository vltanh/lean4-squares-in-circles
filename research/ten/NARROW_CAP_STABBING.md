# A cap beginning at 9/10 contains at most one unit square

This is a hand-proved one-square stabbing lemma. Every unit square contained
in

```text
D_(9/2) ∩ {x ≥ 9/10}
```

contains `P=(3/2,0)` in its interior. Consequently a packing in `D_(9/2)`
has at most one square wholly contained in that cap. Rotation gives the
same conclusion in every direction.

The argument uses the full square geometry, rather than only centre
separation. It does not by itself close the unrestricted ten-square bound.

## 1. Coordinates and a bound for the farthest vertex

Put `a=9/10`. Let the square have centre `(x,y)` and maximum squared vertex
norm `F≤9/2`. Reflect vertically so that `y≥0`. Write its unoriented frame
angle as either `theta` or `-theta`, where

```text
0 ≤ theta ≤ pi/4,
c=cos(theta), s=sin(theta), w=c+s, z=c-s.
```

Its horizontal half-width is `w/2`, so the cap condition gives

```text
x ≥ x0 := a+w/2 ≥ 7/5.                             (1)
```

Every unit-square centre in `D_(9/2)` has norm less than `25/16`, because
`F≥|(x,y)|²+|(x,y)|+1/2`. In particular `y<1<x0`: the centre squared norm
is less than `5/2`, whereas `x²≥49/25`.

For frame angle `theta`, the exact farthest-vertex formula gives

```text
F = x²+y²+1/2 + max(xz+yw, xw-yz).
```

For angle `-theta`, its final term is `xw+yz`, since `x≥y≥0` and `c≥s`.
This is at least both terms in the preceding maximum. Therefore in either
orientation

```text
F ≥ x²+y²+1/2 + max(xz+yw, xw-yz).                 (2)
```

Both branches on the right increase with `x≥0`, so (1) allows us to replace
`x` there by `x0`.

## 2. Comparison with an axis-parallel square

We prove

```text
F ≥ (a+1)²+(y+1/2)².                              (3)
```

After replacing `x` by `x0` in (2), the difference from the right side of
(3) is

```text
D(y) = x0²-(a+1)²+1/4
        + max(x0 z+y(w-1), x0 w-y(z+1)).
```

The first affine function of `y` is nondecreasing and the second is
strictly decreasing. Their intersection is

```text
y0 = x0 s/c.
```

Hence `D(y)≥D(y0)` for every `y≥0`, including `theta=0`. At that intersection

```text
D(y0) = x0²-(a+1)²+1/4+x0(1-s)/c.                 (4)
```

Set `tau=tan(theta/2)`. The farthest horizontal coordinate of the square is
at least `a+w`, so

```text
w ≤ 3/sqrt(2)-a < 43/20-9/10 = 5/4.
```

The function `cos(theta)+sin(theta)` increases on `[0,pi/4]`; at
`tau=1/4` it equals `23/17>5/4`. Thus `0≤tau<1/4`.
Using

```text
c=(1-tau²)/(1+tau²),   s=2tau/(1+tau²),
```

a direct expansion of (4), with `a=9/10`, gives

```text
D(y0) = tau [1-tau-(23/5)tau²-3tau³-(18/5)tau⁴]
          / [(1+tau)(1+tau²)²].                    (5)
```

The bracket is positive: for `0≤tau≤1/4`, the sum of its four subtracted
terms is at most

```text
1/4 + 23/80 + 3/64 + 18/1280 = 383/640 < 1.
```

Thus (5) is nonnegative, proving (3).

## 3. A common interior point

By (3),

```text
(y+1/2)² ≤ 9/2-(19/10)² = 89/100 < (19/20)²,
```

so `|y|<9/20`. Combining (1) with the centre bound gives

```text
7/5 ≤ x < 25/16,     |x-3/2| ≤ 1/10.
```

Consequently

```text
|(x,y)-(3/2,0)|² < 1/100+81/400 = 17/80 < 1/4.
```

The open disk of radius `1/2` about the square's centre lies in its interior.
It therefore contains `P=(3/2,0)`, proving the stabbing statement. Two squares
in the cap would share this interior point, which is impossible in a packing.
