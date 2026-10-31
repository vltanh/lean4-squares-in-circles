# Four inner squares have width at least two in every direction

Four pairwise interior-disjoint unit squares whose centers lie in a disk of
radius `1` have union, and hence convex hull, of width at least `2` in every
direction. Their orientations are arbitrary. The ordinary `2 by 2` square
array shows that the constant `2` is sharp, even when all four centers lie
strictly inside the unit disk.

This is a geometric restriction on the four-inner-center case from
[CENTER_RADIUS_REDUCTION.md](CENTER_RADIUS_REDUCTION.md). It does not yet
exclude six additional squares in the target containing disk.

We prove the following slightly more general statement:

> Four disjoint unit squares cannot all lie in a strip of width strictly
> less than `2` if their centers span a distance at most `2` in the direction
> along that strip.

## 1. A clipped section bound for one square

Take the strip's middle line as `x=0`, and translate vertically so that all
center heights belong to `[-1,1]`. Let a square have center `(x,y)` and edge
directions making an angle `theta` with these axes. By the square's symmetry
and reflection, we may use

```text
c = cos(theta),    s = sin(theta),
c >= s >= 0,
w = c+s,          1 <= w <= sqrt(2),
h = w/2.
```

Here `h` is the square's horizontal bounding-box half-width. Since the
containing strip has width less than `2`,

```text
|x| < 1-h = 1-w/2.                                 (1)
```

In particular `|x|<h`, so the line `x=0` meets the square's interior. Write
its vertical section as an interval `I=[l,u]`.

First, the length of `I` is greater than `4/5`. For `s=0` it is `1`. For
`s>0`, the usual section formula for a rotated unit square is

```text
length(I) = min(1/c, (h-|x|)/(cs)).
```

Using (1) and `cs=(w^2-1)/2`, the second term is greater than

```text
(w-1)/(cs) = 2/(w+1) >= 2/(1+sqrt(2)) > 4/5.
```

The first term is at least `1`, proving the claim.

Second, `I` contains `[y-3/10,y+3/10]`.

If `w>=6/5`, (1) gives `|x|<2/5`. The square's inscribed disk of radius
`1/2` cuts the middle line in a segment of half-length at least

```text
sqrt(1/4-(2/5)^2) = 3/10.
```

If `w<=6/5`, we can prove the stronger containment
`[y-2/5,y+2/5] subset I`. In the square's own coordinates, the absolute
coordinates of either endpoint are bounded by

```text
c|x|+(2/5)s,
s|x|+(2/5)c.
```

Using `|x|<=1-w/2`, `c=w-s`, and `0<=s<=w/2`, the first expression is at
most

```text
w-w^2/2+s(w/2-3/5) <= w-w^2/2 <= 1/2.
```

The second is at most

```text
(2/5)w+s(3/5-w/2)
  <= (7/10)w-w^2/4
  <= 12/25 < 1/2.
```

This proves the stronger containment and hence the asserted `3/10` bound.

Since `-1<=y<=1`, we have `l<=7/10` and `u>=-7/10`. Therefore clipping
`I` to the fixed segment `[-3/2,3/2]` leaves length at least `4/5`:

* if neither endpoint is clipped, its length was already greater than
  `4/5`;
* if only the upper endpoint is clipped, the remaining length is at least
  `3/2-7/10=4/5`;
* the lower-endpoint case is symmetric;
* if both endpoints are clipped, the remaining length is `3`.

## 2. Four sections cannot fit

The middle line meets every square's interior. Thus disjoint square
interiors give vertical section intervals with disjoint relative interiors.
Their clipped intervals also have disjoint relative interiors, so their
total length is at most `3`. Section 1 instead gives total length at least

```text
4(4/5) = 16/5 > 3,
```

a contradiction. This proves the strip theorem.

If four centers lie in a radius-`1` disk, their projections onto any line
span at most `2`. Applying the strip theorem in every orientation shows
that the union cannot have width less than `2` in any direction, as claimed.
