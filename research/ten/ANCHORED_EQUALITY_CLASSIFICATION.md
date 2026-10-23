# Ten squares with four corner anchors: a complete conditional classification

This is a hand proof about an explicitly restricted class of packings. Suppose
ten unit squares lie in the disk centered at the origin with squared radius
`Q = 9/2`, their interiors are pairwise disjoint, and four of them are the
axis-parallel squares centered at

```text
(-1,-1), (-1,1), (1,-1), (1,1).
```

Call these four squares the **anchors**. The other six squares may initially
have arbitrary positions and orientations. We prove that they are all
axis-parallel and classify all their positions.

**The unrestricted problem remains open here.** We do not prove that an
arbitrary ten-square packing has these anchors, that every packing at
`Q = 9/2` can be brought to this form, or that a smaller disk is impossible.
The argument below uses no numerical optimization or computational certificate.

## The conditional theorem

Put

```text
R = 3/sqrt(2),
h = (sqrt(17)-1)/2.
```

Up to interchanging the coordinate axes and relabeling the six additional
squares, their centers are exactly

```text
(-a,0), (b,0), (0,z1), (0,z2), (0,z3), (0,z4),
```

where

```text
1 <= a <= h,       1 <= b <= h,
-h <= z1,
z1 + 1 <= z2,     z2 + 1 <= z3,     z3 + 1 <= z4,
z4 <= h.
```

Conversely every choice of these six parameters gives a packing with the four
anchors in the disk of radius `R`. In particular, the two horizontal squares
can slide independently outward, in addition to the freedoms in the vertical
four-square chain. The original construction is the choice
`a=b=1` and `(z1,z2,z3,z4)=(-3/2,-1/2,1/2,3/2)`.

The proof first excludes a rotated square among the six additional squares,
then classifies the axis-parallel possibilities.

## 1. A slice obstruction supplied by the anchors

For every height `y` with

```text
1/2 < |y| < 3/2,
```

the anchor interiors occupy both horizontal intervals
`(-3/2,-1/2)` and `(1/2,3/2)`. A connected horizontal interval in the disk
avoiding those interiors must therefore lie either in the central gap of
length `1` or in one of the exterior portions of the disk slice.

Each exterior portion has length at most

```text
sqrt(9/2-y^2) - 3/2
  < sqrt(17)/2 - 3/2
  < 1.
```

The last inequality follows from `17 < 25`. Consequently, an additional
square cannot have an interior horizontal slice of length greater than `1`
at any such height. The analogous statement holds for vertical slices at
`1/2 < |x| < 3/2`.

These statements allow boundary contacts. Only anchor interiors and slices of
square interiors are excluded.

## 2. Every rotated additional square contains a fixed central disk

Consider an additional square that is not axis-parallel. Quarter turns of its
frame, followed if necessary by a reflection of the whole picture, put its
angle in the range `0 < theta <= pi/4`. These operations preserve the anchor
set and disk, and preserve the absolute values of the center coordinates.
Write its center as `(u,v)` and put

```text
c = cos(theta),      s = sin(theta),      t = c+s,
H = t/2 - cs,
B = 1/2 - H = t(t-1)/2.
```

Here `0 < s <= c < 1`, `c^2+s^2=1`, and `1 < t <= sqrt(2)`.
In particular, `cs <= 1/2 < t/2`, so `H > 0`.

### 2.1. Where its slices have length greater than one

At height offset `w = y-v`, its interior horizontal slice has length

```text
1/c                                      if |w| <= (c-s)/2,
(t/2 - |w|)/(cs)                         if (c-s)/2 <= |w| < t/2,
0                                        if |w| >= t/2.
```

To obtain this formula, intersect the two open intervals given by

```text
|c(x-u) + sw| < 1/2,
|-s(x-u) + cw| < 1/2.
```

Since `c < 1`, the first slice length is greater than `1`. Moreover,

```text
H - (c-s)/2 = s(1-c) > 0,
H < t/2.
```

It follows that the slice length is greater than `1` **exactly** when
`|y-v| < H`. The same computation for vertical slices gives the condition
`|x-u| < H`.

### 2.2. The wide slices must lie in the central gap

By Section 1, the nonempty interval `(v-H,v+H)` cannot meet either forbidden
height band `(-3/2,-1/2)` or `(1/2,3/2)`. Because it is connected, it must lie
in one of the three remaining bands. Thus either

```text
|v| + H <= 1/2,
v - H >= 3/2,
or v + H <= -3/2.
```

The second possibility is impossible. The top vertex of the square would
have height at least

```text
3/2 + H + t/2 = 2 + t - t^2/2 >= 1 + sqrt(2) > R.
```

The middle inequality follows, without approximation, from

```text
2 + t - t^2/2 - (1+sqrt(2))
  = (sqrt(2)-t)((sqrt(2)+t)/2-1) >= 0.
```

The last strict inequality is equivalent to `sqrt(2) > 1`. It contradicts
containment in the disk. Reflection excludes the third possibility. Therefore
`|v| <= B`. The vertical-slice argument likewise gives `|u| <= B`.

### 2.3. A uniform disk inside the rotated square

Define

```text
r = 3/2 - sqrt(2) > 0.
```

The absolute projection of `(u,v)` on either unit axis of the rotated square
is at most

```text
tB = t^2(t-1)/2 <= t-1 <= sqrt(2)-1.
```

For any point `p` with Euclidean length strictly less than `r`, its projection
on either unit axis has absolute value less than `r`. The corresponding
coordinate of `p-(u,v)` consequently has absolute value strictly less than

```text
r + (sqrt(2)-1) = 1/2.
```

Thus the **open disk of radius `r` centered at the origin lies in the interior
of every rotated additional square**. In particular there can be at most one
such square in an interior-disjoint packing.

## 3. Axis-parallel additional squares have centers on the axes

For an axis-parallel unit square centered at `(x,y)`, disk containment is
equivalent to

```text
(|x|+1/2)^2 + (|y|+1/2)^2 <= 9/2.
```

It follows that `|x| <= h` and `|y| <= h`, where `h < 2` follows from
`sqrt(17) < 5`.

If both `x` and `y` were nonzero, choose the anchor in the quadrant with their
signs. Both coordinate gaps from its center would be strictly less than `1`:

```text
||x|-1| < 1,       ||y|-1| < 1.
```

The interiors of the two axis-parallel unit squares would overlap. Hence
`x=0` or `y=0`. Conversely, an axis-parallel square centered anywhere on either
axis with coordinate in `[-h,h]` lies in the disk and is interior-disjoint
from all four anchors.

## 4. Six additional squares exclude every rotated square

Suppose one of the additional squares is rotated. By Section 2 it contains
the central open disk of radius `r`, and all five remaining additional
squares are axis-parallel. By Section 3 their centers are on the coordinate
axes. None is centered at the origin, since that square would overlap the
central disk.

There cannot be two on the same one of the four open coordinate half-axes.
Indeed, write their positive distances from the origin as `a < b`. Interior
disjointness on that half-axis requires `b-a >= 1`, while containment gives
`b <= h`. Thus `a <= h-1`, and the inner square meets its axis in the open
interval `(a-1/2,a+1/2)`, whose lower endpoint is at most `h-3/2` and whose
upper endpoint is positive.

The required strict comparison is

```text
h - 3/2 < r,
```

equivalently `sqrt(17)+2sqrt(2) < 7`. To prove it exactly, observe that
`7sqrt(2) < 10` because `98 < 100`; hence

```text
(7-2sqrt(2))^2 = 57-28sqrt(2) > 17.
```

Both sides being nonnegative, `sqrt(17) < 7-2sqrt(2)`, as desired.
It follows that the inner square's open interval on its axis intersects
`(-r,r)`, so its interior meets the central disk. This is a contradiction.

There are only four open half-axes, so at most four axis-parallel squares can
coexist with the rotated square. That gives at most five additional squares,
whereas six are required. Therefore **all six additional squares are
axis-parallel**.

## 5. Classifying the six centers

Their centers now lie on the coordinate axes, within distance `h` of the
origin. A square centered at the origin would force every other center to
have distance at least `1` from it. Each open half-axis could then hold at
most one center, since its allowed interval `[1,h]` has length `h-1 < 1`.
This would give at most five centers. Therefore none is at the origin, and
each belongs to exactly one coordinate axis.

On either axis, consecutive centers are separated by at least `1`. Since
`2h < 4`, each axis holds at most four centers. The only possible counts are
therefore `4+2`, `3+3`, and `2+4`.

The split `3+3` is impossible. On either axis, the middle of three centers
has coordinate in `[-h+1,h-1]`, a subset of `(-1,1)`. The corresponding
horizontal and vertical squares then have both coordinate gaps strictly
less than `1`, so their interiors overlap.

After interchanging the axes if necessary, there are four vertical centers
`z1<z2<z3<z4`. Their constraints are precisely the chain inequalities in the
theorem. Each of `z2,z3` has absolute value at most `h-1 < 1`. An additional
horizontal square centered at `(w,0)` is disjoint from either of those
squares only if `|w| >= 1`.

The two horizontal centers must have opposite signs, because the interval
`[1,h]` on either half-axis has length less than `1`. They are therefore
`(-a,0)` and `(b,0)` with `1 <= a,b <= h`. This proves necessity of the stated
six-parameter family.

## 6. Sufficiency and scope

For any parameters in the stated ranges, the four vertical squares are
interior-disjoint by their successive gaps. The two horizontal squares are
separated from each other by at least `2` and from every vertical square by
a horizontal gap of at least `1`. Every additional square is separated from
each anchor along one coordinate by at least `1`.

Each additional square lies in the disk because its center is on an axis at
distance at most `h`, and

```text
(h+1/2)^2 + 1/4 = 9/2.
```

The anchors themselves lie in the disk and are mutually interior-disjoint.
Their outer corners `(+-3/2,+-3/2)` lie on the circle. This proves sufficiency
and completes the conditional theorem.

The remaining structural task is substantial: establish what, if anything,
forces these four anchors from unrestricted ten-square geometry. Without
that step, neither this classification nor the construction settles the
unrestricted lower bound or the complete equality classification.
