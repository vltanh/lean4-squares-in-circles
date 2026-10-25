# A vertically translated two-by-two core admits at most five more squares

Let four axis-parallel unit squares with centers
`(±1/2,t±1/2)` fill the rectangle

```text
K = [-1,1] × [t−1,t+1].
```

Suppose their four centers lie in the closed unit disk. Then at most five
additional unit squares, with arbitrary independent orientations and interiors
disjoint from one another and from `K`, fit in the origin-centered disk of
squared radius `9/2`.

In particular, a ten-square packing cannot have this four-square core. This
is a restricted hand obstruction: it assumes an exact two-by-two block and
translation along one of its side directions. It does not cover a sheared
four-square core or arbitrary core orientations.

## 1. A region containing every additional center

Reflect vertically if necessary, so `t>=0`. The upper core centers are
`(±1/2,t+1/2)`. Their unit-disk condition gives

```text
t <= (sqrt(3)−1)/2 < 3/8.                         (1)
```

For any unit square in the containing disk, write its center in its own
orthogonal coordinates as `(a,b)`, and put `r=sqrt(a²+b²)`. The largest
squared vertex norm is

```text
r² + |a| + |b| + 1/2 >= r²+r+1/2.
```

Consequently every additional center `p=(x,y)` satisfies

```text
|p| <= (sqrt(17)−1)/2 < H,     H=25/16.           (2)
```

Its square contains the open disk of radius `1/2` centered at `p`, so
disjointness from the four-square block implies

```text
distance(p,K) >= 1/2.                             (3)
```

Distinct additional centers have distance at least one, since their open
inscribed radius-`1/2` disks are disjoint.

We claim that every point satisfying (2) and (3) belongs to at least one
of these four regions:

```text
L: x <= −3/2,
R: x >=  3/2,
T: y >= t+3/2,
B: y < −1.                                       (4)
```

If the closest point of `K` lies on a side, this follows immediately from
(3); for the lower side use `y<=t−3/2<−1`. It remains to consider the
corner regions.

An upper-corner point has `|x|=1+a`, `y=1+t+b`, with `a,b>=0` and
`a²+b²>=1/4`. Since `a+b>=1/2`,

```text
|p|² >= 2+(a²+b²)+2(a+b) >= 13/4 > H².
```

Thus upper-corner points are impossible. A lower-corner point has
`|x|=1+a`, `y=−(1−t+b)`, with the same conditions on `a,b`. If `y>=−1`,
then `0<=b<=t<3/8`, and hence

```text
|p|² >= (1+sqrt(1/4−b²))² + (1−t+b)².            (5)
```

The expression on the right is a constant plus
`2sqrt(1/4−b²)+2(1−t)b`, a concave function of `b`. Its minimum on
`[0,t]` is therefore attained at an endpoint. At those endpoints it is
bounded below by

```text
b=0:   9/4+(1−t)² > 169/64 > 625/256 = H²,
b=t:   (1+sqrt(1/4−t²))²+1 > 41/16 > H².
```

For the second estimate, `t<3/8` gives
`sqrt(1/4−t²)>sqrt(7)/8>1/4`. Both alternatives contradict (2). Every
possible lower-corner point therefore has `y<−1`. This proves (4).

## 2. Capacities of the four regions

Each side region `L` and `R` contains at most one additional center.
Indeed, its intersection with `|p|<H` lies in a rectangle of horizontal
width `1/16` and vertical height `7/8`, because

```text
H²−(3/2)² = 49/256.
```

The squared diameter of that rectangle is `197/256<1`. The same estimate,
with coordinates interchanged and using `t>=0`, shows that `T` contains
at most one center.

Region `B` contains at most three centers. Inside `|p|<H` and `y<−1`,
the horizontal span is less than `sqrt(369)/8` and the vertical span is
less than `9/16`. If four centers existed, order them by their horizontal
coordinates. Some consecutive pair would have horizontal difference less
than `sqrt(369)/24`. Its squared distance would then be less than

```text
369/576 + 81/256 = 245/256 < 1,
```

contradicting the center separation.

If `t>1/16`, then `T` is empty by (2), so the capacities in (4) already
give at most `1+1+0+3=5` additional centers.

## 3. The case where the top region may be nonempty

Suppose `0<=t<=1/16`. In this case no lower-corner point is possible
either. Such a point would satisfy

```text
|p|² = 1+(1−t)²+a²+b²+2a+2(1−t)b
      >= 1+(1−t)²+1/4+(1−t)
       = 1+(3/2−t)²
      >= 1+(23/16)² = 785/256 > H².
```

Here we used `a²+b²>=1/4`, `a+b>=1/2`, and `1−t<=1`.

Every point outside `L`, `R`, and `T` must therefore lie beyond the lower
side of the block, so

```text
y <= t−3/2 <= −23/16.
```

This lower cap has horizontal span at most `sqrt(6)/2` and vertical span
at most `1/8`. Three centers would have a consecutive horizontal gap at
most `sqrt(6)/4`, giving squared distance at most

```text
6/16 + 1/64 = 25/64 < 1.
```

It consequently contains at most two centers. Adding the three other
capacities gives at most `1+1+1+2=5`, completing the proof.

The proof uses only necessary conditions on additional centers; it allows
their square orientations to vary independently throughout.
