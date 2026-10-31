# A diagonal five-cycle transmitter forces other inner squares to protrude

**Status:** hand deduction; independent mathematical review passed (2026-10-29). This is a further
restriction on C19, not an exclusion of the whole component.

Use the four-loaded five-cycle and its diagonal transmitter U from
[MIXED_FIVE_FOUR_LOADED_GEOMETRY.md](MIXED_FIVE_FOUR_LOADED_GEOMETRY.md).
Put

```text
k=1/sqrt(2),       s=3/8,       r=sqrt(1+1/sqrt(2)).
```

**Theorem.** U is wholly inside the open disk of squared radius `3/2`.
It contains an open arc of the circle of radius s with angular length
strictly greater than `5pi/6`. At most one other packing square can be
wholly contained in the closed disk of radius r.

Consequently, if there are three inner centers, at least one of the other
two inner squares protrudes beyond that disk; if there are four inner
centers, at least two of the other three do. A square's center lying in
the open unit disk does not mean that the whole square lies in this disk.

## 1. Both diagonal coordinates of the center are small

In coordinates along and perpendicular to the transmission line, write
the center of U as `(m,h)` and set `a=|m|`, `b=|h|`. The cited theorem
already proves

```text
a+b<k,
a^2+b^2+(2k/sqrt(3))b<k^2,                         (1)
```

and each transmission endpoint has norm strictly greater than `11/20`.
The second inequality in (1) implies

```text
b<1/sqrt(6),
```

since substituting `b=1/sqrt(6)` into its last two terms gives exactly
`k^2=1/2`, and those terms increase for nonnegative b.

The nearer transmission endpoint has squared norm `(k-a)^2+b^2`.
Since `a<k`, its lower bound gives

```text
(k-a)^2 > 121/400-1/6=163/1200,
a<k-sqrt(163/1200)<1/sqrt(6).                       (2)
```

For the last comparison, both sides of
`sqrt(163/1200)>k-1/sqrt(6)` are positive. Their squared comparison follows
from

```text
(k-1/sqrt(6))^2=2/3-1/sqrt(3)<2/15=160/1200,
```

using `1/sqrt(3)>8/15`, whose squared check is `225>192`.

Let x,y be the absolute coordinates of U's center in its own side frame.
Rotation by 45 degrees and (1)--(2) give

```text
x+y=sqrt(2) max(a,b)<1/sqrt(3),
x^2+y^2=a^2+b^2<1/3.                               (3)
```

The farthest squared vertex radius is therefore

```text
x^2+y^2+x+y+1/2 < 5/6+1/sqrt(3)<3/2,
```

where `1/sqrt(3)<2/3` follows by squaring. Convexity proves the first
assertion of the theorem. In particular U lies wholly in the radius-r
disk, since `3/2<1+1/sqrt(2)`.

## 2. U contains a small-circle arc longer than 150 degrees

The origin lies strictly inside U by the cited geometric theorem, so
`x,y<1/2`. Define

```text
P=(1/2-x)/s>0,       T=(1/2-y)/s>0.
```

The elementary small-circle computation in
[THREE_CORE_INNER_STABILITY.md](THREE_CORE_INNER_STABILITY.md) gives an
open arc in U of angular length

```text
L=pi/2+asin(min(P,1))+asin(min(T,1)).                (4)
```

The two far sides are beyond the small circle because their distances
from zero are at least `1/2>s`. Formula (4) describes the arc through the
quadrant pointing from zero toward U's center, extending to the two near
side cuts. If the entire circle lies in U, the claimed subarc still exists.

Equation (3) and `1/sqrt(3)<5/8` give

```text
P+T=(1-x-y)/s > (1-5/8)/(3/8)=1.                    (5)
```

Here the radical comparison has squared check `64<75`.
If either P or T is at least one, (4) gives `L>=pi>5pi/6`.
Otherwise convexity of arcsine on `[0,1]` and (5) give

```text
asin(P)+asin(T)>=2 asin((P+T)/2)>2 asin(1/2)=pi/3.
```

Thus `L>5pi/6`, proving the second assertion.

## 3. Two other squares cannot both have no trace on the larger circle

Every unit square wholly contained in the closed radius-r disk supplies
an open arc on the radius-s circle of length at least `5pi/8`, by
[THREE_CORE_INNER_STABILITY.md](THREE_CORE_INNER_STABILITY.md). If two
other packing squares were both so contained, their two arcs and the
arc in U would have total angular length strictly greater than

```text
5pi/6+2(5pi/8)=25pi/12>2pi.
```

Those arcs lie in disjoint square interiors, which is impossible on one
circle. At most one other square can therefore be wholly contained in
the radius-r disk. The stated consequences for three and four inner
centers follow because U itself has center norm below one.

This does not yet bound the larger-circle traces of the squares forced
to protrude. Their interaction with the outer squares remains open.
