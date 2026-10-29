# The diagonal transmitter's scalar bounds alone do not force enough outer trace

**Status:** exact counterexample to a proposed intermediate reduction;
independent full mathematical audit passed (2026-10-29). This is not a ten-square packing or a realization
of the four-loaded stress component.

Let `k=1/sqrt(2)` and `r=sqrt(1+k)`. Take three axis-parallel unit squares
with centers

```text
U: (7/25,k-1),       B: (-18/25,k-1),       C: (0,k).
```

The first two squares share a vertical side. The bottom side of C has
the same height as the top sides of U and B. Thus their open interiors
are disjoint, and all three centers lie in the open unit disk.

The proposed diagonal transmitter U satisfies all the scalar localization
conditions used in
[DIAGONAL_FIVE_CYCLE_INNER_TRACE.md](DIAGONAL_FIVE_CYCLE_INNER_TRACE.md).
Nevertheless B and C have total angular trace on the test circle strictly
less than `pi/4`. Hence those scalar conditions alone cannot exclude the
three-inner-center case by requiring more than `pi/4` of inner-square
trace. The loaded path geometry must enter such an argument.

## 1. The scalar transmitter conditions

Choose the transmission direction along `(1,1)/sqrt(2)`, and its positive
perpendicular along `(-1,1)/sqrt(2)`. The center coordinates are

```text
m=1/2-18k/25<0,       h=1/2-32k/25<0.
```

The origin lies strictly inside U because both its own side-coordinate
center magnitudes are less than `1/2`. Put `a=|m|`, `b=|h|`. Directly,

```text
a^2+b^2+(2k/sqrt(3))b
 =1973/1250-sqrt(2)+32/(25sqrt(3))-1/sqrt(6)
 <2477/5000<1/2.                                    (1)
```

For the displayed strict rational bound use

```text
sqrt(2)>7071/5000,    1/sqrt(3)<231/400,
1/sqrt(6)>51/125.
```

Their squared checks have positive differences respectively `959`, `83`,
and `19`. Thus U meets the strict greater-than-120-degree chord condition.

The nearer of its two transmission endpoints has squared norm

```text
(k-a)^2+b^2=849/625-k>1521/2500>1/2,                 (2)
```

using `k<3/4`. Both endpoints therefore have norm greater than k, which
is at least `R-sqrt(2)` throughout `R<=3/sqrt(2)`. The other recorded
center bound holds too: `|c_U|^2<1/4`, whereas
`[1-(R-sqrt(2))^2]/2>=1/4` in that window.

The two small-coordinate bounds also hold directly: `a<1/25` and
`b<1/sqrt(6)`, with the latter already implied by (1).

## 2. The two additional squares consume less than pi/4

The farthest vertex of C has squared norm

```text
1/4+(k+1/2)^2=1+k=r^2.
```

Hence C is contained in the test disk and has no open trace on its circle.
The same is true of U: its farthest squared vertex norm is
`(39/50)^2+(3/2-k)^2<1+k`.

For B the coordinate ranges are

```text
-61/50 <= x <= -11/50,
k-3/2 <= y <= k-1/2.
```

A point of B on the test circle must have `y<0`. Otherwise `0<=y<1/4`
and `|x|<5/4` would give squared norm less than `13/8`, while
`r^2=1+k>17/10>13/8`.

Moreover `y>=k-3/2>-4/5`, whereas `r/sqrt(2)>9/10`. Every test-circle
point in B therefore has

```text
x<0,       -r/sqrt(2)<y<0.
```

Its polar angle belongs to the open interval `(pi,5pi/4)`. The closed
intersection of B with the test circle stays strictly away from both
endpoints, so its angular measure is strictly less than `pi/4`.
Together with C's zero trace, this proves the claimed obstruction.

All elementary bounds used above follow from `7/10<k<3/4`. The three
squares also lie in every containing disk of the working radius window;
their largest squared vertex radius is that of B,
`(61/50)^2+(3/2-k)^2<9/4<(79/40)^2`.

This configuration has not been completed with the four required loaded
bodies. It only rules out a proof that discards their contact geometry
and retains solely the current scalar conditions on U.
