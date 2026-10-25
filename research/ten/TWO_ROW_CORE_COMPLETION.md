# A family of staggered two-row cores has total capacity at most nine

Put `Q=9/2` and `r=sqrt(1+1/sqrt(2))`. Suppose a packing in the
origin-centered disk of squared radius Q contains the four axis-parallel
unit squares centered at

```text
(-1/2,-t), (1/2,-t), (-b,1-t), (b,1-t),
3/10 <= t <= 8/25,
3/5 <= b <= 7/10.
```

Then it has at most five additional squares, even when their orientations
are arbitrary. Thus this whole two-parameter core family cannot occur in a
ten-square packing in the target disk.

The family includes the exact counterexample to localized abstract gap
counting in
[LOCALIZED_FOUR_CORE_GAP_OBSTRUCTION.md](LOCALIZED_FOUR_CORE_GAP_OBSTRUCTION.md).
Every core in this family leaves room for six abstract arcs of angle
`pi/4`; the proof below uses the actual shape of any square trying to use
the upper gap.

## 1. The core and its two circle gaps

The lower squares fill

```text
K_0 = [-1,1] x [-t-1/2,1/2-t].
```

The upper squares have horizontal intervals
`[-b-1/2,-b+1/2]` and `[b-1/2,b+1/2]`, and vertical interval
`[1/2-t,3/2-t]`. Write

```text
z=3/2-t,    59/50 <= z <= 6/5.
```

The square interiors are disjoint. The lower center squared norms are at
most `881/2500< (13/20)^2`; the upper center squared norms lie between
`514/625>(9/10)^2` and `49/50<1`. All four squares lie in the target disk.

The lower squares lie wholly inside the test circle: their farthest squared
radius is at most `1+(41/50)^2=4181/2500<r^2`. For the upper-right square,
the two corners adjacent to its outward corner have squared norms at most
`37/25<r^2`, while the outward corner lies outside the test circle. Its
circle trace is therefore exactly

```text
[alpha,beta],
alpha=acos((b+1/2)/r),
beta=asin(z/r).
```

The upper-left square gives the reflected trace `[pi-beta,pi-alpha]`.
Since both `b+1/2` and z belong to `[11/10,6/5]` or the smaller interval
displayed above, and

```text
r/sqrt(2) < 1 < b+1/2,z <= 6/5
  < (1+sqrt(2))/2 = r cos(pi/8),
```

the complementary gaps satisfy

```text
pi/4 < G_top=pi-2beta < pi/2,
5pi/4 < G_bottom=pi+2alpha < 3pi/2.                 (1)
```

They have abstract capacities one and five, respectively.

## 2. Every additional center lies outside the unit disk

Every point of the unit disk is within distance at most `1/5` of the core.
Indeed, a point `(x,y)` of that disk has `-1<=x,y<=1`. If `y<=1/2-t`, its
distance to the lower rectangle `K_0` is at most `1/2-t<=1/5`. If
`y>=1/2-t`, its height is within the upper squares' vertical interval, and
its horizontal distance to their union is at most `b-1/2<=1/5`.

An additional unit square contains the open disk of radius `1/2` about its
center. Such a disk would overlap the core if its center lay in the closed
unit disk. Hence every additional center has norm strictly greater than one.

Containment in `D_Q` also bounds every unit-square center norm by

```text
A=(sqrt(17)-1)/2 < 25/16.                            (2)
```

This follows from the lower bound `u^2+u+1/2` for the farthest squared
vertex norm of a square whose center norm is u.

By [CENTER_RADIUS_REDUCTION.md](CENTER_RADIUS_REDUCTION.md), each additional
square occupies one connected arc of angle at least `pi/4` on the test
circle. Its arc must lie in one of the two gaps in (1).

## 3. A square using the top gap must cross a blocked horizontal section

Suppose an additional square S uses the upper gap. Let its center be
`(x_c,y_c)`, with norm u. The radial point `r(x_c,y_c)/u` is strictly
inside S: its distance from the center is `|r-u|<1/2`, using

```text
1<u<25/16,    5/4<r<3/2.
```

Consequently the center's polar direction lies in the upper gap. This gives

```text
y_c >= z/r,
|x_c| <= u sqrt(1-z^2/r^2).                         (3)
```

Since `z>7/6` and `r^2<7/4`,

```text
1-z^2/r^2 < 2/9,
x_c^2 < (25/16)^2(2/9) < 9/16.
```

Thus `|x_c|<3/4`. Every unit square has horizontal half-width at most
`sqrt(2)/2<3/4`, so its entire horizontal extent lies in `(-3/2,3/2)`.

Let m and M be the lowest and highest heights of S, and write its vertical
width as `w=c+s`, where `c>=s>=0` and `c^2+s^2=1`. From (3), the
half-width bound `w/2>=1/2`, and `r<21/16`,

```text
M-z >= y_c+1/2-z
    >= 1/2-z(1-1/r)
     > 1/2-(6/5)(5/21)
      = 3/14 > 1/5.                                (4)
```

Writing `R=3/sqrt(2)<17/8`, disk containment also gives

```text
z-m >= z-R+w > w-23/24.                            (5)
```

In particular `m<z<M`: the upper inequality follows from (4), and
`m<=R-1<9/8<z` gives the lower one.

The horizontal chord of S at height z has length strictly greater than
`2/5`. For an axis-parallel square its length is one. Otherwise the exact
chord formula is

```text
min(1/c, (z-m)/(cs), (M-z)/(cs)).
```

The first term is at least one, and the last exceeds `2/5` by (4) and
`cs<=1/2`. For the middle term, (5) suffices because

```text
w-23/24 > (w^2-1)/5 = (2/5)cs,
                  1<=w<=sqrt(2).
```

To check this last inequality, subtract its right side. The resulting
quadratic is concave in w and positive at both endpoints: its values are
`1/24` and `sqrt(2)-139/120`.

At height z, the core occupies the two closed intervals

```text
[-b-1/2,-b+1/2],    [b-1/2,b+1/2].
```

Inside `(-3/2,3/2)`, their complement has three components with lengths

```text
1-b,    2b-1,    1-b,
```

each at most `2/5` because `3/5<=b<=7/10`. The open interior of S cannot
meet a core boundary point: a neighborhood of that point inside S would
also meet the core's interior. Its horizontal chord, which crosses its
interior and has length greater than `2/5`, therefore cannot fit in any of
the three free intervals. This is a contradiction.

No additional square can use the upper gap.

## 4. Count the remaining arcs

All additional squares must use the lower gap, whose angular length is
strictly less than `3pi/2` by (1). Six disjoint arcs of length at least
`pi/4` cannot fit there. There are therefore at most five additional
squares, proving total capacity at most nine throughout the stated family.
