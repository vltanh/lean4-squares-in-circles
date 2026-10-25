# Radial localization does not bound abstract gap capacity by five

The abstract circle-gap approach also fails under the two-small/two-large
center localization. The following four-square core satisfies that
localization and leaves room for six disjoint abstract arcs of angle `pi/4`,
with positive clearance. This is not a ten-square packing.

Let `r=sqrt(1+1/sqrt(2))` be the test-circle radius. Take axis-parallel unit
squares with centers

```text
(-1/2,-3/10), (1/2,-3/10),
(-13/20,7/10), (13/20,7/10).
```

Their two rows are separated vertically by `1`; within each row the center
spacing is at least `1`. The square interiors are therefore disjoint.
The two lower centers have squared norm `17/50`; the two upper centers have
squared norm `73/80`. Thus precisely two centers have norm below `13/20`,
and the other two have norm strictly between `9/10` and `1`.

All four squares lie in the containing disk of squared radius `9/2`.
The lower squares lie wholly inside the test circle, since their farthest
squared radius is `41/25<r^2`.

The upper right square is

```text
[3/20,23/20] × [1/5,6/5].
```

Its inward adjacent corners lie inside the test circle and its outward
corner lies outside. Consequently its circle trace is the angular interval

```text
[alpha,beta],
alpha = acos((23/20)/r),
beta  = asin((6/5)/r).
```

The upper left square gives the reflected interval `[pi-beta,pi-alpha]`.
The complementary gaps have angles

```text
G_top = pi-2beta,
G_bottom = pi+2alpha.
```

Using `r cos(pi/8)=(1+sqrt(2))/2`, we have

```text
6/5  < r cos(pi/8),
23/20 < r cos(pi/8),
```

so `beta<3pi/8` and `alpha>pi/8`. Also `r<sqrt(2)` gives
`beta>pi/4` and `alpha<pi/4`. Therefore

```text
pi/4 < G_top < pi/2,
5pi/4 < G_bottom < 3pi/2.
```

One abstract arc of angle `pi/4` fits strictly inside the upper gap, and
five such arcs fit strictly inside the lower gap. The gap capacity is
exactly six.

This rules out a proposed proof that uses only the four core traces and
the minimum arc length of an outer square, even after applying
[RADIAL_COUNT_LOCALIZATION.md](RADIAL_COUNT_LOCALIZATION.md). A successful
completion argument must also use the physical shapes, locations, or
orientations of the additional squares. It does not follow that six actual
outer squares can fit around this core.
