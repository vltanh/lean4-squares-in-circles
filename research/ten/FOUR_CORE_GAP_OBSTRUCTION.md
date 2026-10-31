# Six abstract arcs can fit around a four-square core

This exact example disproves the proposed unrestricted bound that the
complement of four inner-square traces can hold at most five disjoint arcs
of angle `pi/4`. It is a four-square core, not a ten-square packing and not
a counterexample to the target radius.

Put

```text
r = sqrt(1+1/sqrt(2)),
b = 1/sqrt(2),
a = acos(1/r).
```

Take the four axis-parallel unit squares with centers

```text
(-1/2,b), (1/2,b), (-1/2,b-1), (1/2,b-1).
```

They tile the rectangle `[-1,1] x [b-3/2,b+1/2]`, and their interiors are
disjoint. The upper centers have squared norm `3/4`; the lower centers have
squared norm `7/4-sqrt(2)`. All four centers lie strictly inside the unit
disk, and all four squares lie in the disk of squared radius `9/2`.

The two lower squares lie wholly inside the test circle, because their
farthest squared radius is

```text
1+(3/2-b)^2 = 15/4-3/sqrt(2) < r^2.
```

The right upper square meets the test circle in the angular interval

```text
[a,3pi/8].
```

Its first endpoint lies on `x=1`; its last lies on `y=b+1/2`, since
`b+1/2=r cos(pi/8)`. The left upper square gives the reflected interval
`[5pi/8,pi-a]`. Thus there are two complementary gaps:

* the upper gap has angle `pi/4`;
* the gap around the lower semicircle has angle `pi+2a`.

Since `pi/8<a<pi/4`, the second gap has angle strictly between `5pi/4` and
`3pi/2`. It can hold five disjoint arcs of angle `pi/4`. The upper gap holds
one more. Therefore the abstract gap capacity is exactly six.

The inequalities are stable under a small decrease of `b`: the lower squares
remain inside the test circle, and the upper gap becomes strictly larger
than `pi/4`. Consequently merely replacing closed gaps by open gaps does
not repair the proposed unrestricted capacity bound.

## What this does and does not rule out

The example violates the necessary high-center localization from
[RADIAL_COUNT_LOCALIZATION.md](RADIAL_COUNT_LOCALIZATION.md): its two larger
center norms are `sqrt(3)/2<9/10`. Thus it does not disprove a gap-capacity
theorem under the additional two-small/two-large localization.

It also shows why physical square geometry can be stronger than abstract
arc placement. At the exact parameter `b=1/sqrt(2)`, no additional square
with center norm at least `1`, contained in the target disk, can use the
upper gap. Its circle arc would have to have angle exactly `pi/4`; the
equality classification in
[CENTER_RADIUS_REDUCTION.md](CENTER_RADIUS_REDUCTION.md) permits only types
S, C, and D. All have arc midpoint direction `pi/2`. At either endpoint
their side directions are vertical or make angle `pi/4` with the horizontal.
The two core squares instead have horizontal sides at the shared endpoints
`(+-1/2,b+1/2)`, and these points are strictly inside those sides. Distinct
side lines crossing there force overlapping square interiors in a local
open wedge. Hence no equality square fits in the upper gap.

The lower gap can hold at most five outer-square arcs. Therefore this exact
four-square core cannot be completed by six outer-center squares, despite
its abstract gap capacity of six. This last argument is specific to the
displayed parameter; a general core completion theorem remains open.
