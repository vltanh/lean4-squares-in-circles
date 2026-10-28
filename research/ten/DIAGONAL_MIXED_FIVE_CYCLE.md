# The remaining mixed five-cycle cannot have two diagonal transmitters

Use the unique-circle-vertex normal form proved in
[SIDE_NORMAL_MIXED_FIVE_CYCLE.md](SIDE_NORMAL_MIXED_FIVE_CYCLE.md) for the
positive component `A-U-C-V-B-A`. Precisely `A,B,C` are loaded, and `U,V`
are unloaded degree-two transmitters. This note excludes the case in
which both transmitters are diagonal. It does not exclude the other
transmitter types or a central square with two circle vertices.

The argument below is geometric once the normal form has been obtained;
it does not use a further radius estimate or alter any physical force
normal.

## 1. Coordinates and the two diagonal transmitters

Translate C's bottom-left contact vertex to `P=(0,0)`, retaining its own
coordinate directions. The other transmission contact is

```text
Q=(d,0),                 0<d<1.
```

The respective outgoing unit directions are

```text
(-p,-q), (0,-1),         p>q>0, p^2+q^2=1.
```

The strict inequality `p>q` is the force-and-torque conclusion (2) of
the normal-form manuscript. Assume both U and V are diagonal
transmitters. Their widths along these directions are `sqrt(2)`, and
their two endpoints are opposite vertices. Thus U has vertices

```text
(0,0),
(-(p-q)/sqrt(2), -(p+q)/sqrt(2)),
(-sqrt(2)p, -sqrt(2)q),
(-(p+q)/sqrt(2), (p-q)/sqrt(2)),
```

while V has vertices

```text
(d,0), (d-1/sqrt(2),-1/sqrt(2)),
(d,-sqrt(2)), (d+1/sqrt(2),-1/sqrt(2)).
```

Put `w=p+q` and `v=p-q`; then `1<w<sqrt(2)` and `v>0`.
At height `y=-1/sqrt(2)`, the right endpoint of U's horizontal section
lies on its edge from P to its lower-right vertex and has coordinate

```text
x_U=-v/(sqrt(2)w).
```

This section has positive length: its height lies strictly between the
minimum and maximum heights of U, because `w>1`. V's section on the
same line is `[d-1/sqrt(2),d+1/sqrt(2)]`, also of positive length.
Its right endpoint is positive, whereas `x_U<0`. Disjoint square
interiors therefore require V's left endpoint to be at least `x_U`.
Consequently

```text
d >= 1/sqrt(2)-v/(sqrt(2)w)
  = sqrt(2)q/w.                                         (1)
```

## 2. Contact of the loaded endpoints gives the opposite bound

The contact on A reached through U is

```text
P_A=(-sqrt(2)p,-sqrt(2)q),
```

with inward supporting normal `(-p,-q)`. A unit square supported there
can extend at most q to the right. For vertex support, at most one
incident unit edge points to the right, and its horizontal component
is at most q; otherwise the inward supporting normal would lie outside
the cone of those edges. For side support, the unit side's horizontal
extent is q, while translation into the square in the normal direction
moves left. Hence

```text
max_x A <= -sqrt(2)p+q.                                  (2)
```

The contact on B reached through V is `P_B=(d,-sqrt(2))`, with inward
normal `(0,-1)`. Its one-sided leftward extent is at most one: at a
vertex only one incident unit edge can point left, and at a horizontal
support side that side itself has length one. Thus

```text
min_x B >= d-1.                                         (3)
```

A and B have a positive physical contact, so their horizontal projections
must overlap. Equations (2)--(3) imply

```text
d <= 1-sqrt(2)p+q.                                      (4)
```

## 3. The bounds are strictly incompatible

In terms of w and v, subtract the right side of (4) from that of (1):

```text
sqrt(2)q/w - (1-sqrt(2)p+q)
 = -(sqrt(2)-1)(sqrt(2)-w)/2
   + v[(sqrt(2)+1)/2-1/(sqrt(2)w)].                     (5)
```

Because `w>1`, the bracket exceeds `1/2`. Moreover
`w+v=2p>sqrt(2)`, so `sqrt(2)-w<v`. Substitution in (5) gives the
strict lower bound

```text
sqrt(2)q/w - (1-sqrt(2)p+q)
 > (2-sqrt(2))v/2 > 0.
```

This contradicts (1) and (4), and proves that U and V cannot both be
diagonal transmitters in the stated normal form. At least one of the
two remaining transmitters must therefore be a side transmitter.
