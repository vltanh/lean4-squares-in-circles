# Completing a staggered four-square chain: an open three-square lemma

This note gives a hand reduction for one restricted configuration class. It
does **not** prove that a ten-square packing belongs to that class, or prove
that the class has no ten-square completion. The geometric reduction is
proved below; the arbitrary-orientation lemma needed to finish it is explicitly
left open.

## The four-square hypothesis

Let the containing disk be

```text
D = {(x,y) : x^2+y^2 <= 17/4},
R = sqrt(17)/2.
```

Assume the packing includes four axis-parallel unit squares with centers

```text
(-3/2,0),  (-1/2,t1),  (1/2,t2),  (3/2,0),
where -1/2 <= t1,t2 <= 1/2.
```

These four squares are mutually interior-disjoint and contained in `D`.
Write `A` for their union. The two outer squares have corners
`(+-2,+-1/2)` on the circle. The heights `t1,t2` remain independent throughout
the reduction.

## Proved barrier reduction

Every additional unit square in `D`, interior-disjoint from `A`, lies wholly
in either the closed upper half-plane or the closed lower half-plane.

First, its interior cannot meet the *closed* set `A`: an interior point on an
anchor boundary has a neighborhood in the additional square that intersects
the anchor's interior. Its interior also lies in the open disk. Thus its
connected interior lies in one component of `int(D) \ A`.

For each `-2 < x < 2`, the vertical section of `A` is a nonempty interval
containing `0`. On the four open strips cut by `x=-1,0,1`, respectively, its
lower and upper endpoints are

```text
[-1/2, 1/2],
[t1-1/2, t1+1/2],
[t2-1/2, t2+1/2],
[-1/2, 1/2].
```

At a common strip boundary, take the union of the two indicated intervals;
they intersect, so that union is again an interval containing `0`. Even the
extreme case `t1=-t2=1/2`, where the two middle squares meet only at a point,
leaves no open passage through their common boundary.

Consequently the complement between `x=-2` and `x=2` separates into an upper
region with `y>0` and a lower region with `y<0`. A path between those regions
would have to cross `A` or go around one of its ends. Going around an end is
impossible inside the open disk: at `x=+-2` the disk has `|y|<1/2`, and that
entire section is in the corresponding outer square. The two remaining side
caps have `x>2` and `x<-2` and are separate components.

A unit square cannot lie in a side cap. Each cap's horizontal width is
`R-2 < 1`, whereas the horizontal width of a unit square of any orientation
is `|cos(theta)|+|sin(theta)| >= 1`. Hence the connected interior of every
additional square is in the upper or lower region. Taking closures proves
the asserted closed-half-plane containment.

The exact value `17/4` matters to this argument. It makes the four outer
corners boundary contacts and closes the passages around the ends. A larger
disk does not give this barrier for free.

## A precise sufficient lemma that remains open

**Upper-triple rigidity conjecture.** Suppose three unit squares, of arbitrary
independent orientations, are pairwise interior-disjoint, are contained in
`D`, lie wholly in `y>=0`, and are interior-disjoint from the two fixed outer
squares centered at `(-3/2,0)` and `(3/2,0)`. Then, up to relabeling, they are
the three axis-parallel squares centered at

```text
(-1/2,1/2), (1/2,1/2), (0,3/2).
```

This is a nonempty candidate statement: the displayed T-shaped triple really
satisfies all the hypotheses. It is not being asserted as a proved theorem
for arbitrary orientations.

If this lemma is proved, it excludes a six-square completion of the original
four-square chain:

1. The barrier partitions the six additional squares into an upper group and
   a lower group.
2. Upper-triple rigidity implies that there cannot be four upper squares:
   apply the lemma to two different triples from those four. Both triples
   would have to be the same three geometric squares, contradicting
   interior-disjointness. Thus the upper group has at most three squares.
   Reflection gives the same upper bound on capacity: at most three below.
3. The six squares must therefore split as three above and three below. The
   upper triple is the displayed T, and the lower triple is its reflection.
4. The square at `(-1/2,1/2)` is disjoint from the inner anchor at
   `(-1/2,t1)` only when `1/2-t1 >= 1`, hence `t1=-1/2`. The right upper
   square similarly forces `t2=-1/2`. The reflected lower triple instead
   forces `t1=t2=1/2`. These requirements are incompatible.

The reduction does not require any statement about the orientations of the
six additional squares until the open lemma is invoked.

## The upper-triple lemma when the three squares are axis-parallel

This restricted version has a short proof. It checks the candidate statement
but does not discharge its arbitrary-orientation hypothesis.

Let `(x,y)` be the center of one of the upper squares. Half-plane containment
gives `y>=1/2`, and disk containment gives

```text
(|x|+1/2)^2 + (y+1/2)^2 <= 17/4,
```

so `y<=3/2` and `|x|<=sqrt(13)/2-1/2 < 5/2`.

If `|x|>1/2`, its horizontal center gap from the outer square on that side
is strictly less than `1`. Interior disjointness therefore requires `y>=1`.
The disk inequality then sharpens its horizontal bound to

```text
|x| <= sqrt(2)-1/2 < 1.
```

For `|x|<=1/2`, of course `|x|<1` already. Thus **every** upper square in this
restricted setting has its center in

```text
-1 < x < 1,       1/2 <= y <= 3/2.
```

For three centers in this horizontal interval, some pair has horizontal gap
strictly less than `1`: otherwise the ordered three would have total span at
least `2`. That pair must be separated vertically by at least `1`, so its
heights are exactly `1/2` and `3/2`.

The disk inequality forces the square at height `3/2` to have `x=0`.
Every other upper square has `|x|<1`, so disjointness from this top square
forces its height to be exactly `1/2`.

At height `1/2`, disjointness from the outer anchors forces `|x|<=1/2`.
The two lower squares are separated horizontally by at least `1`, so their
centers are exactly `(-1/2,1/2)` and `(1/2,1/2)`. There is no room for a
fourth square. This proves the restricted lemma and, consequently, excludes
a completion by six axis-parallel squares for every allowed `t1,t2`.

## The remaining gap

For rotated squares, disjointness need not give a horizontal or vertical
center gap of at least one. A tilted separating axis can separate squares
whose gaps in both fixed coordinates are smaller. Likewise, a square that
barely crosses `y=1/2` can have an arbitrarily short chord on that line;
counting each crossing as a full unit of width would be invalid.

A proof must control those orientations or use a different geometric
inequality. Neither the barrier nor the axis-parallel calculation supplies
that missing step. No conclusion about an arbitrary-oriented completion, or
about the unrestricted ten-square optimum, follows from this note alone.

## A failed shortcut: two symmetric stabbing points

One might try to prove the open lemma by finding two points `(+-a,b)` such
that every allowable upper square contains one of them. There are **no** such
universal symmetric points, even if closed-square membership is sufficient.
The obstruction already uses test squares contained in the smaller disk of
squared radius `q=21/5`. The fixed outer squares remain the obstacles from
the original `17/4` configuration; this does not assert that those obstacles
themselves fit in the smaller disk.

Put

```text
r = sqrt(21/5),
k = sqrt(2)/2,
d = sqrt(39/20)-1/2.
```

Consider the following four allowable test squares, individually:

- The axis-parallel square `B` centered at `(0,1/2)`.
- The axis-parallel squares `L,R` centered at `(-d,1)` and `(d,1)`.
- The square `H` turned by `pi/4`, centered at `(0,r-k)`. Its vertices are
  `(0,r)`, `(0,r-2k)`, and `(+-k,r-k)`.

All lie above `y=0` and avoid the interiors of the two fixed outer obstacles.
For `L,R`, their bottom edge has height `1/2`, and their farthest vertices
have squared norm `(d+1/2)^2+(3/2)^2=q`. For `B`, the maximum squared norm is
`5/4`. The diamond `H` has horizontal extent `[-k,k]`, entirely between the
outer obstacles, and its four vertices lie in the radius-`r` disk: the top
vertex is on the circle, the bottom vertex is between height `0` and `r`,
and the side vertices have squared norm
`k^2+(r-k)^2 <= r^2` because `r>=k`. Convexity then gives containment of the
whole square.

Suppose a symmetric point pair `(+-a,b)`, with `a>=0`, hits all four test
squares. The two disjoint lateral squares `L,R` force

```text
a >= d-1/2 = sqrt(39/20)-1.
```

Hitting `B` forces `b<=1`. Membership in `H` requires

```text
a + |b-(r-k)| <= k,
```

and consequently

```text
a <= b+sqrt(2)-r <= 1+sqrt(2)-sqrt(21/5).
```

These bounds are incompatible. Indeed,

```text
sqrt(39/20) > 139/100,
sqrt(21/5) > 51/25,
sqrt(2) < 71/50,
```

as follows by squaring positive quantities. Hence
`sqrt(39/20)+sqrt(21/5) > 343/100 > 342/100 > 2+sqrt(2)`.

### The asymmetric version also fails

In fact, no two fixed points, symmetric or otherwise, hit every allowable
individual square. Retain `L,R,H` above, and replace `B` by the two
axis-parallel squares

```text
B_L = [-1,0] x [0,1],
B_R = [0,1] x [0,1].
```

They avoid the outer obstacles in their interiors and lie in the disk of
squared radius `2`, so they are allowable in the same smaller test disk.
The five-square family `B_L,B_R,L,R,H` has no two-point transversal, even
when boundary membership counts.

Indeed, `L` and `R` are disjoint closed sets: their nearest horizontal
coordinates to the origin have absolute value
`d-1/2=sqrt(39/20)-1>0`. A hypothetical pair therefore has one point `p` in
`L` and the other `p'` in `R`. Since `R` misses `B_L` and `L` misses `B_R`,
one must have `p in B_L` and `p' in B_R`. Both points consequently satisfy

```text
y <= 1,       |x| >= sqrt(39/20)-1.
```

But any point of `H` with `y<=1` satisfies

```text
|x| <= y+sqrt(2)-r <= 1+sqrt(2)-sqrt(21/5),
```

which contradicts the exact strict inequality proved above. Neither point
can hit `H`.

These test squares are families to be stabbed, **not** simultaneous
interior-disjoint packings. Thus neither obstruction refutes upper-triple
rigidity. They rule out universal two-point transversals of the allowable
individual squares. A configuration-dependent argument would need separate
justification.
