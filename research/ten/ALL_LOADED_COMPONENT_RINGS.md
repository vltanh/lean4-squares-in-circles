# An all-loaded positive component is an enclosing physical ring

Use the original physical positive-stress certificate and body-pair graph
from [PHYSICAL_TREE_REDUCTIONS.md](PHYSICAL_TREE_REDUCTIONS.md), in the
radius window

```text
79/40 <= R <= 3/sqrt(2).
```

Suppose a whole nonzero positive component has positive circle load on
every one of its bodies. Then its original positive graph is a simple
cycle. In a hypothetical ten-square packing with `R²<9/2`, the cycle has
exactly seven bodies. Its actual body-center/contact-point polygon is a
Jordan curve enclosing the origin. Every square of the packing whose
center has norm less than one lies on the bounded side of this physical
ring.

These conclusions are conditional on the component being entirely
loaded. They do not assert that every positive component is entirely
loaded or that every cyclic component has this form.

The imported lower radius window and its source are recorded in
[EXPANDED_TREE_INVENTORY.md](EXPANDED_TREE_INVENTORY.md). The deductions
below use only the stated window and the linked hand lemmas.

## 1. Loaded center rays are more than 36 degrees apart

Every loaded square has a vertex on the containing circle. Its center
therefore has norm at least `R−1/sqrt(2)`. Since `sqrt(2)<29/20`, the
radius window and the universal square-center bound give

```text
5/4 < |c_i| < 25/16.                              (1)
```

Distinct square centers are at distance at least one. Suppose two centers
with radii in `[5/4,25/16]` made a minor angle at most `pi/5`. Since
`cos(pi/5)=(1+sqrt(5))/4>4/5`, their squared distance would be strictly
less than

```text
f(r,s)=r²+s²−(8/5)rs.
```

This quadratic is convex in each radius separately, so its maximum on
the radius rectangle occurs at a corner. Its three distinct corner
values are

```text
f(5/4,5/4)=5/8,
f(5/4,25/16)=225/256,
f(25/16,25/16)=125/128.
```

All are less than one, a contradiction. Thus every pair of loaded
center rays has minor angular separation strictly greater than `pi/5`.
In particular every successive cyclic gap of a set of loaded center
rays is greater than `pi/5`.

## 2. Only cyclic neighbors can touch

Section 4 of
[CYCLIC_STRESS_REDUCTIONS.md](CYCLIC_STRESS_REDUCTIONS.md) proves that two
touching loaded squares have center-ray separation at most

```text
alpha=2asin(1/(sqrt(2)R−1)) < 2pi/5.               (2)
```

For at least four loaded bodies, take their cyclic center-angle order.
If two are not consecutive, each of the two circular arcs joining their
center rays contains at least two successive gaps. Section 1 makes both
arcs longer than `2pi/5`, contradicting (2) if the bodies touch.
Consequently no nonconsecutive pair can touch, even at an unweighted
physical contact.

An entirely loaded positive component has no bridge: the bridge-cover
theorem supplies a circle-clear endpoint for every positive bridge. It
also cannot be an isolated loaded body. Its circle forces would then
balance without contacts, putting the origin in the convex hull of its
circle vertices and hence in the square; this is impossible when
`R>sqrt(2)`, since a unit square has diameter `sqrt(2)`.
Thus every vertex of this connected component has degree at least two.

Entirely loaded components with at most five bodies are excluded in
Section 5 of [CYCLIC_STRESS_REDUCTIONS.md](CYCLIC_STRESS_REDUCTIONS.md).
For a larger component, the preceding no-nonconsecutive-contact result
bounds every degree by two. All degrees are therefore exactly two, and
the positive graph is precisely the full cyclic-neighbor cycle.

All loaded centers have norm greater than one by (1). The sharp
[center-radius reduction](CENTER_RADIUS_REDUCTION.md) says that a
strictly subcritical ten-square packing has at most seven such centers.
Its entirely loaded component consequently has six or seven bodies.

## 3. Contact points lie between their two center rays

Every point `p` of a loaded square lies at angular distance strictly less
than `pi/5` from its center ray. Indeed, the square lies in the disk of
radius `1/sqrt(2)` about its center. That disk avoids the origin, and
the largest possible angular deviation from the center ray has sine
`1/(sqrt(2)|c_i|)`. By (1), this is less than `2sqrt(2)/5`. The strict
comparison with `sin(pi/5)` follows from

```text
2sqrt(2)/5 < 4/7 < sin(pi/5).
```

For the first inequality use `sqrt(2)<10/7`. For the second,
`sqrt(5)<9/4` gives
`sin²(pi/5)=(5−sqrt(5))/8>11/32>16/49`.

Let `m>=6` be the size of the loaded cycle, and choose increasing angle
lifts `phi_1,...,phi_m,phi_(m+1)=phi_1+2pi`. Each successive gap is
strictly less than `pi`: the other `m−1` gaps already sum to more than
`(m−1)pi/5>=pi`. It is therefore the minor angular separation of its
two touching centers, and (2) gives

```text
pi/5 < phi_(i+1)−phi_i <= alpha < 2pi/5.          (3)
```

Choose the actual application point `p_i` of the original positive pair
force between squares `i` and `i+1`. Since `p_i` belongs to both squares,
the angular bound just proved places it simultaneously within `pi/5`
of both center rays. The consistent lift consequently satisfies

```text
phi_i < arg(p_i) < phi_(i+1).                     (4)
```

For example, its lower bound from square `i+1` is
`arg(p_i)>phi_(i+1)−pi/5>phi_i`; the upper bound from square `i` is
analogous. No contact point or force normal has been replaced.

## 4. A physical Jordan ring enclosing the inner squares

Join the consecutive points

```text
c_1,p_1,c_2,p_2,...,c_m,p_m,c_1
```

by straight segments. Each center-to-contact segment lies in the
corresponding closed square, with its noncontact portion in that square's
interior. Equation (4) makes the polar angle strictly increase along
every segment. In fact each segment lies in the cone between its endpoint
rays, whose angular width is less than `pi`, and does not meet the origin.
The successive angular intervals are disjoint except at their endpoints.
The polygon is therefore simple, and its total polar-angle increase is
`2pi`. It is a Jordan curve with the origin on its bounded side.

This is a physical contact curve, contained in the union of the cycle's
squares. Its vertices use the original pair-contact application points;
the argument does not substitute center-to-center bars for the force
witnesses.

Each loaded square avoids the closed disk `B(0,1/2)`: a point of norm at
most `1/2` and its loaded circle vertex would have distance at least

```text
R−1/2 >= 59/40 > sqrt(2),
```

larger than a unit square's diameter. Thus the physical ring avoids this
closed half-radius disk. The disk is connected and contains the origin,
so the whole disk lies on the ring's bounded side.

Finally, an additional square with center norm less than one has its
open inscribed radius-`1/2` disk intersecting `B(0,1/2)`. Its interior
therefore meets the bounded side of the ring. Its interior cannot meet
the ring itself: an interior point lying on the closed boundary of any
cycle square would have a neighborhood intersecting that square's
interior, violating disjointness. Since the additional square's interior
is connected, all of it lies on the bounded side. Taking closures gives
the same containment in the closed bounded region for the entire square.

## 5. A loaded square occupies less than sixty degrees as viewed from zero

Choose a loaded square's own axes so its center is `(a,b)`, with
`a>=b>=0`. Then

```text
(a+1/2)²+(b+1/2)²=R²,
a>1/2.
```

Let `omega` be the total angular width of the square as viewed from the
origin. If `b>=1/2`, its visible extreme corners are
`(a+1/2,b−1/2)` and `(a−1/2,b+1/2)`. With `t=a+b`,

```text
tan(omega)=t/(R²−t−1),
t<=sqrt(2)R−1.
```

The denominator is positive, and the displayed ratio increases with t.
Consequently

```text
omega <= 2atan(1/(sqrt(2)R−1)) < pi/3.
```

For the last strict inequality it suffices that
`R>(1+sqrt(3))/sqrt(2)`. Indeed,
`sqrt(3)<7/4` and `sqrt(2)>7/5` bound that threshold by
`55/28<79/40`.

If `0<=b<=1/2`, put `x=a−1/2>0`. The visible endpoints are the inner
side's vertices `(x,b−1/2)` and `(x,b+1/2)`. Suppose their angular
separation were at least `pi/3`. Their cross product is x and their dot
product is `x²+b²−1/4`, so this would imply

```text
x²+b²−1/4 <= x/sqrt(3),
(x−1/(2sqrt(3)))²+b² <= 1/3.
```

Apply the triangle inequality to the farthest vertex

```text
(x+1,b+1/2)
 = (x−1/(2sqrt(3)),b) + (1+1/(2sqrt(3)),1/2).
```

It would give

```text
R <= 1/sqrt(3) + sqrt(4/3+1/sqrt(3))
  < 7/12 + sqrt(23/12)
  < 79/40,
```

a contradiction. Here `1/sqrt(3)<7/12` follows by squaring, and the last
comparison follows from

```text
(79/40−7/12)²−23/12 = 289/14400 > 0.
```

Thus `omega<pi/3` in both cases.

## 6. Only a seven-body loaded ring remains in the subcritical case

The physical ring in Section 4 surrounds zero, so it meets every ray from
zero. Since it is contained in the union of the loaded component's
squares, their angular viewing intervals cover the entire circle. Six
squares, each of viewing width strictly less than `pi/3`, cannot do this.
The six-body alternative in Section 2 is therefore excluded.

In a subcritical ten-square packing an entirely loaded component must
accordingly consist of seven bodies. Every loaded center has norm greater
than one, so the center-radius reduction makes the other three centers
strictly less than one. Section 4 puts all three remaining squares inside
the physical ring.

The remaining completion problem for this component type is now precise:
exclude three disjoint unit squares inside a circle-loaded seven-square
contact ring in the stated radius window. This manuscript does not yet
bound the inner region's capacity or exclude that last ring configuration.
