# Four original centers: planar matching and energy bounds

November 3, 2026. **A new necessary physical restriction; no original cell
or whole mask is closed by this theorem alone.** The unchanged accepted
counts at input commit `3c1f7527d17b2d983a39b85e5f8327fa70b9594a` are
197 CLOSED / 34 OPEN original cells for `001/00`, and 8 CLOSED / 24 OPEN
whole masks. No Lean, Lake or CI.

## 1. Quantified theorem and physical caller

Let A, B, C, D be four points in the Euclidean plane. Suppose every one
of their six mutual distances is at least one. Among the three perfect
matchings

```
AB | CD,    AC | BD,    AD | BC,
```

at least one satisfies

```
distance(first pair)^2 + distance(second pair)^2 >= 4.       (1)
```

Consequently

```
sum of all six squared distances >= 8,                     (2)
max of all six squared distances >= 2.                     (3)
```

The statements include all contacts, straight angles, collinear points
and degenerate convex hulls. No orientation, container, chain, selected
separator or sign hypothesis is required.

They apply to every choice of four of the same nine original physical
unit-square centers. Each original contains its open disk of radius
1/2 about its center. Two such open disks overlap when their centers
are less than one apart, which would violate physical interior
disjointness. Thus the required six distance bounds follow from the
six original physical pairs. No replacement square or new frame is used.

## 2. Convex quadrilateral

First suppose the four points are vertices of a strictly convex
quadrilateral, in cyclic order A, B, C, D. Put the intersection of the
diagonals at the origin and write

```
A = x e,   C = -y e,   B = z f,   D = -w f,
x,y,z,w > 0,   ||e|| = ||f|| = 1.
```

Give AB, BC, CD, DA the respective weights

```
yw, xw, xz, yz,
```

divided by `(x+y)(z+w)`. These weights are positive and sum to one.
Expanding their weighted squared lengths cancels every term containing
`e dot f` and gives exactly

```
weighted average of AB^2, BC^2, CD^2, DA^2 = xy + zw.
```

Every boundary edge has squared length at least one. Therefore
`xy+zw >= 1`. The diagonal matching satisfies

```
AC^2 + BD^2 = (x+y)^2 + (z+w)^2
            >= 4xy + 4zw >= 4.
```

This proves (1) in the convex case. In particular, no supposition that
the diagonals are perpendicular or have a common midpoint is involved.

## 3. All other convex hulls

If the four points are not the vertices of a strictly convex
quadrilateral, some point P belongs to the closed convex hull of the
other three. All points are distinct because their mutual distances
are at least one.

If P lies on a segment between two of the other points, those points
are on opposite rays from P. Their separation is at least two; its
square is at least four. Together with the disjoint remaining pair,
this already gives a matching sum at least five.

Otherwise P is strictly inside the triangle formed by the other
three points. The three successive sectors about P sum to 360 degrees
and each is strictly less than 180 degrees. At least one is at least
120 degrees. Let U and V be the corresponding two vertices. With
`a=||U-P||>=1` and `b=||V-P||>=1`, the cosine rule gives

```
||U-V||^2 >= a^2 + b^2 + ab >= 3.
```

The complementary pair, P and the third vertex, has squared distance
at least one. This proves (1). These two cases also cover every
collinear configuration and every point on the boundary of a
three-vertex convex hull.

## 4. Energy, diameter and sharpness

The matching supplied by (1) contributes at least four. Each of the
other four pairs contributes at least one, proving (2). At least one
of the two matching distances has square at least two, proving (3).

The constant eight in (2) is sharp: a unit square has four boundary
squared lengths equal to one and two diagonal squared lengths equal
to two. A unit-side rhombus whose diagonals are both at least one
also has total squared pair distance eight. These examples establish
sharpness of this four-point theorem only; they assert no nine-square
packing or whole-mask conclusion.

## 5. Exact affine rows on certified original bounds

For any proved interval `l<=t<=u`,

```
t^2 <= (l+u)t - lu,                                        (4)
```

because `(t-l)(u-t)>=0`. Apply (4) separately to the two components
of each original center difference and sum over a quadruple. Since
the true squared-distance sum is at least eight, its resulting
affine upper bound is at least eight. This gives a necessary linear
row on the entire original parent, using only previously certified
bounds for those same original differences.

Alternatively use

```
dx^2 + dy^2 = ((dx+dy)^2 + (dx-dy)^2)/2
```

and certified diagonal-difference bounds. Cartesian and diagonal
secants may be selected independently for each of the six pairs.
Every such selection is a valid unconditional necessary row; the
implementation retains all selections available from the input.

For a selected matching alternative (1), the same construction uses
its two pairs and threshold four. **A matching row is conditional.**
Its caller must retain all three matching alternatives as a complete
cover. No single selected matching may be asserted on an unsplit
original parent without a separate proof.

## 6. Shared quadratic variables and acceptance scope

In a common quadratic lift with original variables z and products
`X_ij=z_i*z_j`, (2) is inserted without a secant as the exact expansion
of `-sum ||c_i-c_j||^2 <= -8`. The matching version expands (1) with
right side `-4`, on its conditional branch. Physical configurations
embed in this lift. A numerical moment solution need not be a
physical configuration; a positive numerical margin is not a proof.

The source `computer_assisted/four_original_planar_rows.py` uses
exact fractions. All 126 four-original choices retain their labels.
A future accepted exclusion must separately supply full original
coverage, exact arithmetic replay, original-parent entailment and
its complete hand/table assembly. This theorem changes none of the
231 original IDs, 32 masks, 7,915 positional roots or 15 roadmap IDs.

## 7. Independent checks

The separate [geometric review](FOUR_ORIGINAL_PLANAR_ENERGY_INDEPENDENT_REVIEW.md)
checks the convex, interior, boundary and collinear arguments and the
complete three-matching cover. A standard-library-only checker reconstructs
the row coefficients using separate algebra and monomial indexing:

```
python -B -S research/nine/computer_assisted/verify_four_original_planar_rows.py
```

The saved [replay report](computer_assisted/four_original_planar_rows_replay.json)
records 11,390 exact coefficient identities, including all 126 energy
expansions, every available mixed Cartesian/diagonal secant, all 378
matching choices and their quadratic expansions. Its source hashes bind
the generator, checker and portable rational fixture. This is an algebra
and theorem review; the fixture does not certify a particular parent's
interval guards, and no cell exclusion is inferred from this check.
