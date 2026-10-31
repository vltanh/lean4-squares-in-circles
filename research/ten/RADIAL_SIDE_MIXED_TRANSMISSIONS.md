# A radial-side central square forces two diagonal transmitters

Consider the positive component `A-U-C-V-B-A`, with precisely A,B,C
loaded and U,V unloaded degree-two transmitters. Suppose C has two
vertices on the containing circle. In a hypothetical ten-square packing
in the target radius range, **both U and V must be diagonal transmitters**.

The side-side case is excluded by
[RADIAL_SIDE_MIXED_FIVE_CYCLE.md](RADIAL_SIDE_MIXED_FIVE_CYCLE.md).
This note excludes the remaining side-diagonal case. The diagonal-
diagonal case is not excluded here.

## 1. The explicitly imported, slightly sharper lower window

We use

```text
R^2 > 5/2+sqrt(2),              R<=3/sqrt(2).             (1)
```

This holds for every ten-square packing by the same n=8 source used in
[EXPANDED_TREE_INVENTORY.md](EXPANDED_TREE_INVENTORY.md), Section 1.
At main commit `cd9127ff04e089909cc460d817ea28c4b1eb9ea9`,
[Eight.lower_bound and radius_eq_stationary](https://github.com/vltanh/lean4-squares-in-circles/blob/cd9127ff04e089909cc460d817ea28c4b1eb9ea9/SquaresInCircles/Eight/Uniqueness.lean)
give `R^2>=qStar` for an eight-square subpacking, while
[ExactFamily.qStar_limits](https://github.com/vltanh/lean4-squares-in-circles/blob/cd9127ff04e089909cc460d817ea28c4b1eb9ea9/SquaresInCircles/Eight/ExactFamily/Stationary.lean)
gives `qStar>7831/2000`. The exact comparison needed here is

```text
7831/2000-5/2 = 2831/2000 > sqrt(2),
2831^2-2(2000)^2 = 14561 > 0.
```

The imported `qStar_limits` theorem retains the arithmetic dependency
disclosed in the inventory: its coarse stationary bracket uses the
repository's generated exact interval data. This note is a hand deduction
from that explicit lower bound, not a new independent hand derivation of
the n=8 bracket or a new local Lean build. The previous weaker window
`R>=79/40` follows as before and will be used for convenient estimates.

Rotate and then reflect the horizontal coordinate so that

```text
C=[-L-1,-L] x [-1/2,1/2],
L=sqrt(R^2-1/4)-1.
```

Equation (1) gives

```text
L>sqrt(2)-1/2,
91/100<L<17/16.                                        (2)
```

The second lower bound follows already from `R>=79/40`, as verified in
[PARALLEL_MIXED_FIVE_CYCLE.md](PARALLEL_MIXED_FIVE_CYCLE.md).

## 2. Contact positions and endpoint center bounds

By Section 1 of the side-side note, both transmission contacts lie on
C's right side, including its two corners. Their outgoing origin
torques have the strict sign of their heights, and vanish only at the
side midpoint. Torque balance therefore puts one contact above zero
and one below zero, unless both are the midpoint. That exceptional case
has parallel outgoing directions and is already excluded by the
parallel-transmission theorem.

Assume exactly one transmitter is side type. Reflect vertically and
relabel so that U is side type at the upper contact and V is diagonal
at the lower contact. Write their widths as `W_U=1`, `W_V=sqrt(2)`.

For an upper-corner transmission of width W and direction `(p,q)`, where
`p,q>=0` and `p^2+q^2=1`, its endpoint square is supported at

```text
Q=(Wp-L,1/2+Wq)
```

with inward normal `(p,q)`. If its center is `(X,Y)`, elementary support
geometry gives

```text
X >= (W+1/2)p-q/2-L,
Y >= 1/2+(W+1/2)q-p/2,
X <= W-L+1/sqrt(2).                                   (3)
```

For completeness, at a supported vertex the vector from that vertex to
the square center has length `1/sqrt(2)` and its direction differs from
the inward normal by at most `pi/4`. Thus its horizontal and vertical
components are respectively at least `(p-q)/2` and `(q-p)/2`; its
horizontal component is at most `1/sqrt(2)`. At a side point the vector
is a convex combination of those at the side endpoints, so the same
linear bounds hold.

Every square center has norm less than `25/16`. If `p<=12/25`, then
`q>7/8`, and the lower bound for Y in (3), using W>=1, gives

```text
Y > 1/2+(3/2)(7/8)-(1/2)(12/25)
  =629/400 >25/16,
```

a contradiction. Hence `p>12/25` and `q<22/25`. The lower bound for X
in (3) now yields

```text
X > (3/2)(12/25)-(1/2)(22/25)-17/16
  =-313/400.                                          (4)
```

For a side-interior contact the direction is horizontal, and
`X>=W-L+1/2>0`; no corner estimate is needed. Vertical reflection proves
the same horizontal bounds at a lower contact.

Use `sqrt(2)<99/70` and (2) in the upper bound of (3). For the two loaded
endpoints, the bounds (3)--(4) consequently imply

```text
|X_A|<x_0:=279/350,
|X_B|<z_0:=212/175.                                    (5)
```

The lower bound `-313/400` is greater than `-x_0`, so it causes no loss
when passing to absolute values.

## 3. The endpoint centers lie on opposite sides of the horizontal axis

Section 2 of
[RADIAL_SIDE_MIXED_FIVE_CYCLE.md](RADIAL_SIDE_MIXED_FIVE_CYCLE.md)
is a one-endpoint lemma: the loaded endpoint of a width-one transmission
from an upper contact must lie wholly in `y>0`. Thus `Y_A>0` here,
regardless of the type of the other transmitter.

If V's contact is the lower corner, its direction is `(p,-q)` and the
reflected center-support bound gives

```text
Y_B <= -1/2-(sqrt(2)+1/2)q+p/2 <=0.
```

Equality is impossible for a loaded endpoint: its center norm is greater
than `71/56`, whereas (5) gives `|X_B|<212/175<71/56`.
Therefore `Y_B<0` in the corner case.

It remains to handle V's contact in the relative interior of the lower
half-side. Its direction is horizontal, and B has minimum horizontal
coordinate

```text
l=sqrt(2)-L>0.
```

By (2),

```text
l+sqrt(2)=2sqrt(2)-L<L+1<R.
```

The loaded-square sign lemma from Section 1 of
[PARALLEL_MIXED_FIVE_CYCLE.md](PARALLEL_MIXED_FIVE_CYCLE.md)
therefore says that `Y_B` is nonzero and every loaded vertex of B has
that same strict vertical sign.

Suppose `Y_B>0`. Every circle vertex of A is also above zero. Furthermore
every point of either endpoint square has horizontal coordinate less than
`L+1`: its contact has coordinate `Wp-L<=sqrt(2)-L`, and the square's
diameter is `sqrt(2)`, so its horizontal coordinate is at most
`2sqrt(2)-L<L+1`.

Define the linear functional

```text
H(x,y)=y-x/[2(L+1)].
```

On a circle point with `y>0` and `x<L+1`, H is strictly positive. If
`x<=0`, this is immediate. If `0<x<L+1`, the circle equation
`R^2=(L+1)^2+1/4` implies `y>1/2`, which proves the assertion too.
Both circle vertices of C, `(-L-1,+-1/2)`, have H>=0. Thus H is
nonnegative on every circle-load vector in this component and strictly
positive on the positive loads of A and B. Their positive weighted sum
cannot be zero. This contradicts the sum of the component's force
equations, which cancels all internal contact forces. Therefore `Y_B<0`
in the side-interior case as well.

## 4. The loaded endpoint centers are too far apart to touch

Each loaded center has norm at least `R-1/sqrt(2)`, so

```text
|c_A|,|c_B|>r_0:=71/56,
x_0,z_0<r_0.
```

Their vertical coordinates have opposite signs. Set `x=|X_A|` and
`z=|X_B|`. It follows that

```text
|c_A-c_B|^2
 > 2r_0^2-2xz+2sqrt((r_0^2-x^2)(r_0^2-z^2)).             (6)
```

Using absolute horizontal coordinates only weakens the bound if the
horizontal signs differ. The right side decreases separately in x,z
on `[0,r_0)`. Substitute the bounds (5), and use the exact comparisons

```text
r_0^2-x_0^2-(49/50)^2 = 93/8000 >0,
r_0^2-z_0^2-(37/100)^2 = 1177/392000 >0.
```

Then (6) gives

```text
|c_A-c_B|^2
 > 2r_0^2-2x_0z_0+2(49/50)(37/100)
 = 2+1717/196000 >2.
```

Touching unit squares have center distance at most `sqrt(2)`. This
contradicts the edge A--B and excludes the side-diagonal case.

Together with the earlier side-side result, this leaves only two diagonal
transmitters when C has two circle vertices. No claim is made here that
this last pattern exists or that it has been excluded.
