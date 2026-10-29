# A corner-moment capacity bound for a loaded side/vertex ring

Independent mathematical review passed on 2026-10-29; this is not Lean verification.

**Status:** hand proof of a conditional nonuniform-ring exclusion. This
uses the one-chirality contact pattern; it does not classify other contact
patterns or exclude every ring in this pattern.

Use the physical loaded seven-ring, its three inner unit squares, and the
one-chirality notation of
[SEVEN_RING_SPIKE_REDUCTION.md](SEVEN_RING_SPIKE_REDUCTION.md). Let

```
w_i=R(cos(alpha_i)u_i-sin(alpha_i)v_i),
A_i=w_i-u_i+v_i,
X_i=R cos(alpha_i),       Y_i=R sin(alpha_i).
```

The symbol `A_i` here means the square's corner opposite its circle
vertex, not its concurrence point. Define

```
M=max_i (|A_i|^2+|A_(i+1)|^2).
```

**Theorem.** Every unit square in the central hole is contained in the
disk of radius `sqrt(M)` about the original origin. Consequently, if
`M<425/256`, the ring cannot enclose three interior-disjoint unit squares.
In particular, a physical one-chirality seven-ring with

```
Y_i>=15/16 for every i                               (1)
```

cannot be a component of a subcritical ten-square packing.

The first assertion concerns unit squares that fit in the hole, rather
than all points of the hole. The hole may have thin protruding triangles.

## 1. A disk with diameter AB lies in a controlled centered disk

For arbitrary points `A,B`, the disk with diameter `[A,B]` has center
`(A+B)/2` and radius `|A-B|/2`. Every point `z` in that disk satisfies

```
|z| <= (|A+B|+|A-B|)/2,
|z|^2 <= (|A+B|^2+|A-B|^2)/2
       = |A|^2+|B|^2.                               (2)
```

The inequality is the elementary bound `(r+s)^2<=2(r^2+s^2)`; the
identity is the parallelogram identity.

## 2. Every vertex of an inner unit square is controlled

The polygon-chain argument in Section 2 of the spike note proves the
following slightly more precise form of its displayed disk reduction:

```
Omega \ conv{A_i} is contained in union_i conv{A_i,p_i,A_(i+1)}.
```

Indeed the winding number of the polygon through the `A_i` vanishes at
every point outside their convex hull, so its stated proof applies there
directly. This does not require the polygon through the `A_i` to be simple.

Let `K` be a unit square contained in the central hole and let `z` be any
of its vertices. If `z` lies in `conv{A_i}`, convexity of the norm gives

```
|z|^2 <= max_i |A_i|^2 <= M.
```

Otherwise `z` belongs to a contact triangle
`conv{A_i,p_i,A_(i+1)}`. The two loaded bodies defining that triangle are
interior-disjoint from `K`. Section 5 of the spike note therefore puts
`z` in the disk with diameter `[A_i,A_(i+1)]`. Applying (2) yields
`|z|^2<=M` again. All four vertices of `K` belong to this centered disk,
and its convexity gives the same containment for the whole square.

## 3. The three-square optimum converts containment to exclusion

The hand three-square theorem gives optimal radius

```
R_3=5sqrt(17)/16,       R_3^2=425/256.
```

Its source is the repository's
[three-square proof](https://github.com/vltanh/lean4-squares-in-circles/blob/4bea747b3efa13c869b956cb28435efaf21526fa/docs/proof/06-three.md),
also used in [REGULAR_SEVEN_LOADED_RING.md](REGULAR_SEVEN_LOADED_RING.md).
Three interior-disjoint unit squares therefore cannot all belong to a
disk of squared radius strictly below `425/256`. Section 2 proves the
claimed exclusion when `M<425/256`.

## 4. A uniform own-coordinate condition suffices

The incoming-neighbor inequality in
[SEVEN_RING_FORCE_RATIO.md](SEVEN_RING_FORCE_RATIO.md), Section 4, proves
`X_i>1` for every physical one-chirality ring body. Assume (1), and put
`m=15/16`. Then both `X_i,Y_i>=m`, and

```
X_i^2+Y_i^2=q=R^2,
|A_i|^2=(X_i-1)^2+(Y_i-1)^2=q+2-2(X_i+Y_i).
```

For nonnegative `X,Y>=m` with `X^2+Y^2=q`, one has

```
X+Y>=m+sqrt(q-m^2).                                 (3)
```

To see this, put `u=X^2` in `[m^2,q-m^2]`. The concave quadratic
`u(q-u)` is at least its endpoint minimum `m^2(q-m^2)`. Thus
`XY>=m sqrt(q-m^2)`; squaring the nonnegative sides proves (3).
Consequently

```
|A_i|^2 <= q+2-2m-2sqrt(q-m^2).
```

The right side increases throughout the working radius window: its
derivative is `1-1/sqrt(q-m^2)>0`, because
`q>=6241/1600` and `m^2=225/256` give `q-m^2>1`.
At `q<=9/2` this yields

```
|A_i|^2 <= (37-sqrt(927))/8,
M <= (37-sqrt(927))/4 < 33/20 < 425/256.              (4)
```

The first strict comparison in (4) is equivalent to
`sqrt(927)>152/5`, proved by `25*927-152^2=71>0`.
The second follows from `425/256-33/20=13/1280>0`.
Section 3 therefore excludes the three-square completion under (1).

## 5. Remaining scope

This theorem provides a geometric sufficient condition for exclusion;
it does not prove that every physical ring satisfies that condition.
A remaining one-chirality seven-ring must have an adjacent pair of
opposite corners with squared-norm sum at least `425/256`, and it must
have at least one body with `R sin(alpha_i)<15/16`. These conditions
retain arbitrary variation in the frames and contact magnitudes.
Other contact ownership patterns remain outside this manuscript.
No Lean verification is claimed.
