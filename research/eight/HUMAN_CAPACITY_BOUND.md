# Two-square capacity beyond a central side facing away from the origin

**Status.** This note proves an analytical disk-cap theorem. No numerical
minimum, interval cover, or marker certificate is a premise. The continuous
orientation variable is reduced by strict concavity to the two cardinal
endpoints and one actual change of the farthest vertex.

## 1. The disk-cap theorem

**Theorem.** At most two pairwise interior-disjoint unit squares can be
contained in

```text
{(x,y): x^2+y^2 <= 4, x >= 1/2}.                         (1)
```

The threshold radius here is exactly `2`, including its boundary. The theorem
does not assume that the squares have a common orientation or touch the
straight side of the cap.

The key geometric fact is the following restriction on the center of a
single square.

**Center-height lemma.** If a unit square is contained in (1), and its center
is `(x_c,y_c)`, then

```text
|y_c| < sqrt(3)/2.                                      (2)
```

We first prove the lemma over the entire continuous orientation range.

## 2. Normalize a hypothetical high-center square

Suppose, for contradiction, that `y_c >= y_0`, where

```text
y_0 = sqrt(3)/2.
```

Reflection in the horizontal axis covers the other sign. Choose a side-frame
angle in `[-pi/4,pi/4]` using the quarter-turn symmetry of the square, and put

```text
theta = absolute value of that angle,
c = cos(theta),  s = sin(theta),
L = c+s,         D = c-s,       0 <= theta <= pi/4.
```

The half-width on each coordinate axis is `L/2`. The cap condition therefore
implies `x_c >= 1/2+L/2`. Move this one square left and down until its center
is

```text
(x_0,y_0),       x_0 = (1+L)/2.                         (3)
```

Every vertex remains in the first quadrant during this move: the leftmost
coordinate is at least `1/2`, and the lowest is at least
`y_0-L/2 >= (sqrt(3)-sqrt(2))/2 > 0`. Hence moving left and down decreases
each squared vertex distance from the origin. The new square remains in the
cap. This is a reduction for a single square; no simultaneous motion of a
packing is asserted.

We may also take the frame angle to be `+theta`. Here is the exact comparison
if its original sign was negative. Since `x_0 >= 1 > y_0`, the farthest-vertex
formula at the fixed center `(x_0,y_0)` gives, beyond the common term
`x_0^2+y_0^2+1/2`, the quantities

```text
positive angle:  x_0 c+y_0 s+|y_0 c-x_0 s|,
negative angle:  x_0 L+y_0 D.
```

If `y_0 c >= x_0 s`, the second minus the first is
`2s(x_0-y_0)>=0`. If `y_0 c <= x_0 s`, it is `2y_0 D>=0`. Thus choosing the
positive angle can only decrease the maximum squared vertex distance, and
does not change the half-width or the cap condition.

It suffices to show that the square with center (3) and frame angle
`theta in [0,pi/4]` always has a vertex of squared distance greater than `4`.

## 3. Only two candidate farthest vertices

The right and top vertices of the normalized square are

```text
V_R = (1/2+L, y_0-D/2),
V_T = (1/2+c, y_0+L/2).
```

The other two vertices are

```text
V_L = (1/2,   y_0+D/2),
V_B = (1/2+s, y_0-L/2).
```

All coordinates are nonnegative. The top vertex is coordinatewise at least
each of `V_L,V_B`, so one of `V_R,V_T` is farthest. Put

```text
F_R(theta) = (1/2+L)^2+(y_0-D/2)^2,
F_T(theta) = (1/2+c)^2+(y_0+L/2)^2.                     (4)
```

Each function is strictly concave on the whole interval `[0,pi/4]`.
Indeed, direct differentiation yields

```text
F_T'' = -2 cos(2 theta)-2cs-c-y_0 L < 0,
F_R'' = -6cs-L+y_0 D < 0.                              (5)
```

For the second inequality, use `L>=1`, `0<=D<=1`, and `y_0<1`. Every sign in
the first inequality is immediate on the interval, with `c>0`.

The difference of the two functions is

```text
F_R-F_T = 2(s x_0-c y_0).
```

Let `g(theta)=s x_0-c y_0`. Its derivative is

```text
g' = c/2 + cos(2 theta)/2 + cs + y_0 s > 0.            (6)
```

At angle zero it is negative, while at `pi/4` it is positive because
`x_0=1/2+1/sqrt(2)>y_0`. There is consequently exactly one angle `theta_0`
at which the farthest-vertex identity changes.

On `[0,theta_0]` the squared farthest-vertex distance is `F_T`; on
`[theta_0,pi/4]` it is `F_R`. By concavity, its minimum is attained among just

```text
F_T(0),   F_T(theta_0)=F_R(theta_0),   F_R(pi/4).         (7)
```

This reduction uses the two orientation endpoints and the unique actual
vertex transition; there is no artificial partition of the angle domain.

## 4. The three forced possibilities all exceed 4

At the endpoints,

```text
F_T(0)    = 13/4+sqrt(3)/2 > 4,
F_R(pi/4) = 3+sqrt(2)      > 4.                         (8)
```

For the first inequality, `sqrt(3)/2>3/4`; for the second, `sqrt(2)>1`.

It remains to treat the transition `theta_0`. Its defining equation
`s x_0=c y_0` says that the square center lies on the frame's first axis.
Write

```text
x_0=a c,   y_0=a s,   a>0.
```

At this angle the squared farthest-vertex distance is therefore

```text
(a+1/2)^2+1/4.                                         (9)
```

Suppose (9) were at most `4`. It would follow that

```text
a < 13/9,
```

since substituting `a=13/9` into (9) gives `653/162>4`. On the other hand,
the central-coordinate identity in (3) gives

```text
(2a-1)c = 1+s.
```

Both sides are positive. Squaring and using `c^2=1-s^2`, then dividing by
`1+s`, gives the exact relation

```text
s = ((2a-1)^2-1)/((2a-1)^2+1).                         (10)
```

Here `a>=1`, because `(2a-1)c=1+s>=1` and `c<=1`. The expression in (10)
is increasing for `a>=1`. Thus `a<13/9` implies

```text
s < 104/185,
y_0=a s < (13/9)(104/185) = 1352/1665 < 5/6.
```

This contradicts `y_0=sqrt(3)/2>5/6`. Hence (9) exceeds `4`. Together with
(7) and (8), this proves that every normalized square has a vertex outside
the radius-2 disk, completing the contradiction and the center-height lemma.

## 5. Deduce the two-square capacity

Let `p_i=(x_i,y_i)` be the centers of three hypothetical pairwise
interior-disjoint unit squares in the cap (1). Each square contains its
closed inscribed disk of radius `1/2`. The left cap condition and the right
disk bound imply

```text
1 <= x_i <= 3/2.                                       (11)
```

The lower bound also follows from the horizontal half-width being at least
`1/2`. For the upper bound, the point `p_i+(1/2,0)` lies in the square, so
`x_i+1/2<=2`.

Centers of two interior-disjoint unit squares are at least `1` apart, because
their open inscribed disks of radius `1/2` are disjoint. From (11),

```text
|y_i-y_j|^2 >= 1-|x_i-x_j|^2 >= 3/4.
```

Order the three centers by height. Both successive height gaps are at least
`sqrt(3)/2`, so the total span is at least `sqrt(3)`. But the center-height
lemma places all three in the open interval
`(-sqrt(3)/2,sqrt(3)/2)`, whose total length is `sqrt(3)`. This contradiction
proves the theorem.

## 6. Application to the central square in an eight-square packing

Let a unit square `C`, with center `c_0`, be part of a packing in a disk of
radius at most `2` about the origin. Let `n` be one of its four outward unit
side normals. Suppose

```text
n dot c_0 >= 0.
```

If another square is separated from `C` on the outward `n` axis, every one
of its points satisfies

```text
n dot x >= n dot c_0+1/2 >= 1/2.
```

Rotating the coordinate system and applying the disk-cap theorem shows:

**Central-side corollary.** At most two other squares can be separated from
`C` beyond any central side whose outward normal has nonnegative projection
on `c_0`.

No central-square existence theorem is needed for this statement; it applies
to any chosen square. When a square containing the origin has been
identified, reflect its two axes so that the two coordinates of its center
are nonnegative. Its right and top sides then each have capacity at most two.
If a center coordinate is zero, both sides on that axis satisfy the same
bound; if the central center is the disk center, all four sides do.

This combines with `HUMAN_STRUCTURAL_LEMMAS.md`: at least three of the seven
other squares admit central-axis separators; all exceptions have distinct
corner assignments; and the two outward central sides cannot each serve
more than two squares. These constraints concern separators that actually
exist, and do not assert a common orientation or a prescribed contact graph.

The other two central sides need separate analysis. Their supporting lines
can lie closer to the disk center than `1/2`; the theorem above does not
apply to those larger caps.

An exact four-square example shows why that qualification is necessary.
Take an axis-parallel central square with center `(2/5,0)`, and three
axis-parallel squares with centers

```text
(-3/5,-1),   (-3/5,0),   (-3/5,1).
```

The central square's left side is `x=-1/10`, and all three other squares
are separated beyond it. Their mutual vertical center gaps are at least
one. Every square lies in the disk with squared radius

```text
(11/10)^2+(3/2)^2 = 173/50 < 4.
```

The central square even contains the closed radius-`1/12` disk in its open
interior, since its nearest side is at distance `1/10>1/12` from the origin.
Thus a general two-square capacity for *every* central side would already
fail in this exact example. It does not constitute an eight-square packing;
an eight-square theorem eliminating such larger-cap triples would need to
use the other four squares as well.

The five-corner projected chain is still not forced, and no unrestricted
sharp eight-square lower bound is claimed.
