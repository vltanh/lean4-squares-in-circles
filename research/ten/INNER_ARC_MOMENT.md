# Arc cost of a square with center in the unit disk

Put

```text
r = sqrt(1+1/sqrt(2)).
```

For an arbitrarily oriented unit square whose center has squared norm
`t<=1`, let `L` be the total angular length of its intersection with the
circle `C_r`. The intersection can have two components. Then

```text
L >= (pi/2) max(t-1/2,0).                            (1)
```

The inequality is strict when `1/2<t<1`. For `t=1`, equality occurs exactly
for a radial square, or a square whose two edge directions make angles
`pi/4` with the radial direction. In the notation of
[CENTER_RADIUS_REDUCTION.md](CENTER_RADIUS_REDUCTION.md), these are types
S with radial center `1`, and D.

This gives a conditional way to exclude five centers in the open unit disk:
it suffices to prove that five disjoint unit squares with centers of norm
at most `1` satisfy `sum(t_i)>=4`. That moment inequality is **not proved in
this note**.

## 1. Coordinates and the small-arc cases

Choose the square's edge directions as axes, and reflect or interchange them
so that its center is `(u,v)` with `u>=v>=0`. Thus `t=u^2+v^2`. Such a square
automatically has farthest squared radius at most `3/2+sqrt(2)<9/2`, so the
containing-disk hypothesis of the cited arc theorem is satisfied. The assertion
is immediate for `t<=1/2`, and the case `t=1` follows from the complete arc
bound and equality classification in
[CENTER_RADIUS_REDUCTION.md](CENTER_RADIUS_REDUCTION.md). We henceforth
assume

```text
1/2 < t < 1.
```

If `L>=pi/4`, (1) is strict. We may therefore also assume `L<pi/4`.

Write

```text
A = u-1/2,    B = v-1/2,
U = u+1/2,    V = v+1/2.
```

Here `A>0`. Both left corners of the square lie strictly inside `C_r`, since

```text
A^2+V^2 = t+1/2-u+v <= 3/2 < r^2.
```

Its upper-right corner lies outside `C_r`, since

```text
U^2+V^2 = t+1/2+u+v >= t+1/2+sqrt(t) > r^2.
```

Also `V<=1/2+1/sqrt(2)<r`. If `U>=r`, the full horizontal strip between
`y=B` and `y=V` cuts out one circle arc, of angle at least `pi/4` because
the endpoint chord has length at least `1=2r sin(pi/8)`. This contradicts
the small-arc assumption. Therefore `U<r`, and we can put

```text
p = acos(U/r),
q = asin(V/r),
s = asin((1/2-v)/r).
```

We have `p>0` and `q>p`. If `s<-p`, the arc again spans the full horizontal
strip and has angle at least `pi/4`. Thus `s>=-p`. The total arc length is
exactly

```text
L = q-p + max(s-p,0).                               (2)
```

There is one arc when `s<=p` and two arcs when `s>p`.

## 2. Reduction of the one-arc case to two scalar functions

Fix an arc angle `ell=L` with `0<ell<pi/4`, and put `d=ell/2`.
In the one-arc case, `q=p+ell`. Write

```text
m = (p+q)/2,
z = cos(m-pi/4).
```

The inequality `u>=v` gives `m<=pi/4`. The lower-right corner is inside or
on `C_r`; equivalently `|s|<=p`. In particular

```text
r(sin(p)+sin(q)) >= 1,
sin(m) >= 1/(2r cos(d)).
```

Define

```text
m_0(d) = asin(1/(2r cos(d))).
```

Then `m_0(d)<=m<=pi/4`, and a direct expansion gives

```text
t = r^2(1-sin(ell)+2z^2 sin(ell))
      -2r cos(pi/4-d) z + 1/2.                      (3)
```

For fixed `ell`, this is convex as a function of `z`. Consequently its
maximum over the displayed interval occurs at `m=m_0(d)` or `m=pi/4`.

The second endpoint is the diagonal-center branch

```text
T_D(ell) = 2(r cos(pi/4-ell/2)-1/2)^2.              (4)
```

At the first endpoint the lower-right corner lies on `C_r`. Put

```text
k = tan(ell/2),
X = sqrt(r^2/(1+k^2)-1/4).
```

The center is `(X+(k-1)/2, Xk)`, and its squared norm is

```text
T_B(ell) = r^2-k/2-(1-k)X.                          (5)
```

We have proved

```text
t <= max(T_D(ell),T_B(ell))                         (6)
```

in the one-arc case.

## 3. The two-arc case reduces to the same boundary branch

Now suppose `s>p`. For fixed total angle `ell=L`, put

```text
m = (q+s)/2,
d = (q-s)/2.
```

Since `r(sin(q)+sin(s))=1` and `ell=q+s-2p`, we have

```text
sin(m) = 1/(2r cos(d)),
p = m-ell/2,
0 <= d < ell/2.
```

In particular

```text
pi/8 <= m < m_0(ell/2),
sin(m) <= tan(pi/8) = sqrt(2)-1 < 1/2.
```

The center coordinates give

```text
t = (r cos(p)-1/2)^2 + r^2 cos(m)^2 - (1/4)cot(m)^2.
```

Differentiate with respect to `m`, keeping `ell` fixed and using
`p=m-ell/2`:

```text
dt/dm = -2r^2 cos(p)sin(p) + r sin(p)
          + (2cos(m)/sin(m)^3)(1/4-r^2 sin(m)^4).
```

The final term is strictly larger than `sqrt(3)`: use `sin(m)<1/2`,
`cos(m)>sqrt(3)/2`, and `r^2<2`. The first term is at least `-r^2`, and
the second is nonnegative. Since `r^2<sqrt(3)`, this proves `dt/dm>0`.

Thus increasing `d` to `ell/2`, so that the lower arc shrinks to a single
point, increases `t`. The resulting center is exactly the boundary branch
in (5). Therefore

```text
t <= T_B(ell)                                      (7)
```

also in the two-arc case.

## 4. Bounds for the two scalar branches

We prove, for `0<ell<pi/4`,

```text
T_D(ell) < 1/2+2ell/pi,
T_B(ell) < 1/2+2ell/pi.                             (8)
```

For (4), put `theta=pi/4-ell/2`. Then

```text
T_D'(ell) = r^2 sin(2theta)-r sin(theta).
```

As a function of `theta` in `[pi/8,pi/4]`, the right side is concave:
its second derivative is `sin(theta)(r-8r^2 cos(theta))<0`. At the two
endpoints its values are `1/sqrt(2)` and `r^2-r/sqrt(2)`, respectively;
the latter is at least `1/sqrt(2)` because `r<=sqrt(2)`. Hence

```text
T_D'(ell) >= 1/sqrt(2) > 2/pi.
```

Since `T_D(pi/4)=1`, integration backwards from `pi/4` proves the first
strict inequality in (8).

For (5), differentiation and `dk/dell=(1+k^2)/2` give

```text
T_B'(ell) = (1+k)X/2 -(1+k^2)/4 + k(1-k)/(8X).
```

Here `0<=k<=K=sqrt(2)-1`, and `X>1`. The function `(1+k)X` is increasing:
its derivative has the sign of

```text
r^2(1-k) - (1/4)(1+k^2)^2 > 0,
```

because `r^2(1-k)>=r^2(1-K)=1` and `(1+k^2)^2<4`. At `k=K` its value is
`sqrt(1+sqrt(2))<5/3`. Using also `k(1-k)<=1/4`, we obtain

```text
T_B'(ell) < 5/6-1/4+1/32 = 59/96 < 5/8 < 2/pi.
```

The last comparison follows, for example, from `pi<22/7<16/5`.
Since `T_B(0)=1/2`, integration from `0` proves the second strict inequality
in (8).

Equations (6)--(8) imply `t<1/2+2L/pi`, proving strictness in (1) whenever
`1/2<t<1`. The endpoint cases were already treated in Section 1.

## 5. Conditional consequence for five inner centers

Suppose five pairwise interior-disjoint unit squares have centers of squared
norms `t_i<1`, and suppose additionally that `sum(t_i)>=4`. Summing (1),
using `max(t_i-1/2,0)>=t_i-1/2`, gives total arc length at least `3pi/4`.
At least one `t_i` exceeds `1/2`, so the strict part of (1) makes the total
**strictly greater** than `3pi/4`.

If these were exactly the five squares with centers in the open unit disk
in a ten-square packing of squared radius at most `9/2`, the other five
centers of norm at least `1` would occupy total
arc length at least `5pi/4` by
[CENTER_RADIUS_REDUCTION.md](CENTER_RADIUS_REDUCTION.md). Disjoint square
interiors give disjoint circle arcs up to finitely many endpoints. The two
arc budgets would exceed `2pi`, a contradiction.

Thus the five-inner-center branch would be closed by the stated five-center
moment inequality. No conclusion about that missing inequality is assumed
here.
