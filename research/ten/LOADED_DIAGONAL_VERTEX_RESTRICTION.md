# A loaded body contacted at its two opposite noncircle corners

**Status:** hand proof; two independent full mathematical reviews passed
on 2026-10-29, including the force equations, physical neighbor bounds,
and exact corner comparison. This is a local
restriction for an additional loaded-ring support type. It does not
classify all contact ownership patterns.

Use the entirely loaded positive seven-ring and the working radius window.
Suppose one body has a unique circle vertex and is contacted, in ring order,
at the other two corners adjacent to that circle vertex. In its own frame,
write

```
C=[X-1,X] x [-Y,1-Y],
w=(X,-Y),       X,Y>1/2,       X^2+Y^2=q=R^2,
L=w-(1,0)=(X-1,-Y),
U=w+(0,1)=(X,1-Y).
```

Thus `L,U` are opposite corners of the square, and the remaining corner
is `A=(X-1,1-Y)`. Both neighboring squares are contained in `D_R`.
The argument permits a contact normal on the boundary of a corner normal
cone; such a normal exposes a side support face rather than a unique
support vertex.

**Theorem.** Both farthest-vertex coordinates satisfy `X,Y>=1`. If either
contact normal exposes a unique vertex of this body, both do and
`X,Y>1`. In all cases,

```
|A|^2<=9/2-sqrt(14)<49/64.                             (1)
```

## 1. Force and torque balance leave one nonnegative parameter

The inward incoming force at `L` is `(a,b)`, with `a,b>=0`.
The outgoing force is `(c,d)`, with `c,d>=0`, since its negative is an
inward supporting normal of `C` at `U`. Let the positive outward circle
load be `lambda*w`, where `lambda>0`. Force balance gives

```
a-c=lambda*X,       d-b=lambda*Y.
```

Equality of the two origin torques is

```
(X-1)b+Y*a = X*d+(Y-1)c.
```

Substituting force balance cancels the circle-load terms and gives `b=c`.
Put `r=b/lambda>=0`. The two original force vectors are therefore

```
f_in =lambda*(r+X,r),
f_out=lambda*(r,r+Y).                                 (2)
```

In particular, a strictly interior corner normal at either contact is
possible exactly when `r>0`, and then both are strictly interior. If
`r=0`, both supports expose the adjacent inner sides, with application
points at their endpoints.

For `r>0`, the force turn is acute: the cross product in (2) is
`lambda^2[r(X+Y)+XY]>0`, and their scalar product is
`lambda^2*r(2r+X+Y)>0`. For `r=0`, the force turn is exactly `pi/2`.

## 2. The physical neighbors force X,Y>=1

A supported unit square contains the point obtained by moving one unit
from any support point along its inward unit normal. This includes both
vertex and side supports; see
[SEVEN_RING_FORCE_RATIO.md](SEVEN_RING_FORCE_RATIO.md), Section 4.

At `L`, the incoming neighbor has inward unit normal

```
-(r+X,r)/N_1,       N_1=sqrt((r+X)^2+r^2)>0.
```

It therefore contains

```
w-(1,0)-(r+X,r)/N_1.
```

Its squared norm is at most `q=|w|^2`. Expansion and multiplication by
`N_1/2` give

```
(X-1)(N_1+r+X)>=Y*r.                                 (3)
```

At `U`, the outgoing neighbor has inward unit normal

```
(r,r+Y)/N_2,       N_2=sqrt(r^2+(r+Y)^2)>0.
```

The corresponding contained point is

```
w+(0,1)+(r,r+Y)/N_2.
```

The same norm comparison gives

```
(Y-1)(N_2+r+Y)>=X*r.                                 (4)
```

Every factor multiplying `X-1` or `Y-1` is strictly positive. Equations
(3)--(4) prove `X,Y>=1`; if `r>0`, their right sides are strictly positive
and hence `X,Y>1`.

This deduction uses physical neighbor containment. It is not an assertion
about the force-balance equations in isolation.

## 3. The opposite corner is strictly inside a smaller disk

For `X,Y>=1` on `X^2+Y^2=q`, one has
`X+Y>=1+sqrt(q-1)`. Therefore

```
|A|^2=(X-1)^2+(Y-1)^2
     =q+2-2(X+Y)
     <=q-2sqrt(q-1)
     <=9/2-sqrt(14).
```

The last function increases for `q>2`, covering the working window.
Finally,

```
14*64^2-239^2=223>0
```

proves `9/2-sqrt(14)<49/64`, establishing (1).

The corresponding bound for a body with two adjacent inner side supports
is `|A|^2<53/64`, proved in
[LOADED_DOUBLE_SIDE_RESTRICTION.md](LOADED_DOUBLE_SIDE_RESTRICTION.md).
Thus a pair consisting of one corner of each of these two types has
squared-norm sum below

```
53/64+49/64=51/32<425/256.
```

Whenever the local spike admits the diameter-disk reduction, this sum is
a sufficient centered-disk capacity bound by
[SEVEN_RING_CORNER_MOMENT_CAPACITY.md](SEVEN_RING_CORNER_MOMENT_CAPACITY.md),
Section 1. No assertion that every contact has such a spike or these
endpoint types is made here.

## 4. Optional exact concurrence formula

Equations (2) also recover the radial concurrence without choosing a new
contact point. The common origin torque is

```
tau=lambda*[r(X+Y-1)+XY].
```

The two force lines meet at `eta*w`, where

```
eta=[r(X+Y-1)+XY]/[r(X+Y)+XY]
    =1-r/[r(X+Y)+XY].
```

This point lies on the positive circle-load ray, and `eta<=1`, with
strict inequality exactly when `r>0`. These formulas retain the original
application points `L,U`. They do not prove that every loaded body has
this geometric contact pattern, and no Lean verification is claimed.
