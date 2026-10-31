# The nearer endpoint of the four-loaded diagonal cycle is a strict vertex

**Status:** Sections 1--4 passed root and independent mathematical reviews
on 2026-10-29; Section 5 has root mathematical review. The side-support
exclusion in Sections 1--4 is the geometric input to
[the C19 exclusion](DIAGONAL_FIVE_CYCLE_EXCLUSION.md). The extra concurrence
statement is not needed for that closure.

Use `U-A1-A2-A3-A4-U` from
[MIXED_FIVE_FOUR_LOADED_GEOMETRY.md](MIXED_FIVE_FOUR_LOADED_GEOMETRY.md),
with the explicitly imported radius window

```text
5/2+sqrt(2) < R^2 <= 9/2,        R>=79/40.
```

Orient the transmission normal horizontally and its positive cycle direction
to the right. Write `k=1/sqrt(2)` and the center of U as `(m,-b)`, where
`b>0`. Its two transmission contacts are `(m+k,-b)` and `(m-k,-b)`.
Choose the endpoint nearer zero; reflection in the vertical axis, together
with reversal of the cycle order, lets us call it A1 and write

```text
q0=(r,-b),       r=k-a,       a=|m|>=0.
```

The existing geometric and inner-trace lemmas give

```text
a,b<1/sqrt(6),
a^2+b^2+sqrt(2/3)b<1/2,
|c_U|^2<279/800.                                      (1)
```

**Theorem.** The support feature of A1 at q0 is a strict vertex, and its
opposite vertex is its unique circle vertex. In addition, its positive
radial force-concurrence point belongs to its closed square. Thus three
consecutive loaded bodies A1,A2,A3 have closed-square concurrence. Only
the farther endpoint A4 may still require a separate concurrence argument.

The choice of the nearer endpoint is allowed to tie. In that event the
same conclusions hold at both endpoints.

## 1. Proximity and the scalar range

The nearer endpoint satisfies

```text
|q0|^2=|c_U|^2+1/2-sqrt(2)a<679/800
       <1521/1600=(39/40)^2<=(R-1)^2.                  (2)
```

Every point within distance one of q0 is therefore strictly inside the
containing circle. In particular, if q0 is a vertex of A1, both adjacent
vertices are circle-clear; its opposite vertex must be the sole circle
vertex.

Also

```text
1/4<r<=k,       0<b<5/12.                             (3)
```

For the lower bound use `k>7/10` and `1/sqrt(6)<5/12`, giving
`r>17/60>1/4`. The upper bound follows from `a>=0`.

## 2. What side support would imply

Suppose the supporting feature on A1 were an edge. Since its inward normal
is horizontal, A1 would have the form

```text
A1=[r,r+1] x [-b-u,1-b-u],       0<=u<=1.
```

This includes support-edge application at either endpoint. Put

```text
X=r+1,       Y=b+u,
F=(X,-Y),       W=(X,1-Y),       E=(r,1-Y).
```

The two vertices on the support side are circle-clear by (2). Any circle
vertex on the opposite side must have absolute height strictly greater
than one, since

```text
R^2-X^2 > (5/2+sqrt(2))-(1+k)^2=1.
```

But `-b<=W_y<=1-b` and `0<b<5/12`, so `|W_y|<1`.
Consequently F is the unique circle vertex, and

```text
R^2=X^2+Y^2,       1<Y<17/12,       u=Y-b>0.           (4)
```

Let the incoming force at q0 be `(mu,0)`, with `mu>0`, and let the circle
load at F be `-lambda F`, with `lambda>0`. The other inward contact force
on A1 has the form `(alpha,-nu)`, with

```text
mu+alpha=lambda X,       nu=lambda Y>0.                (5)
```

Its negative vertical component puts its application point on A1's top
edge, including either endpoint. Write this point as

```text
P=(r+t,1-Y),       0<=t<=1.
```

Here `alpha>=0` unless `P=W`; the interior top edge has `alpha=0`,
and the top-left corner E has `alpha>=0`. Torque balance about F gives

```text
nu(1-t)=u mu+alpha.                                   (6)
```

## 3. The other contact cannot be the upper-right corner

Suppose `P=W`, so `t=1`. Equations (5)--(6) give

```text
alpha=-u mu,       mu(1-u)=lambda X,
0<u<1.
```

The force into the neighboring square therefore has direction `(1,rho)`,
where

```text
rho=Y(1-u)/(uX)>0.
```

Its supporting line passes through W. Every unit square has projection
width at least one. Containment of this neighbor in the radius-R disk
would consequently require, for `n=(1,rho)/sqrt(1+rho^2)`,

```text
W dot n <= R-1.                                       (7)
```

We now show the reverse strict inequality by elementary bounds.
From (4),

```text
X^2>6241/1600-(17/12)^2>(11/8)^2,
```

where the final difference is `11/3600`. Since `u=Y-b>Y-5/12`,

```text
rho < Y(17/12-Y)/[(Y-5/12)X]
     < (96/77)(17/12-Y) < 40/77 < 4/7.
```

Here `Y/(Y-5/12)<=12/7` for `Y>=1`. Completing the product also gives

```text
(Y-1)rho < (96/77)(Y-1)(17/12-Y)
         <= (96/77)(5/24)^2=25/462<1/16.
```

Thus

```text
W dot n = [X-(Y-1)rho]/sqrt(1+rho^2)
        > (11/8-1/16)/(sqrt(65)/7)
        = 147/(16sqrt(65)) > 9/8 > R-1.
```

The penultimate comparison squares to `21609>21060`; the last follows
from `R<=3/sqrt(2)<17/8`. This contradicts (7). Notice that this argument
only needs containment of the neighbor, not its positive circle load.

## 4. The other top-edge possibilities violate the transmitter bound

We now have `alpha>=0` and `t<1`. Substituting (5) into (6) gives

```text
b-r u = tY+(1-u)alpha/lambda >=0.
```

Since `u=Y-b`, this implies

```text
b >= rY/(r+1) > r sqrt(Q-(r+1)^2)/(r+1),
Q=5/2+sqrt(2).                                        (8)
```

We verify that the right side is already too large for (1). Put
`x=r+1`, so `5/4<x<=1+k`, and define

```text
P(x)=x^2(Q-x^2)-3[x^2-(x-1)Q/sqrt(2)]^2
 = -4x^4+(6+15sqrt(2)/2)x^3
   -(127/8+14sqrt(2))x^2+(99/4+15sqrt(2))x
   -99/8-15sqrt(2)/2.
```

This polynomial is strictly concave throughout the real line. Indeed its
second derivative is a quadratic with negative leading coefficient, and
its maximum is

```text
max P'' = -125/32-89sqrt(2)/8 < 0.
```

At the two endpoints of the displayed x interval,

```text
P(5/4)=(-549+515sqrt(2))/128>0,
P(1+k)=-3/16+sqrt(2)/4>0.
```

The first strict comparison follows already from `sqrt(2)>7/5`.
Concavity therefore gives `P(x)>0` throughout the interval.
Since `x sqrt(Q-x^2)/sqrt(3)>0`, this yields

```text
x sqrt(Q-x^2)/sqrt(3) > x^2-(x-1)Q/sqrt(2).            (9)
```

Let `b0=r sqrt(Q-x^2)/x`. Direct expansion gives

```text
(k-r)^2+b0^2+sqrt(2/3)b0-1/2
 = (sqrt(2)r/x^2)
   [x sqrt(Q-x^2)/sqrt(3)-x^2+rQ/sqrt(2)] >0.
```

By (8), `b>b0`, while the left expression is strictly increasing in b.
This contradicts (1). Hence no side support is possible at q0.
The remaining support feature is a strict vertex, and (2) gives the
asserted unique opposite circle vertex.

## 5. The nearer endpoint also has concurrence inside its square

The [force-quadrilateral theorem](FOUR_LOADED_FORCE_QUADRILATERAL.md)
gives positive radial concurrence on every loaded body and distinct
contact points. For A1 write its circle vertex in its own frame as
`w=(X0,Y0)` with `X0,Y0>1/2`, and its opposite vertex as
`q0=(X0-1,Y0-1)`. Write the concurrence as `Z=eta w`, `eta>0`.

The argument of Section 5 of
[SEVEN_RING_INTERNAL_CONCURRENCE.md](SEVEN_RING_INTERNAL_CONCURRENCE.md)
excludes `eta>1` without needing both neighbors loaded: an inward force
pointing away from such Z would act at the forbidden circle vertex;
both forces pointing toward Z would have to act at q0, contradicting
distinctness of the contacts.

Suppose instead that Z precedes A1 on its positive circle ray. The circle
force points toward Z. A separating-functional argument shows that at
least one contact force must point away from Z. Its application point is
the unique point of A1 nearest Z, by the convex nearest-point identity in
Section 2 of the cited note.

If this force belongs to the loaded neighbor A2, the exact nearest-side
or nearest-corner estimates in Section 4 of that note make A2 strictly
circle-clear, a contradiction. Those local estimates need only that this
particular neighbor is loaded.

If instead this force is the one from U, it acts at the strict opposite
vertex q0. Both components of its inward normal in A1's own frame are
strictly positive. Hence both coordinates of Z are strictly smaller than
those of q0. The other contact force cannot point away from Z too, since
its application point is distinct and the nearest point is unique. It
must point toward Z. Both its coordinates would then be strictly negative.
The only point of A1 whose inward normal cone contains such a vector is
w itself. A contact at w is forbidden because two packed squares cannot
share a point of the containing circle. This is again a contradiction.

Thus Z cannot precede or follow A1 on its positive circle ray, proving
`Z in A1`. The two internal bodies already have this containment by the
force-quadrilateral theorem, proving the stated three-body consequence.

No completion capacity is inferred merely from these three concurrence
containments. In particular, this note does not assume that the mixed
cycle inherits the all-loaded ring's convex enclosure theorem.
