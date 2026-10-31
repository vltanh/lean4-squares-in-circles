# A diagonal vertex transmission forces a rotated opposite endpoint

Consider the remaining unique-circle-vertex normal form for the mixed
five-cycle `A-U-C-V-B-A` from
[SIDE_NORMAL_MIXED_FIVE_CYCLE.md](SIDE_NORMAL_MIXED_FIVE_CYCLE.md).
Use C's own coordinate frame with the disk center at the origin:

```text
c_C=(a,b),                 b>a>0,
R^2=(a+1/2)^2+(b+1/2)^2,
79/40 <= R <= 3/sqrt(2).
```

The contacts on C are its bottom-left corner
`P=(a-1/2,b-1/2)` and the interior point
`Q=(a-1/2+d,b-1/2)` on its bottom side, with `0<d<1`.
The outgoing transmission directions are `(-p,-q)` and `(0,-1)`, with
`p>q>0` and `p^2+q^2=1`.

**Claim.** If U is a diagonal transmitter, then B cannot be parallel to
C. In particular B's contact with V cannot be in the relative interior
of a side of B.

This is a further conditional reduction, not an exclusion of the whole
mixed five-cycle. By
[DIAGONAL_MIXED_FIVE_CYCLE.md](DIAGONAL_MIXED_FIVE_CYCLE.md), U diagonal
already forces V to be a side transmitter. Thus V has width one in the
vertical transmission direction. We use that conclusion below.

## 1. The separation and stress inequalities

Put

```text
rho=q/p,       k=sqrt(2)p-q=(sqrt(2)-rho)/sqrt(1+rho^2).
```

The endpoint A's rightward extent from its support point is at most q,
while B's leftward extent from its vertically supported point is at most
one. The same bounds as in Section 2 of the diagonal-transmitter note
therefore give

```text
d <= 1-k.                                               (1)
```

In particular `k<1`. Since `p>1/sqrt(2)` and `q<1/sqrt(2)`, also

```text
k > 1-1/sqrt(2) > 29/100.                              (2)
```

Write the outgoing force at P as `(-u,-v)`, the one at Q as `(0,-z)`,
and C's circle force as `-lambda(a+1/2,b+1/2)`. The established force
and torque equations imply

```text
u=lambda(a+1/2),
u-v=z(1-d),
zd=lambda(b-a).
```

As `v/u=rho`, division yields

```text
(b-a)/(a+1/2) = d(1-rho)/(1-d)
             <= (1-k)(1-rho)/k.                         (3)
```

The expression on the right is strictly less than `1/3`. Here is an
elementary proof retaining all radicals. Put `x=1-rho`, so `0<x<1`,
and `h=sqrt(2)-1`. The identity

```text
[1+h rho]^2-(1+rho^2)=2h rho(1-rho)>0
```

shows that

```text
k > (h+x)/(sqrt(2)-hx).
```

All denominators are positive, and

```text
(h+x)(1+3x)-3x(sqrt(2)-hx)
 = h-2x+3sqrt(2)x^2
 >= h-1/(3sqrt(2))
 = 5sqrt(2)/6-1 > 0.
```

Consequently `k>3x/(1+3x)`, equivalently
`(1-k)(1-rho)/k<1/3`. Equation (3) now gives

```text
b < (4/3)a+1/6.                                        (4)
```

It follows that `a>13/20`. Otherwise `b<31/30`, and hence

```text
R^2 < (23/20)^2+(23/15)^2 = 529/144 < (79/40)^2,
```

contrary to the radius window.

## 2. An axis-parallel B is strictly circle-clear

Suppose B is parallel to C. Its top supporting point reached through V
is

```text
Q_B=(a-1/2+d,b-3/2).
```

Thus its center is `(X,b-2)` for some X. Because Q_B lies on its top
unit side, and because B touches A, the horizontal support bounds give

```text
a+d-1 <= X <= a-k.
```

Using `d>0`, (2), and `a>13/20`, these inequalities imply

```text
|X| < a-29/100.                                        (5)
```

Indeed the lower bound is greater than `a-1`, which exceeds
`-(a-29/100)` because `2a>13/10>129/100`; the upper bound follows from
`k>29/100`.

Also `b<R-1/2<2`, so B's maximum squared vertex norm satisfies

```text
F_B=(|X|+1/2)^2+(5/2-b)^2
   < (a+21/100)^2+(5/2-b)^2.
```

Subtracting this upper bound from the squared norm of C's loaded vertex
gives

```text
R^2-[(a+21/100)^2+(5/2-b)^2]
 = (29/50)a+2059/10000+6b-6.                           (6)
```

If `b>=1`, this is positive immediately. If `b<1`, the radius lower
bound and `a<b` imply the convenient rational estimates

```text
a>39/50,               b>179/200.
```

For the first, `a<=39/50` and `b<1` would give
`R^2<(32/25)^2+(3/2)^2=9721/2500<(79/40)^2`.
For the second, `a<b<=179/200` would give
`R^2<2(279/200)^2=77841/20000<(79/40)^2`.
Substitution in (6) gives the strict lower bound

```text
(29/50)(39/50)+2059/10000-63/100
 = 283/10000 > 0.
```

Therefore `F_B<R^2` in every case. This contradicts B's positive
circle load and proves the claim.

Finally, a side-interior contact on B has a unique inward side normal.
Here that normal is vertical, which would make B parallel to C. Such a
contact is therefore excluded as well. Any surviving D-S pattern must
have V's contact on a vertex of a rotated B.
