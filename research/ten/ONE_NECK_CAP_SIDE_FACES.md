# Two side-face exclusions for a square in the upper cap

This proves two branches needed for the cap part of
[ONE_NECK_STABBING.md](ONE_NECK_STABBING.md). The square orientations are
arbitrary; this note does not by itself prove the complete stabbing theorem.

Let a unit square be contained in the disk of squared radius `17/4` and in
the half-plane `y>=1/2`. Choose its orthonormal edge directions as

```text
u=(c,s), v=(-s,c),
c>0, |s|<=c, c^2+s^2=1,
```

and let `(A,B)` be its center in these coordinates. Put

```text
a = 27/64,
p = 255/256,
q = 5/4,
P = (a,p),
Q = (-a,q).
```

Then

```text
A < u dot P + 1/2,
A > u dot Q - 1/2.                                  (1)
```

Thus P and Q cannot both miss the square beyond the same one of its two
faces normal to `u`. Both bounds are strict.

## 1. Two signs and heights suffice

We prove the slightly stronger upper bound

```text
A < u dot (a,h)+1/2
```

for either height `h=p` or `h=q`, and either sign of `s`. When `s>=0`, the
bound for the lower height `p` implies that for `q`. When `s<=0`, the bound
for the higher height `q` implies that for `p`. Consequently only these
two cases require proof:

```text
positive tilt with h=p;
negative tilt with h=q.
```

The first inequality in (1) follows directly. For the second, reflect
horizontally. The new frame is `u'=(c,-s), v'=(s,c)`, the own-frame center
is `(-A,B)`, and the reflected Q is `(a,q)`. The upper bound for this
reflected square becomes exactly `A>u dot Q-1/2`.

## 2. A lower bound from two half-planes

Write `s=epsilon sigma`, where `sigma>=0`, `epsilon` is `1` or `-1`, and
`c^2+sigma^2=1`. Define

```text
X=A+1/2, Y=B+1/2,
H=1/2+c+(sigma+s)/2,
n=(s,c).
```

Half-plane containment gives `sA+cB>=(1+c+sigma)/2`, and hence

```text
n dot (X,Y) >= H.                                  (2)
```

The largest squared vertex norm of the square is
`(|A|+1/2)^2+(|B|+1/2)^2`, which is at least `X^2+Y^2`. Therefore

```text
X^2+Y^2 <= 17/4.                                   (3)
```

Suppose the required upper bound failed. Then

```text
X >= X_0 = 1+a c+h s.
```

Put `Y_0=(H-sX_0)/c`. In both cases below,

```text
X_0-sH>0,   Y_0>0.                                (4)
```

These conditions imply that the intersection point `(X_0,Y_0)` is the point
of smallest norm satisfying the two half-plane constraints. One direct
verification is

```text
(X_0,Y_0) = (Y_0/c)n + ((X_0-sH)/c^2)(1,0).
```

Both coefficients are positive. Taking its dot product with
`(X-X_0,Y-Y_0)` and using the two constraints yields a nonnegative result.
Expansion of the squared distance then gives

```text
X^2+Y^2 >= X_0^2+Y_0^2.                            (5)
```

For positive tilt with `h=p`, we have `H=1/2+c+sigma` and

```text
X_0-sH = c(c-sigma+a)+(p-1/2)sigma > 0,
Y_0 = 1-a sigma+(1/2-p sigma^2)/c > 0.
```

Here `c>=sigma`, `p>1/2`, and `p<1`. For negative tilt with `h=q`, we have
`H=1/2+c` and `X_0=1+a c-q sigma>0`, since `q<sqrt(2)` and
`sigma<=1/sqrt(2)`. Thus `X_0-sH=X_0+sigma H>0` and
`Y_0=(H+sigma X_0)/c>0`. This proves (4).

## 3. Two explicit positive polynomial identities

Set

```text
z=tan(|theta|/2),
c=(1-z^2)/(1+z^2), sigma=2z/(1+z^2),
0<=z<=sqrt(2)-1<1/2.
```

For the positive-tilt case with `h=p`, direct expansion gives

```text
X_0^2+Y_0^2-17/4
 = N_+(z) / [16384(1-z^2)^2(1+z^2)],

N_+(z) = 356+51348z-109667z^2-75264z^3
            +201629z^4+23916z^5-60060z^6.
```

For the negative-tilt case with `h=q`, the corresponding identity is

```text
X_0^2+Y_0^2-17/4
 = N_-(z) / [4096(1-z^2)^2(1+z^2)],

N_-(z) = 89+5824z-345z^2-38400z^3
            +66471z^4-16576z^5-15015z^6.
```

For completeness, both polynomial positivities have the following explicit
algebraic certificates. Define the seven nonnegative polynomials

```text
E_i(z) = binomial(6,i) (2z)^i (1-2z)^(6-i),  i=0,...,6.
```

Their sum is `1` on `[0,1/2]`. The two identities

```text
240 N_+(z) = sum_i C_i E_i(z),
960 N_-(z) = sum_i D_i E_i(z)
```

hold with these strictly positive integer coefficients:

| i | C_i | D_i |
| --- | ---: | ---: |
| 0 | 85440 | 85440 |
| 1 | 1112400 | 551360 |
| 2 | 1700692 | 1011760 |
| 3 | 1737420 | 1236240 |
| 4 | 1311317 | 1260284 |
| 5 | 742640 | 1302380 |
| 6 | 387840 | 1455915 |

These are polynomial identities, verifiable by expanding the displayed
binomials. They prove `N_+(z)>0` and `N_-(z)>0` throughout the full interval;
no sampled or interval-search premise is used.

Thus `X_0^2+Y_0^2>17/4` in both hard cases. Together with (5), this
contradicts (3). The desired upper bounds, and hence both exclusions in
(1), follow.
