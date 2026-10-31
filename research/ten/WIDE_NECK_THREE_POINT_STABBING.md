# Three interior stabbing points for the upper wide neck

Let `D` be the origin-centered disk of squared radius `17/4`. Suppose a
unit square is contained in `D` and in `y>=0`, and is interior-disjoint
from the two axis-parallel squares centered at `(-3/2,0)` and `(3/2,0)`.
Then it contains at least one of the following points in its **interior**:

```text
P_- = (-27/64,255/256),
P_+ = ( 27/64,255/256),
O   = (0,5/4).
```

Consequently at most three pairwise interior-disjoint unit squares can
satisfy these hypotheses. Orientations are arbitrary.

Write

```text
a = 27/64 = 108/256,
p = 255/256,
q = 5/4,
e = p-1/2 = 127/256,
delta = q-p = 65/256.
```

## 1. Squares wholly above height one half

The completed cap theorem in
[ONE_NECK_CAP_STABBING.md](ONE_NECK_CAP_STABBING.md) says that every unit
square in `D` and `y>=1/2` contains either `P_+` or `(-a,q)` in its interior.
Reflection gives the analogous alternative `P_-` or `(a,q)`.
If neither `P_-` nor `P_+` belongs to the square's interior, both points
`(-a,q)` and `(a,q)` do. Convexity of the square's interior then puts their
midpoint O in its interior.

It remains to consider a square of minimum height `m<1/2`.

## 2. The wide neck and the chord at height p

Below height `1/2`, every part of such a square lies in the closed neck
`-1<=x<=1`. The outer obstacle corners `(+-2,1/2)` lie on the containing
circle and close the passages into the two side caps. Each side cap has
horizontal width less than one and cannot contain the square. This is
the same component argument used in
[STAGGERED_CHAIN_REDUCTION.md](STAGGERED_CHAIN_REDUCTION.md).

Put `d=1/2-m`, so `0<d<=1/2`. The square's maximum height is at least
`m+1>=1>p`, while `m<p`. Its horizontal chord `I` at height p therefore
crosses its interior. A point of I is an interior point of the square
exactly when it is in the relative interior of I.

We first prove that I cannot lie wholly to the right of `x=a`, or wholly
to the left of `x=-a`.

### Positive tilt: I cannot lie wholly to the right

Use edge vectors

```text
u=(c,s), v=(-s,c),
0<s<=c, c^2+s^2=1,
```

from the lowest vertex `B=(b,m)`. The own-frame coordinates of `P_+-B`
are

```text
alpha = c(a-b)+s(e+d),
beta  = -s(a-b)+c(e+d).
```

The chord cannot lie wholly to the right of P_+ if `alpha>0` and `beta<1`:
these are exactly the two strict inequalities for P_+ to be to the right
of the chord's left boundary.

If `d<=s`, the right chord endpoint at height `1/2` gives
`b+(c/s)d<=1`. Therefore

```text
beta <= s(1-a)+ce < 1.
```

The proof of `alpha>0` in the positive-tilt section of
[ONE_NECK_STABBING.md](ONE_NECK_STABBING.md) uses only this right-endpoint
inequality and disk containment, so applies unchanged. Explicitly, failure
would force the highest vertex V to satisfy

```text
u dot V >= 1+ac+ps,
v dot V >= 1+c/2-s,
|V|^2 >= (1+ac+ps)^2+(1+c/2-s)^2 > 17/4.
```

The last strict inequality is the exact positive-quartic calculation in
that note; it does not use the left edge of the narrower neck.

If `d>=s`, the rightmost vertex `B+u` has height `m+s<=1/2`, so the wide
neck gives `b+c<=1`. Using `d>=s` and `d<=1/2`,

```text
alpha >= 1-c+ca+se > 0,
beta  <= cp+s(1-a-c) <= p < 1.
```

For the second bound, `s<=d<=1/2` implies
`c>=sqrt(3)/2>1-a`. Thus I cannot lie wholly to the right in either case.

### Negative tilt: I cannot lie wholly to the right

Now use edge vectors `(-c,s),(s,c)` from the lowest vertex `B=(b,m)`.
Since `d<=1/2<c`, the right chord endpoint at height `1/2` is always
`b+(s/c)d`. The wide neck therefore gives

```text
cb+sd<=c,    b<=1.
```

For P_+, define

```text
lambda = c(b-a)+s(e+d),
mu     = s(a-b)+c(e+d).
```

The two inequalities needed to exclude a chord wholly to its right are
`lambda<1` and `mu>0`. The first follows directly:

```text
lambda <= c(1-a)+se < 1.
```

The proof of `mu>0` in Section 1 of
[ONE_NECK_NEGATIVE_TILT.md](ONE_NECK_NEGATIVE_TILT.md) uses only `b<=1`,
`d>=0`, and disk containment. For angles at most `pi/6`, it gives the
explicit bound `mu>69/640`. For angles between `pi/6` and `pi/4`, the
normal `(s,c)` has dot product with P_+ strictly greater than one; failure
of `mu>0` would force the opposite square face to have support greater
than two in its own normal direction, impossible in `D`. Thus that proof
also applies to the wider neck.

Reflection now excludes a chord wholly to the left of P_- for either
tilt sign. Axis-parallel low squares also have neither possibility: their
unit horizontal chord lies in `[-1,1]` and contains one of `-a,a` strictly.

Therefore, if neither P_- nor P_+ is interior, their chord satisfies

```text
I subset [-a,a],    length(I)<=2a<1.                (1)
```

## 3. A central narrow chord forces O into the upper corner

Reflect if necessary, so that the tilt is positive and `c>=s>0`. Put
`w=c+s`. A maximal horizontal chord of a unit square has length `1/c>=1`,
so (1) is not in the maximal-chord part of the square. It is not in the
bottom triangular part either: there its length would be

```text
(p-m)/(cs) >= 2(p-m) > 2(p-1/2) = 254/256 > 2a.
```

Thus I lies in the top triangular part. Let the highest vertex be
`T=(x_T,M)`, and put `t=M-p`. Then

```text
0<t<=s,
length(I)=t/(cs),
t>=w-p,
t<=2a cs.
```

The third inequality uses `M=m+w` and `m>=0`. Combining the last two
inequalities gives

```text
f(w)=a(w^2-1)-w+p >= 0.                            (2)
```

The quadratic f is convex. Both values

```text
f(1)=p-1 < 0,
f(sqrt(31)/4)=1425/1024-sqrt(31)/4 < 0
```

are strictly negative; the second follows by squaring positive quantities,
since `1425^2=2030625<2031616=31(256^2)`. Convexity then makes f negative
throughout `[1,sqrt(31)/4]`. Equation (2) therefore forces

```text
w>sqrt(31)/4,
2cs=w^2-1>15/16,
c^2<11/16.                                         (3)
```

For the last implication, use
`(c^2-s^2)^2=1-4c^2s^2<31/256` and `sqrt(31)<6`.
Also `sqrt(31)/4>89/64`, so

```text
t>=w-p>101/256.
```

These inequalities give the strict comparison

```text
a cs+c^2 delta
 < a/2+(11/16)delta
 = 1579/4096
 < 1616/4096 = 101/256 < t.                         (4)
```

In particular `t>delta`, so height q lies below the highest vertex and
remains in the upper triangular part. The chord endpoints at height p are

```text
x_T-(c/s)t,    x_T+(s/c)t.
```

Their containment in `[-a,a]` gives

```text
-a+(c/s)t <= x_T <= a-(s/c)t.
```

At height `q=p+delta`, the left chord endpoint is consequently at most

```text
a-t/(cs)+(c/s)delta < 0,
```

by (4). The right endpoint is at least

```text
-a+t/(cs)-(s/c)delta > 0,
```

again by (4), since `c>=s`. Thus x=0 is strictly between the endpoints:
O belongs to the square's interior.

This proves the three-point theorem in every case.

## 4. Every staggered four-square chain has total capacity at most nine

Assume the four-square chain from
[STAGGERED_CHAIN_REDUCTION.md](STAGGERED_CHAIN_REDUCTION.md), with centers

```text
(-3/2,0), (-1/2,t_1), (1/2,t_2), (3/2,0),
-1/2<=t_1,t_2<=1/2.
```

Its proved barrier puts every additional square wholly above or wholly
below `y=0`. The present theorem bounds either group by three.

If `t_1>=0`, the upper half of the fixed square centered at `(-1/2,0)`
is contained in the actual inner anchor centered at `(-1/2,t_1)`.
Consequently every additional upper square also avoids that fixed
middle-left obstacle. The completed two-point theorem
[ONE_NECK_STABBING.md](ONE_NECK_STABBING.md) bounds the upper group by two.
There are at most `2+3=5` additional squares.

If `t_1<=0`, reflection gives the same bound with the lower group bounded
by two. Thus every parameter choice has total capacity at most nine.
This is a complete arbitrary-orientation completion bound for the stated
four-square chain. It does not classify all possible ten-square packings.

If either `t_1=0` or `t_2=0`, the one-neck theorem applies on both sides
(with horizontal reflection if needed). Both groups then have capacity at
most two, so the entire chain has total capacity at most eight, regardless
of the other slide parameter.
