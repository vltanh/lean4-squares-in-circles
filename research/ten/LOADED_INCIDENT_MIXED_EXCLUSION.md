# A loaded opposite corner and its incident side cannot be the two ring supports

**Status:** hand proof; independent full mathematical review passed on
2026-10-29, including arbitrary neighbor support types and normal-cone
boundary cases.

Use the physical loaded seven-ring in
`6241/1600<=R^2<=9/2`. Suppose a body has a unique circle vertex and
the incident mixed support pattern U2 or U3 of
[SEVEN_RING_OWNERSHIP_ALPHABET.md](SEVEN_RING_OWNERSHIP_ALPHABET.md).
Both physical neighbors are loaded. The argument permits either an edge
or a vertex support on each neighbor.

**Theorem.** These two local rows are impossible. In particular no
unique-circle body in the ring can have an incident edge/strict-vertex
support pair at its opposite corner.

## 1. Force and torque give a useful normal interval

Reflect and reverse the cyclic order if necessary. Use coordinates

```text
C=[X-1,X] x [-Y,1-Y],       w=(X,-Y),
1/2<X<1<Y,       X^2+Y^2=R^2,
A=(X-1,1-Y),       P=(p,1-Y),
t=p-X+1 in [0,1].
```

The incoming contact is the strict support vertex A, opposite w, and
the outgoing contact is on the top edge at P. The inequalities `X<1<Y`
are the reviewed necessary-coordinate restrictions for U2/U3.

Normalize the positive circle-load coefficient to one. Force balance
then writes the incoming force at A and the outgoing force at P as

```text
f_in=(X,-b),       f_out=(0,mu),
b>0, mu>0,       b+mu=Y.
```

The common positive origin torque gives `p>0`. Equality of the two
contact torques, with the displayed force balance, gives exactly

```text
mu*t=Y-X.                                           (1)
```

Put `H=Y-1`, `epsilon=1-X`. Since X<1 and
`R^2>=6241/1600`, one has `H>7/10`.
The neighbor beyond the top support is contained in `y>=-H` and contains
P. The general one-sided neighbor bound in Section 1 of
[LOADED_DOUBLE_SIDE_RESTRICTION.md](LOADED_DOUBLE_SIDE_RESTRICTION.md)
applies because p>0 and H>1/2. Since that neighbor is loaded,

```text
R^2<=(p+1)^2+H^2,
p>=p_0:=sqrt(X^2+2H+1)-1.
```

But `p<=X`, as P is on C's top side. Consequently `H<=X`, and hence
`p_0>=H`. Moreover

```text
X>4/5,
```

because otherwise `H<=X<=4/5` would give
`R^2=X^2+(H+1)^2<=97/25<6241/1600`.

Now `t=p-X+1>=H-X+1=Y-X`. Combining this with (1) and t<=1 gives

```text
Y-X<=mu<=1,
7/10<H<=b<=X<1,
0<epsilon<1/5.                                      (2)
```

These restrictions depend on the actual other loaded neighbor; force
balance alone would not give them.

## 2. The opposite-corner neighbor's normal points sufficiently upward

The inward unit supporting normal of the neighbor at A is

```text
n=(-c,s),       c=X/N, s=b/N,
N=sqrt(X^2+b^2),       0<s<=c, c^2+s^2=1.
```

From (2),

```text
H*b>=H^2>49/100,
epsilon*(N+X)<(1/5)(1+sqrt(2))<17/35.
```

The last bound uses `sqrt(2)<10/7`. Since
`49/100-17/35=3/700>0`, this proves

```text
H*s>epsilon*(1+c).                                  (3)
```

In particular `H>epsilon` and `s/c>epsilon/H`.

## 3. A supported-square vertex bound at A

Let K be any unit square with A on its supporting line and inward unit
normal n. We claim every vertex z of K satisfies

```text
|z|^2<=|A|^2+
 max(1+2(epsilon*s+H*c),
     2+2(epsilon*(c+s)+H*(c-s))).                     (4)
```

If A lies in a side interior, use tangent `v=(-s,-c)` and enlarge the
actual unit tangential interval to `[-1,1]`. Every vertex is then of the
form `A+xi*v` or `A+n+xi*v`, with `|xi|<=1`. Convexity in xi reduces
to the two endpoints. Since `A dot v=epsilon*s+H*c>0`, those endpoint
norms give exactly the two bounds in (4).

If A is a vertex, write `theta=atan(s/c)`, so `0<theta<=pi/4`.
The two incident unit edges have angles phi and `phi+pi/2`, with

```text
pi/2-theta<=phi<=pi-theta.
```

This interval is precisely the condition that n belongs to their inward
normal cone, including its boundary. The direction gamma of
`A=(-epsilon,-H)` lies in `(5pi/4,3pi/2)`. By (3),
`gamma>3pi/2-theta`. On the possible interval of adjacent-edge angles,
the scalar product with A has no interior maximum: its only possible
interior stationary point is the opposite direction, a minimum. Its
endpoint values are `+-A dot v`, so the maximum is `A dot v`.
This proves the first bound in (4) for both adjacent vertices.

The diagonal of K has length sqrt(2) and direction in
`[3pi/4-theta,5pi/4-theta]`. This entire interval lies strictly between
`gamma-pi` and gamma. The scalar product with A increases on it, so its
maximum occurs at the upper endpoint, the vector `n+v`. This gives the
second bound in (4). The vertex A itself satisfies (4) as well.

The point cannot lie in the interior of K because it lies on a supporting
line. Thus the two cases exhaust all supported unit squares.

## 4. Every vertex of that neighbor is strictly circle-clear

Since `A=(-epsilon,-H)`, one has

```text
R^2-|A|^2=2(X+H).
```

Subtract the first candidate bound in (4):

```text
R^2-[|A|^2+1+2(epsilon*s+H*c)]
 =2X-1+2H(1-c)-2epsilon*s
 > 8/5-1-2/5=1/5>0.                                (5)
```

For the second bound the difference is

```text
2[H(1-c+s)-epsilon(1+c+s)].                          (6)
```

It is strictly positive by (3), using the exact identity

```text
(1-c+s)(1+c)/s=1+c+s.
```

Equations (4)--(6) put every vertex of K strictly inside the radius-R
disk. Such a square cannot carry positive circle load. This contradicts
the assumed loaded neighbor at A and proves the theorem.

The argument excludes only the incident mixed unique-circle rows U2/U3.
The outer-edge mixed rows U4/U5, adjacent strict-vertex rows U8/U9,
radial-side circle bodies, and defects in pair support ownership remain
separate cases.
