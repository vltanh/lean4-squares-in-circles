# Negative-tilt low squares contain one of two fixed interior points

This proves the negative-tilt low-square branch of the one-neck stabbing
argument in [ONE_NECK_STABBING.md](ONE_NECK_STABBING.md). It is a conditional
one-square lemma; the neck inequalities are stated explicitly below.

Set

```text
P = (27/64,255/256),
Q = (-27/64,5/4).
```

Let a unit square lie in the disk of squared radius `17/4`. Suppose its
lower vertex is `B=(b,1/2-d)`, and its two edge vectors from that vertex are

```text
e = (-c,s),    f = (s,c),
c=cos(theta), s=sin(theta), 0<theta<=pi/4.
```

Assume `d>0` and the neck inequalities

```text
sb >= cd,
cb+sd <= c.                                         (1)
```

These hold when the part of the square below height `1/2` fits in the
horizontal neck `0<=x<=1`; the domain reduction in the companion note
establishes them. They imply `0<=b<=1`. We prove that **P or Q lies strictly
inside the square**.

Write

```text
a = 108/256 = 27/64,
v = 127/256 = P_y-1/2,
delta = 65/256 = Q_y-P_y.
```

For any point `Z`, its coordinates relative to the lower vertex and these
edge vectors are

```text
lambda_Z = e dot (Z-B),
mu_Z     = f dot (Z-B).
```

The point is strictly inside the square precisely when both coordinates
belong to `(0,1)`.

## 1. Three strict side inequalities for P

For P the coordinates are

```text
lambda_P = c(b-a)+s(v+d),
mu_P     = s(a-b)+c(v+d).
```

The second inequality in (1) gives

```text
lambda_P <= c(1-a)+sv
         <= sqrt(148^2+127^2)/256 < 1.
```

The first inequality in (1) gives

```text
mu_P <= sa+cv
     <= sqrt(108^2+127^2)/256 < 1.
```

We also have `mu_P>0`. If `theta<=pi/6`, use `b<=1`, `d>=0`,
`c>=sqrt(3)/2>4/5`, and `s<=1/2` to obtain

```text
mu_P >= cv-s(1-a)
     > (4/5)(127/256)-(1/2)(148/256)
      = 69/640 > 0.
```

Now suppose `pi/6<=theta<=pi/4`. On this interval

```text
f dot P = (108 sin(theta)+255 cos(theta))/256 > 1.    (2)
```

Indeed this expression is positive and concave as a function of `theta`,
so its minimum is at an endpoint. At `pi/6` it is greater than
`(108+255(8/5))/512=129/128>1`, since `sqrt(3)>8/5`. At `pi/4` it is
`363/(256 sqrt(2))>1`, because `363^2>2(256^2)`.

Every face of a unit square contained in the disk of squared radius `17/4`
has absolute support at most `2` in its own unit normal direction. To see
this, the two vertices on the face have normal coordinate `h` and transverse
coordinates differing by one. One transverse coordinate has absolute value
at least `1/2`, so `h^2+1/4<=17/4` and hence `|h|<=2`.

If `mu_P<=0`, then `f dot B>=f dot P`. The opposite face has normal
coordinate `f dot B+1>=f dot P+1>2`, contradicting that support bound.
This proves `mu_P>0` also in the second angle range.

We have shown

```text
lambda_P < 1,       0 < mu_P < 1.
```

Therefore P is an interior point unless `lambda_P<=0`.

## 2. The remaining failure puts Q strictly inside

Assume `lambda_P<=0`. Then

```text
b <= a-(s/c)(v+d).                                  (3)
```

The other point has coordinates

```text
lambda_Q = c(b+a)+s(3/4+d),
mu_Q     = -s(a+b)+c(3/4+d).
```

Clearly `lambda_Q>0`. Using `lambda_P<=0` and `3/4=v+delta`,

```text
lambda_Q = lambda_P+2ca+s delta
         <= sqrt(216^2+65^2)/256 < 1.
```

The first neck inequality gives

```text
mu_Q <= -sa+(3/4)c <= 3/4 < 1.
```

Finally (3) gives

```text
mu_Q >= (v+d)/c+delta c-2as
     >= v+(delta-2a)/sqrt(2)
      = (127-151/sqrt(2))/256 > 0.
```

Here we used `c>=1/sqrt(2)`, `s<=1/sqrt(2)`, `c<=1`, and `d>=0`.
The final positivity follows from `2(127^2)>151^2`.

Thus both coordinates of Q lie strictly between zero and one. In every
case, P or Q is strictly inside the square, proving the branch lemma.
