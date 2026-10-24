# Uniform positive-normal cap exclusion above y=1/2

This proves a complete single-square case needed by the still-open
WEDGE.2 argument. It does not by itself prove WEDGE.2 or Y.ALL.

Write `D={x^2+y^2<=17/4}`, `R=sqrt(17)/2`, and let

```
n=(b,a),  0<=a<=b,  a^2+b^2=1,
k=1/2+a/sqrt(2).
```

There is **no** unit square T contained simultaneously in D and
the two half-planes

```
y>=1/2,    n.x>=k.
```

## 1. Reduce all orientations to three support sums

For T's centered square body, let `H(v)` denote its support function.
Put

```
mu=1-a,   d=n+mu*e_y=(b,1),
r=|d|=sqrt(2-a^2),   delta=1/sqrt(2)-1/2.
```

The two floor inequalities imply

```
d.c_T >= k+mu/2+H(n)+mu*H(e_y).
```

Containment in D implies `d.c_T+H(d)<=R*r`. Hence

```
1+delta*a + H(n)+(1-a)*H(e_y)+H(d) <= R*r.       (1)
```

As the frame of a square rotates, each support function is a positive
linear combination of the absolute sine and cosine of its angular
difference from that frame. Between successive angles where one of
the three vectors n,e_y,d is parallel to a frame axis, the support
sum has second derivative equal to its negative. It is therefore
concave on each such interval, and its minimum occurs at one of
those three frames. The values are, respectively,

```
S_n = 1+(1-a)*(a+b),
S_y = 1+b,
S_d = r+b*(1-a)/r.
```

For completeness, at the n frame the e_y projections are a,b and
the d projections are `1+a-a^2` and `b*(1-a)`. At the d frame,
direct summation over the orthonormal axes `d/r,(-1,b)/r` gives S_d.

We show all three numbers satisfy `1+delta*a+S>R*r`, contradicting
(1). The exact rational estimates below are deliberately weaker than
the sharp bounds, to make the verification elementary.

## 2. Rational bounds used in the verification

For `0<=a<=1/sqrt(2)`, we have

```
delta > 207/1000 > 1/5,
R < 33/16,                    R-1 < 17/16,
b >= 1-(59/100)*a^2,
r < 99/70-(707/2000)*a^2,
r >= 707/500-(19/50)*a^2.                              (2)
```

The bound for b follows from the chord of `sqrt(1-t)` on `[0,1/2]`
and `2-sqrt(2)<59/100`.

The upper bound for r follows from the tangent inequality
`sqrt(2-t)<=sqrt(2)-t/(2*sqrt(2))`, together with
`sqrt(2)<99/70` and `1/(2*sqrt(2))>707/2000`.

The lower bound for r follows by concavity: at `t=0` the proposed
line is `707/500<sqrt(2)`, and at `t=1/2` it is
`153/125<sqrt(3/2)`. All constant comparisons follow by squaring
positive rational numbers; in particular `R<33/16` is `1088<1089`.

## 3. The frame parallel to e_y

Using (2),

```
1+delta*a+S_y-R*r
 > 93/1120 + a/5 + (4451/32000)*a^2 > 0.
```

## 4. The frame parallel to n

Using (2) gives

```
1+delta*a+S_n-R*r > P(a),

P(a)=93/1120 +(207/1000)*a -(27549/32000)*a^2
     +(59/100)*a^3.
```

Here `0<=a<=1/sqrt(2)<5/7`. Put `z=7*a/5`, so `0<=z<=1`.
The following exact identity has strictly positive coefficients:

```
P(5*z/7)
 = (93/1120)*(1-z)^3
   + 3*(741/5600)*z*(1-z)^2
   + 3*(11037/313600)*z^2*(1-z)
   + (14641/2195200)*z^3 > 0.
```

The identity is checked simply by expansion.

## 5. The frame parallel to d

Multiplying the desired difference by the positive number r gives

```
r*(1+delta*a+S_d-R*r)
 = (1+delta*a)*r+b*(1-a)-(R-1)*(2-a^2).
```

Using (2), the right side is strictly greater than

```
Q(a)=289/1000 -(1793/2500)*a +(37/400)*a^2
     +(257/500)*a^3.
```

Its positivity has this exact expansion about `s=5/8`:

```
Q(a)=607/256000 +(123/160000)*(a-5/8)
     +(147/200+(257/500)*a)*(a-5/8)^2
    >= 121/64000 > 0.
```

The last step uses only `a>=0`. This proves the third contradiction
to (1), and hence the theorem for every square orientation.
