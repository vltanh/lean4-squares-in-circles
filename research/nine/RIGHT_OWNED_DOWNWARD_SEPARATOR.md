# A right-owned downward separator is impossible

This is a proved finite SAT case for the still-open annular same-sign
pair target. It does **not** settle that target or Y.ALL.

Let `D={x^2+y^2<=17/4}` and let
`E=[1,2] x [-1/2,1/2]`. Suppose A and B are unit squares in D,
wholly in `y>=0`, each physically disjoint from E, with centers
`0<=x_A<x_B<1`. Assume `x_B-x_A>1/2`.

Then A and B cannot be separated, with B on the positive side, by an
axis of B of the form

```
n=(b,-a),  m=(a,b),  0<=a<=b,  a^2+b^2=1.
```

Here separating includes touching: the required inequality is
`n.c_B - n.c_A >= 1/2 + H_A(n)`.

We use only the standard center bound `|c_T|<=3/2` for a unit square
in D, the support bound `H_T(v)>=1/2` for a unit vector, and SAT.

## 1. The E/B separation forces B wholly above y=1/2

Because `x_B>1/2`, B cannot be wholly left of E: its horizontal
halfwidth is at least 1/2. It cannot be right of E, since `x_B<1`,
and cannot be below E, since B is wholly in the upper half-plane.
Thus an E-owned separating axis gives B wholly above y=1/2.

Consider a B-owned separating axis. The direction n cannot put B
to the positive side of E: that would require

```
b*x_B-a*y_B >= 2*b+a/2+1/2,
```

whereas the left side is less than b. If E is on the positive n
side of B, adjoining the A/B separation gives

```
n.(c_E-c_A) >= (a+b)/2 + 1 + H_A(n)
             >= (a+b)/2 + 3/2.
```

But `x_A>=0`, `y_A<=3/2` give
`n.(c_E-c_A)<=3(a+b)/2`. This would force `a+b>=3/2`, impossible
since `a+b<=sqrt(2)<3/2`.

The direction m cannot put E above B. Indeed that would require

```
a*x_B+b*y_B+1/2 <= a-b/2.
```

As `x_B>=0` and `y_B>=1/2`, it implies `a>=b+1/2`, impossible.
The remaining possibility is B above E along m, giving

```
a*x_B+b*y_B >= 2*a+b/2+1/2.
```

Using `x_B<1`, and B's vertical halfwidth `(a+b)/2`, gives

```
b*(y_B-1/2-(a+b)/2)
  > a+1/2-(a*b+b^2)/2
  = a*(1-b/2)+a^2/2 >= 0
```

when `a>0`; for `a=0` the original inequality gives `y_B>=1`.
In all cases B is wholly in `y>=1/2`.

## 2. The pair separator contradicts the circle bound

Put `p=n.c_B` and `q=m.c_B`. Since `x_A>=0`, `y_A<=3/2`,
and `H_A(n)>=1/2`, the A/B separation gives

```
p >= 1-3*a/2 =: p0.
```

The cap floor for B is

```
-a*p+b*q >= 1/2+(a+b)/2.
```

Thus

```
q >= (1/2+(a+b)/2+a*p)/b.
```

The squared norm of B's `(+, +)` vertex in its n,m frame is
`(p+1/2)^2+(q+1/2)^2`. Both lower expressions are positive for
`p>=p0` (here `p0>-1/2`), and they increase with p. Consequently
that vertex has squared norm at least

```
F(a) = (3*(1-a)/2)^2
       + (1+(1+3*a-3*a^2)/(2*b))^2.
```

We prove `F(a)>=9/2`, contradicting containment in D.
Let `C=1+3*a-3*a^2` and `D0=4+12*a-17*a^2`. Direct expansion gives

```
4*b^2*(F(a)-9/2) = 4*b*C-D0,

16*b^2*C^2-D0^2
  = a^2*(24+24*a-193*a^2+288*a^3-144*a^4).
```

Both C and D0 are positive on `0<=a<=1/sqrt(2)`; for D0 this
follows by concavity from its endpoint values `4` and
`6*sqrt(2)-9/2>0`. The quartic factor rewrites as

```
24+24*a-49*a^2-144*a^2*(1-a)^2
  >= 15+24*a-49*a^2
  >= min(15, 12*sqrt(2)-19/2) > 0.
```

The first inequality uses `a*(1-a)<=1/4`; the second uses
concavity on `[0,1/sqrt(2)]`. Thus `4*b*C>=D0` (equality only at
`a=0`), and `F(a)>=9/2`, as required.

## Scope

The hypotheses `x_B<1` and `x_B-x_A>1/2` hold in the noncanonical
same-sign branch by diagonal-center exclusion and the close-center
half-disk rigidity theorem. This lemma closes precisely a separator
owned by the square on the right with normal angle in `[-pi/4,0]`.
It leaves the corresponding separator owned by the square on the
left, and the positive-normal cases, open.
