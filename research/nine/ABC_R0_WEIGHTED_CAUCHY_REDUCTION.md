# R0 scalar: elementary small ratios and one weighted-Cauchy certificate

Date: October 25, 2026. **Status: accepted after independent full source, domain and exact-arithmetic review. See `REVIEW_ABC_R0_WEIGHTED_CAUCHY_2026_10_25.md`.**

This replaces the scalar proof in Sections 6--8 of
`ABC_R0_FULL_ANGLE_BLOCK_PRESSURE.md`, while leaving its physical equations,
whole-angle pressure theorem, strict reserve and original ABC assembly
unchanged. It introduces no new gate and no additional geometric assumption.

The whole force-ratio interval `0<=x<=1` is proved below by an elementary
concavity argument with **no polynomial certificate**. For `x>=1`, one
weighted Cauchy inequality replaces the two successive squarings. Its
single polynomial has degree `(8,14)` and needs **270 exact coefficient
checks**, in two rectangles, instead of the previous **1,559** checks,
three polynomials and seven rectangles. This is a reduction of **1,289
checks**, about **82.7%**. The large-ratio argument remains
exact-arithmetic-assisted; it is not described as wholly table-free.

## Current table-free proof

Section2 below remains the active elementary proof for0<=x<=1.
For every x>=1, `ABC_R0_ANGULAR_ENDPOINT_REDUCTION.md` and
`ABC_R0_POSITIVE_ENDPOINT_ANALYTIC.md` now provide a complete analytic
proof, accepted in `REVIEW_ABC_R0_TABLE_FREE_2026_10_25.md`. The full
angle interval reduces by concavity to two explicit scalar endpoints,
both proved on the entire unbounded ratio domain. The270-sign packet
in Sections3--5 below is preserved as a historical alternative and is
no longer a proof dependency. The original strict pressure reserve is
unchanged.

## 1. Unchanged target

Put `K=79/40`, and for `x>=0`, `|d|<=1/sqrt(2)` define

```
e=sqrt(1-d^2),
a=x^2+1-2*d*x,
b=2*x^2+1+2*x*(e-d),
p=a+d*x/2,
q_s=b+d*x*(e+d)/(2*e),
h=(8+16*d)/25,  t_s=x/2-h.
```

The target, exactly as in the original source, is

```
K*p/sqrt(a)-q_s/sqrt(b)-x/2+h > 0.                 (1)
```

All `a,b,p,q_s` are strictly positive. For example, `a=(x-d)^2+e^2`,
`b>=1+2*x^2`, `p=x^2+1-(3/2)*d*x>0`, and
`q_s=2*x^2+1+x*(2*e-(3/2)*d+d^2/(2*e))>0`.
Both closed angle endpoints and x=0 are permitted enlargements of the
original physical positive-force domain.

## 2. A table-free proof on the entire interval 0<=x<=1

Write `r=1/sqrt(2)`. The exact square identities give

```
p^2/a = x^2+1-d*x + d^2*x^2/(4*a),
q_s^2/b = 2*x^2+1+(e+1/e-d)*x
                  +d^2*x^2*(e+d)^2/(4*e^2*b).    (2)
```

Since `r<=e<=1`, the function `e+1/e` is decreasing and is at most
`3*r`. Also `d^2<=1/2`, `(e+d)^2<=2`, `e^2>=1/2`, and `b>=1`.
Thus

```
p/sqrt(a) >= sqrt(A),
q_s/sqrt(b) <= sqrt(B),
A=x^2+1-d*x,
B=(5/2)*x^2+1+(3*r-d)*x.                         (3)
```

For fixed x, define

```
g(d)=K*sqrt(A)-sqrt(B)-x/2+8/25+(16/25)*d.
```

Here `B-A=(3/2)*x^2+3*r*x>=0`, so

```
g''(d)=(x^2/4)*(B^(-3/2)-K*A^(-3/2)) <= 0.       (4)
```

For x=0 this is simply a linear function. Hence the minimum on the
closed d interval is bounded below by the smaller endpoint value
`g(-r),g(r)`.

Both endpoint functions decrease throughout `0<=x<=1`. To see this
without solving a critical-point equation, note that each square root
of A is convex in x, because its quadratic discriminant quantity is
`4-r^2=7/2>0`. Its derivative is therefore at most its value at x=1,
namely `sqrt(2-d)/2`. Each square root of B at d=+r or -r is also
convex: its corresponding quantities are respectively 8 and 2. Its
derivative is at least its value at x=0, respectively r and 2r.
Consequently

```
g_x(r) <= K*sqrt(2-r)/2-r-1/2 < 0,
g_x(-r) <= K*sqrt(2+r)/2-2*r-1/2 < 0.             (5)
```

The strict signs use `K<2`,
`sqrt(2-r)<r+1/2` (because `r>5/8`), and
`sqrt(2+r)<2*r+1/2` (the squared reserve is `r+1/4>0`).

It remains only to bound the two values at x=1. The elementary interval
`7/10<r<71/100` gives, by squaring positive rational bounds,

```
sqrt(2-r)>113/100,   sqrt(7/2+2*r)<111/50,
sqrt(2+r)>41/25,     sqrt(7/2+4*r)<63/25.
```

Therefore

```
g(r)|_(x=1) > K*(113/100)-111/50-9/50+(16/25)*(7/10)
             =1119/4000,
g(-r)|_(x=1)> K*(41/25)-63/25-9/50-(16/25)*(71/100)
             =423/5000.                          (6)
```

Equations (3)--(6) prove (1), with a margin greater than `423/5000`,
throughout the whole small-ratio rectangle. No sampled sign, angular
partition, Bernstein coefficient or external solver is involved.

## 3. Weighted Cauchy for every large force ratio

For `x>=1`, choose only an algebraic comparison weight

```
rho=3/10-d/10-1/(8*x) > 1/10 > 0.                (7)
```

Indeed `d<3/4` on the entire closed physical angle interval. This
weight is not a pair force or an application mean; no original physical
quantity is altered.

For any real t and positive rho,

```
(q_s/sqrt(b)+t)^2
 <= (1+rho)*q_s^2/b+(1+1/rho)*t^2,                (8)
```

because the difference is
`(sqrt(rho)*q_s/sqrt(b)-t/sqrt(rho))^2`.
Thus it suffices to prove the single strict inequality

```
W=K^2*p^2/a-(1+rho)*q_s^2/b-(1+1/rho)*t_s^2>0.   (9)
```

There is no sign condition on `t_s` in (8). Since `K*p/sqrt(a)>0`,
(9) implies it is strictly larger than the absolute value of
`q_s/sqrt(b)+t_s`, and hence proves (1).

## 4. One explicit rational polynomial

Use the original half-angle variable

```
z=d/(1+e),  Dn=1+z^2,  En=1-z^2,  dn=2*z,
d=dn/Dn, e=En/Dn.
```

The physical range lies in `[-5/12,5/12]`, where Dn and En are
positive. Set

```
aa=Dn*(x^2+1)-2*dn*x,
bb=Dn*(2*x^2+1)+2*x*(En-dn),
pp=Dn*(x^2+1)-(3/2)*dn*x,
qq=En*bb+dn*x*(En+dn)/2,
tt=x*Dn/2-(8*Dn+16*dn)/25,
rn=x*(3*Dn-dn)/10-Dn/8,
rd=x*Dn.
```

The substitutions are exactly

```
a=aa/Dn, b=bb/Dn, p=pp/Dn,
q_s=qq/(Dn*En), t_s=tt/Dn, rho=rn/rd.
```

Define the single polynomial

```
J=K^2*pp^2*bb*En^2*rn*rd
       -(rd+rn)*rn*qq^2*aa
       -(rd+rn)*x*tt^2*aa*bb*En^2.               (10)
```

Direct common-denominator multiplication gives the global identity

```
J=x*Dn^2*En^2*rn*aa*bb*W.                        (11)
```

Every multiplier in (11) is positive on the actual large-ratio domain.
In particular rn=rd*rho>0 by (7). It is enough to show J>0. The
enlarged z rectangle is used to certify a polynomial sign; the physical
positivity assumptions in (11) need only be checked on the original
angle domain.

## 5. Complete 270-coefficient certificate

The polynomial J has degree `(8,14)` in `(x,z)` and 128 nonzero
ordinary coefficients. Put

```
u=1-1/x,
Jlarge(u,z)=(1-u)^8*J(1/(1-u),z).
```

For every finite x>=1, `0<=u<1` and the normalizing factor is positive.
The compactified endpoint u=1 is harmless. Express each restriction
below in the tensor-product Bernstein basis on its whole rectangle:

| u interval | z interval | Degrees | Count | Every coefficient exceeds |
| --- | --- | --- | ---: | ---: |
| `[0,3/4]` | `[-5/12,5/12]` | `(8,14)` | 135 | `1/200` |
| `[3/4,1]` | `[-5/12,5/12]` | `(8,14)` | 135 | `3/500` |

`ABC_R0_WEIGHTED_CAUCHY_CHECK.py` constructs J from (10) using exact
rational arithmetic, proves the whole reciprocal inverse, reconstructs
all 270 coefficients, checks each displayed strict bound, and expands
each full Bernstein representation back to its ordinary coefficients.
No stored sign list is trusted as input. Optional `--json PATH` saves
the complete ordinary and Bernstein coefficients for inspection.

For reference, after affine transformation to variables v,w on the
unit square, if the power coefficients are c_kl, the Bernstein values
are

```
b_ij=sum_(k<=i,l<=j) c_kl * binom(i,k)/binom(8,k)
                              * binom(j,l)/binom(14,l).
```

The checked inverse is the entire identity

```
polynomial(v,w)=sum b_ij*binom(8,i)*binom(14,j)
                    *v^i*(1-v)^(8-i)*w^j*(1-w)^(14-j).
```

The basis is nonnegative and sums to one on the closed square. Both
rectangles, their common interface and the physical angle endpoints
are included. Hence J>0 everywhere required; (11), (9), and (8) prove
(1) for every x>=1. Section 2 includes x=1 as well, so no ratio boundary
or tail is unassigned.

## 6. Geometric reuse and validation limits

This is precisely the same scalar inequality used twice at the genuine
ratios `(mu/gamma,D)` and `(eta/nu,-D)` in the full-angle pressure theorem.
Its Cauchy aggregation, positive corrected denominator, `B/640` reserve,
root-degree extension, whole ABC assembly and physical completion scope
are unchanged. No new circle mask, owner or normal selection is added.

The small-ratio proof is elementary. The remaining 270 signs are exact
finite algebra, not sampled configurations. Independent review passed and the accepted scalar reference is now this
replacement. The
older 1,559-sign source remains available as provenance. No Lean build,
CI, workflow dispatch or claim of unrestricted nine-square closure.

