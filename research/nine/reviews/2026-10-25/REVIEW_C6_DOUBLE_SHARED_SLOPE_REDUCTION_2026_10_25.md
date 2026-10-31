# Independent review: 49-sign double-shared C6 slope proof

Date: October 25, 2026. Reviewer: root, independently of `c6_joint`.

**Verdict: PASS.** `SIX_CYCLE_DOUBLE_SHARED_SLOPE_REDUCTION.md` proves
the same complete double-shared-channel exclusion as the original
209-sign argument, with no additional physical premise. It replaces
that packet by an elementary whole-domain torque-slope bound and one
degree-(6,6) circle-slope polynomial with **49 exact signs**. The remaining
circle comparison is explicitly computational exact algebra; the whole
replacement is not called table-free.

## 1. Original physical implication

I checked the retained definitions and equations against Sections 1--4
of `SIX_CYCLE_DOUBLE_SHARED_CHANNEL_EXCLUSION.md`. The actual third
square has distinct original applications with `0<ell<sqrt(2)-1`.
The unchanged corner coordinates obey `A,B>1/2`, and the actual
circle-equation determinant satisfies `Delta>=4+sqrt(2)>0`.

Its genuine torque expression is

```
F=S*A+ell*C*A-S*(1-ell)*B.
```

Thus the two inequalities
`(S+ell*C)/(S*(1-ell))<15/14<B/A` imply F<0 with strictly positive
normalizing factors A, S and 1-ell. This contradicts the actual T2
equation F=0. It neither assumes equal force magnitudes nor changes
the original shared application means or transverse transmitter positions.

## 2. Complete analytic torque-slope argument

For a fixed sum Sigma in the stated interval, cosine is concave on
the allowed alpha interval. The sum of its two terms is minimized at
one of its endpoint pairs, giving exactly
`cos(alpha)+cos(beta)>=1/sqrt(2)+(S+C)/sqrt(2)`.
Because the original ell is positive and `sin(beta)>=1/sqrt(2)`,
the direction of each subsequent inequality is correct:

```
0<=w=S+C<sqrt(2)-1=k,
ell<=k-w.
```

The identity `S=(w+sqrt(2-w^2))/2` uses the positive value of S-C
on the original angular domain. Both sides of the comparison
`sqrt(2-w^2)>=sqrt(2)-w/5` are positive before squaring. Its squared
reserve is `(2*w/25)*(5*sqrt(2)-13*w)>=0`, using `8*sqrt(2)<13`.
Hence `S>=1/sqrt(2)+(2/5)*w` throughout the full interval.

The torque slope is `1+ell*w/(S*(1-ell))`. Its extra term is
nondecreasing in ell for w>=0, and all replaced denominators are
positive. The required upper bound reduces to the stated quadratic
with leading coefficient 72/5, constant k, and middle coefficient
`74/5-(139/10)*sqrt(2)`. I independently expanded its discriminant
in exact `Q(sqrt(2))` arithmetic and obtained

```
[33153-23452*sqrt(2)]/50<0,
2*23452^2-33153^2=871199>0.
```

The quadratic is therefore positive for every real w, including w=0.
This proves the complete torque-slope bound without a coefficient list
or angle subdivision.

## 3. Exhaustive rectangle and global normalization

For chi=`3*pi/4-Sigma`, the exact relation is
`sin(chi)=w/sqrt(2)<1-1/sqrt(2)<120/409`.
The last reserve `409^2-2*289^2=239` is positive. Since both chi
and `2*atan(3/20)` lie in `[0,pi/4]`, sine is increasing there;
the source's full independent x/y rectangle contains every actual
pair `(Sigma,beta)`. Unphysical additional pairs are used only for
polynomial positivity, not for inferring physical Delta signs.

I substituted the displayed half-angle formulas directly. They give
`S=Sn/Ds`, `C=Cn/Ds`, `u=U/Dw`, `v=V/Dw`, and
`ell=En/(Ds*V)` because `cos(alpha)=C*u+S*v`. All four quantities
`p,q,r,s` then have the common denominator `base=Ds*Dw*V` exactly
as stated.

The physical circle equations imply

```
A=An/(2*Delta*base^3),
B=Bn/(2*Delta*base^3).
```

Consequently division of `14*Bn-15*An` by `Dw^2*V` gives the
global identity

```
G=2*Delta*Ds^3*Dw*V^2*(14*B-15*A).
```

This derivation checks the entire denominator identity, not a few
parameter evaluations. Every multiplier is positive on the actual
physical domain. In particular `V=Dw*sin(beta)>0` at both allowed
beta endpoints of the closed enlargement.

## 4. Independent reconstruction of all 49 signs

I wrote a separate dense bivariate implementation over exact rational
pairs representing `Q(sqrt(2))`. It reconstructed all defining
polynomials from the manuscript without importing the author's build
routine. It verified both unit-trigonometric identities as full
polynomial identities.

The exact division used a different algorithm: the divisor depends
only on y and has nonzero constant coefficient, so each x coefficient
was divided by a low-degree recurrence in y. Multiplying the resulting
degree-(6,6) quotient back by the complete divisor reproduced every
ordinary coefficient of the original numerator, including all higher
degrees. There was no discarded remainder or coefficient.

For the Bernstein conversion, the independent implementation used
lower-triangular elimination against explicitly expanded degree-six
Bernstein bases, first in y and then in x. It reconstructed the full
inverse in both variables. All **49** resulting field elements are
strictly greater than 7, checked by exact rational square comparisons.
Every ordinary quotient coefficient and every Bernstein coefficient
also matched the separately run production implementation exactly.

Since the nonnegative tensor basis sums to one on the closed rectangle,
this proves G>7 there. The positive physical normalization gives
`14*B-15*A>0`, and A>0 gives the second slope inequality. Both pieces
therefore prove F<0 on the entire original domain.

## 5. Scope and dependency accounting

The original physical derivation and its reflected third-interface
case remain unchanged. The argument preserves both original endpoint
means, every positive force ratio, both radius endpoints, all actual
transmitter sliders and all three arbitrary completion squares.
It introduces no post-extraction normal choice or body deletion.

This removes **160** coefficient checks from the double-share proof,
209 to 49. Together with the accepted table-free three-share inequality,
the two C6 scalar packets require **49 signs instead of 254**. Together
with the separate R0 reduction, these three targeted proof dependencies
require **319 signs instead of 1,813**, a reduction of 1,494 signs.
These numbers concern these explicit packets, not a count of every
certificate in PR #11.

No new geometric gate or coarse cell is closed merely by replacing an
already accepted exclusion proof. The one-/two-share completion cases,
strictly obtuse one-radial case, unrestricted bound, original equality
and older full prerequisite-chain audit remain open. No Lean compilation,
CI or workflow dispatch was used in this review.
