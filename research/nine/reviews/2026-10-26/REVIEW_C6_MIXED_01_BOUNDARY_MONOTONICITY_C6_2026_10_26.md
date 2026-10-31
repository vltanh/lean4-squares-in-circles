# Independent review: the whole mixed-01 tradeoff boundary

Date: October 26, 2026.

Reviewed source: `SIX_CYCLE_MIXED_01_BOUNDARY_MONOTONICITY.md`.

**Verdict: accepted.** The source proves the strict directional
monotonicity of `G(p,a,1-a)` throughout `3/10<=a<=1/sqrt(2)`
and for every `p>=1+1/sqrt(2)`. This is the missing boundary
statement; it is proved independently of the separate coordinate
monotonicities. There is no unproved numerical sign or computational
certificate dependency.

## 1. Exact derivative and full force range

I differentiated all definitions in (1) with `b=1-a` varying, including
`w` and `v`, and recovered every identity in (4). In particular the
factor `H` includes both the derivative of the sum of the two angles
and the derivative of the direction `(w,v)`. Neither term is omitted.
All denominators `s,t,v,D` are positive on the stated interval.

The two strict inequalities in (5) imply the desired negative
derivative at `p=P`. The separately proved positive bounds on `B`
and `H` justify extending the result to every `p>=P`, since
`p/D` is strictly increasing in `p` and `-pBH` is strictly
decreasing. This covers the full unbounded positive-force range,
not only the physically bounded ratios in another source.

## 2. The first derivative contribution

The subtraction identity (7) is exact. Writing
`Phi=w(w+s)-(3/2)a-4K^2`, I independently recovered

```
Phi'' = -2 - 6a/s - 3(1+sqrt(2)+a)/s^3 < 0.
```

The two endpoint lower bounds therefore prove `Phi>0` over the
whole interval by concavity. Because `v<3/2` and `a>0`, the
comparison with `w s-a v-v^2` has the correct strict direction.
Multiplication by `T>=0` in (7) gives the required non-strict
upper bound for `U_0'`; the case `T=0` at the right endpoint
is retained. Each subsequent bound for `w-v` is strict, so the
final comparisons with the force term are strict there as well.

The three intervals `[3/10,1/2]`, `[1/2,3/5]`, and
`[3/5,r]` cover the entire domain with both join points included.
The comparison `KP/D` decreases with `b` at fixed `P`, so
using respectively `b<=r`, `b<=1/2`, and `b<=2/5`
has the required direction. The three displayed expressions in
`Q(sqrt(2))` were independently expanded and agree exactly with
the squared comparisons. All squared sides are positive.

## 3. Positive angular factors

On this boundary, convexity of arcsine gives `A+C>=pi/3`,
while `a,b<=r` and their sum one give `A+C<pi/2`.
The proved `gamma<pi/8` therefore puts `A+C-gamma` in
`(5pi/24,pi/2)`, the interval where the sine comparison in
Section 3 is valid. The square-root estimates in (10) give precisely
`B>19/16`. For `a>=3/5`, every term in the sine-difference
formula has the sign required to obtain the stronger `B>5/3`.
The bound `v<11/10` follows directly from `w>19/5` and
the fixed value of `4K^2`.

## 4. Concavity of the auxiliary functions

Direct differentiation reproduces formula (16) for
`F_(lambda,m)''`. The comparison (15) has the correct direction
because `T=s-a>=0` and `1/v>=m`. The case `T=0` is
again retained. All upper estimates for the one positive term of
`F''` and lower estimates for its negative terms have positive
denominators and are valid throughout their stated intervals.

For `(lambda,m)=(1/2,2/3)` on `[3/10,1/2]`, the first
negative term alone exceeds the positive term by the displayed
positive reserve. The endpoint comparison at `a=3/10` correctly
uses increase in `t` and decrease in `s`. For
`(lambda,m)=(1/2,5/6)` on `[1/2,3/5]`, the improved reciprocal
bound follows from the proved increase of `w`, and the second pair
of endpoint values is positive. Thus the half-factor inequality
covers the complete interval through `3/5`.

For `(lambda,m)=(3/8,2/3)`, the first half of the interval
has an even stronger negative second-derivative bound. On the second
half, the two negative terms together exceed the positive term by
`10148/900375`. The strict bounds used there follow from the
original interval: `s>=r>70/99`, `t>6/7`, `b>2/7`,
and `a/s>4/7`. The smooth function is consequently concave
on the entire closed interval, including its midpoint. The right
endpoint comparison has positive squared sides and reduces exactly
to `116r-82>0`. Both complete endpoint arguments are valid.

Combining the resulting lower bounds for `H` with the two bounds
for `B` gives the second strict inequality in (5) on both intervals.
The multiplying factor `1-b/t` is strictly positive throughout,
so neither product comparison loses its strictness at a join or
endpoint.

## 5. Arithmetic audit and use in the full orbit join

All nineteen displayed rational evaluations were independently
recomputed with exact rational arithmetic and agree with the saved
source. The three force comparisons were also independently expanded
in `Q(sqrt(2))`. This arithmetic audit verifies the explicit
elementary proof; it does not introduce an extra executable checker
or coefficient packet into the dependency chain.

The lemma may therefore be used in
`SIX_CYCLE_MIXED_01_COMPLETE_EXCLUSION.md` with both fixed force
values `P=1+r` and `Q=9/4`, and with the complete boundary
intervals needed for those two cases. The original force scale,
physical means, nine squares, masks, radius window and positive
denominators are unchanged by that scalar comparison. The full
mixed-01 theorem and the exhaustive three-orbit theorem still require
their explicit joins, rather than being inferred merely from a
negative derivative.

No numerical optimization, interval sign grid, polynomial coefficient
packet, Lean compilation, CI or workflow action was used in this
review.
