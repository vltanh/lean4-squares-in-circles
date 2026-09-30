# B — axial-boundary derivative ratio by concavity

Baseline: `1dbbd4f106e9860752e9c0c612864196167df103`.
Target: `Seven.Boundary.ratio_derivative_lt_one` in
`SquaresInCircles/Seven/TargetBoundaryMonotonicity.lean`.

## 1. Recover the geometric coordinates

On the circular part of the axial-label boundary, put

```text
Y(s)=1/2+4s/5,          X(s)=sqrt(13/4-Y(s)^2).
```

Thus `X^2+Y^2=13/4`. The existing `axial_circle_bounds` proves

```text
8/5 < X < 7/4,         Y>0.
```

The ratio used to control the target support is

```text
r(s)=X(s)*(9/5-X(s)) / [Y(s)*(X(s)-4/5)].
```

Differentiating, using `Y'=4/5` and `X'=-4Y/(5X)`, and eliminating Y squared
by the circle identity gives the production identity

```text
1-r'(s)=N(X) / [5X(5X-4)^2(13-4X^2)],

N(X)=-500X^5+800X^4+1705X^3-3900X^2+3120X-1872.
```

Every denominator factor is positive: X>8/5, 5X-4>0, and
`13-4X^2=4Y^2>0`. The only remaining issue is the sign of N.

## 2. The new sign proof: N is concave on the whole enclosure

Differentiate twice, and translate by the lower endpoint. For `t=X-8/5>=0`,

```text
N''(8/5+t)=-7816-35850t-38400t^2-10000t^3 < 0.
```

The translation makes the reason for concavity explicit. There is no sign
change or subdivision anywhere in the actual interval.

A concave function is at least the smaller of its endpoint values. Here

```text
N(8/5)=2992/25 > 0,
N(7/4)=20113/256 > 0.
```

Therefore `N(X)>=20113/256>0` on `[8/5,7/4]`. The positive denominator then
implies `r'(s)<1`, exactly the existing theorem.

This replaces all six Bernstein coefficients by one concavity calculation and
two rational endpoint values. The quintic is not a mysterious positivity
object: it is concave throughout the geometric coordinate enclosure.

## 3. Constants and domains

`8/5` and `7/4` are rational enclosures of the radial coordinate already proved
in `axial_circle_bounds`, not switch points between different estimates.
The coefficients in N come from the explicit derivative and the circle
identity. Translating to X-8/5 is simply a way to display the sign of N''.

Do not claim concavity of N on all real numbers. The displayed sign argument
requires X>=8/5. This is sufficient for every production caller.

The strict positive bound also preserves the strict derivative inequality used
by the circular-boundary monotonicity proof; no equality case is introduced.

## 4. Lean handoff

Suggested local helper:

```lean
lemma ratio_numerator_pos {X : ℝ} (hX : 8/5 ≤ X ∧ X ≤ 7/4) :
    0 < -500*X^5+800*X^4+1705*X^3-3900*X^2+3120*X-1872 := ...
```

Define N, N' and N''; produce their `HasDerivAt` proofs using sums and powers.
Rewrite N'' with t=X-8/5 by `ring`. The sign follows from `t>=0` and positivity
of powers. Apply the existing `Seven.positive_of_concavity`, with the two
endpoint values closed by `norm_num`.

Use that helper in place of the `bernstein_pos` block inside
`ratio_derivative_lt_one`. Keep the exact denominator identity and the rest of
`TargetBoundaryMonotonicity.lean` unchanged.

## Validation

The derivative transformation, translated N'', and both endpoint values were
checked by exact symbolic/rational arithmetic. The displayed proof does not
use a computational success premise. The Lean recipe is not a claim of
successful compilation or kernel validation.
