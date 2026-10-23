# A — marker-arc curvature by a ratio majorant

Baseline: `1dbbd4f106e9860752e9c0c612864196167df103`.
Target: `Seven.arcCurvaturePolynomial_pos` in
`SquaresInCircles/Seven/MarkerArc.lean`.

## 1. The actual curvature comparison

Apart from a constant, the marker-arc envelope is

```text
f(x)=(1/3)sqrt(13/4-(x+1)^2)+arcsin x-3x/4.
```

Its second derivative is

```text
f''(x)=x/(1-x^2)^(3/2)
       -(13/12)/(13/4-(x+1)^2)^(3/2).
```

On `0<=x<=3/4`, both radicands are strictly positive. Thus comparing the two
nonnegative curvature terms, and squaring, gives the equivalent inequality

```text
P(x)=676(1-x^2)^3-9x^2(9-8x-4x^2)^3>0.
```

The production proof establishes this with nine Bernstein coefficients. The
following argument explains the sign directly, without expanding P.

## 2. A simple majorant for the ratio of the radicands

Put `D=1-x^2` and `H=9-8x-4x^2`. On the stated interval,

```text
D >= 7/16 > 0,           H >= 3/4 > 0.
```

The exact factorization

```text
(9-6x)D-H = x(6x^2-5x+2)
          = x*[6(x-5/12)^2+23/24] >= 0
```

proves the whole-interval bound

```text
H/D <= 9-6x.
```

The line `9-6x` is a convenient upper bound for the radicand ratio. Its
validity is explained by the displayed square; no fitting or interval testing
is involved.

## 3. One elementary maximum, at a derived critical point

Since H and D are positive, cubing preserves the inequality. Hence

```text
P(x) >= D^3*[676-9 g(x)],
g(x)=x^2(9-6x)^3.
```

Differentiate before expanding:

```text
g'(x)=6x(9-6x)^2(3-5x).
```

Therefore g increases up to `x=3/5` and decreases afterwards on `[0,3/4]`.
This critical point is derived from the derivative, not a selected subdivision.
Its exact maximum is

```text
g(3/5)=177147/3125.
```

Consequently

```text
676-9 g(x) >= 518177/3125 > 0,
P(x) >= (518177/3125)*(1-x^2)^3 > 0.
```

This proves the original polynomial lemma, and hence the curvature comparison,
on the entire original interval. The margin is deliberately coarse and ample;
there is no need to locate the exact minimum of the degree-8 polynomial.

## 4. What this changes, and what it does not

Only `arcCurvaturePolynomial_pos` needs a new proof. The existing derivative
formula for `arcEnvelope`, its use of concavity, and the marker-arc endpoint
bounds remain unchanged. In particular the marker definition, its arc length,
and the small-gap argument are untouched.

The original polynomial is retained only as the interface to those callers.
The human reason for its sign is a bound on the curvature ratio followed by
one elementary maximum, not positivity of an expanded coefficient vector.

## 5. Lean handoff

Suggested helper statements:

```lean
lemma curvature_ratio_majorant {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 3/4) :
    9-8*x-4*x^2 ≤ (9-6*x)*(1-x^2) := ...

lemma curvature_product_bound {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 3/4) :
    x^2*(9-6*x)^3 ≤ 177147/3125 := ...

lemma arcCurvaturePolynomial_pos {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 3/4) :
    0 < arcCurvaturePolynomial x := ...
```

The first uses the factored identity, `sq_nonneg`, and `mul_nonneg`.
For the second, give the displayed derivative with `HasDerivAt`, apply
`Seven.monoOn_of_hasDeriv_nonneg` below `3/5` and
`Seven.antiOn_of_hasDeriv_nonpos` above it, and evaluate at `3/5`.
For the third, use positivity of H,D, monotonicity of cubing, and the final
rational margin. No old positivity lemma is needed to prove these helpers.

## Validation

The ratio factorization, derivative factorization and rational maximum/margin
were independently checked by exact symbolic arithmetic. This is a written
mathematical replacement with an integration sketch, not a compiled Lean
replacement. No production code was changed.
