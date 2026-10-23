# D — opposite-forward axial support by Cauchy–Schwarz

Baseline: `1dbbd4f106e9860752e9c0c612864196167df103`.
Target: `Seven.opposite_axial_scalar` in
`SquaresInCircles/Seven/OppositeForward.lean`.

## Statement

For `0<=z<=pi/3`, prove

```text
F(z)=1-4 pi/15+4z/5-(sqrt(3)-1)sin z-(1/2)(1-cos z)>0.
```

The production argument introduces a degree-5 Taylor polynomial and proves its
positivity with six Bernstein coefficients. Neither step is needed.

## Human proof

Put `a=sqrt(3)-1`. Since `(43/25)^2<3`, we have `sqrt(3)>43/25` and hence

```text
a^2+1/4 = 17/4-2 sqrt(3) < 81/100.
```

For every real z, Cauchy–Schwarz and `cos^2 z+sin^2 z=1` give

```text
a cos z+(1/2)sin z <= sqrt(a^2+1/4) < 9/10.
```

Therefore

```text
F'(z)=4/5-a cos z-(1/2)sin z > -1/10.
```

Integrate this uniform derivative bound from zero, or apply the mean value
theorem. For `0<=z<=pi/3`,

```text
F(z) >= F(0)-z/10
     >= 1-4 pi/15-pi/30
      = 1-3 pi/10
      > 2/35 > 0,
```

using `pi<22/7`. At z=0 the same lower bound follows directly from F(0).
This proves the complete original domain with a uniform positive reserve.

The reason for positivity is simple: the initial support reserve is larger
than the greatest possible accumulated decrease over the whole turn interval.
No search for the actual critical point, Taylor truncation, Bernstein basis,
or subdivision is required.

## Constants and strictness

`9/10` is a rational upper bound for the length of the fixed derivative vector
`(sqrt(3)-1,1/2)`. `43/25` verifies that bound by squaring. The final `2/35`
is the resulting reserve after the maximal possible angle `pi/3`.
These constants bound visible geometric quantities, not a hidden polynomial.

The bound is strictly positive including both endpoints. Thus all callers that
exclude this sector and its possible equality cases can remain unchanged.

## Proposed Lean integration

Replace only the body of `opposite_axial_scalar`. Suggested helpers:

```lean
lemma opposite_derivative_upper (z : ℝ) :
    (Real.sqrt 3-1)*Real.cos z+(1/2)*Real.sin z ≤ 9/10 := ...

lemma opposite_axial_uniform {z : ℝ} (hz : 0 ≤ z ∧ z ≤ Real.pi/3) :
    2/35 < 1-4*Real.pi/15+(4/5)*z-(Real.sqrt 3-1)*Real.sin z
      -(1/2)*(1-Real.cos z) := ...
```

For the first helper, use `Real.sq_sqrt`, `Real.sin_sq_add_cos_sq`, and the
nonnegative square of the orthogonal linear form to derive Cauchy–Schwarz.
For the second, show `F(z)+z/10` is nondecreasing using
`Seven.monoOn_of_hasDeriv_nonneg`, with its displayed derivative, and compare
at zero. Finish with the existing `pi_lt_22_over_7` bound.

These are integration sketches, not compiled declarations. No production
module was changed, and no machine-validation claim is made.
