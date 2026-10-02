# N — initial boundary ratio: exact angle comparison, no decimal bracket

Baseline: `1dbbd4f106e9860752e9c0c612864196167df103`.
Targets: `Seven.Boundary.ratio_zero_lt` and its use in
`circleTarget_decreases`. These are research replacements, not compiled Lean.

## 1. Recover the actual comparison

Put `r=sqrt(3)`. At the start of the circular axial boundary, `X=r`, `Y=1/2`.
The derivative-control ratio is

```math
\rho_0=\frac{2r(9/5-r)}{r-4/5}.
```

The production proof bounds this by 51/200 using an enclosure of r ending in
17321/10000, then separately bounds sine to start its monotonicity argument.
The geometric comparison actually needed is much simpler:

```math
\rho_0<\tan(\pi/12)=2-\sqrt3.
```

The denominator is positive. After clearing it, the difference factors as

```math
(2-r)(r-\tfrac45)-2r(\tfrac95-r)=\frac{7-4r}{5}>0.
```

The final inequality follows from `7^2=49>48=(4sqrt(3))^2`.
Thus there is no need to enclose sqrt(3) numerically at all.

## 2. Start the original monotonicity proof

In `circleTarget_decreases`, the initial angle is
`theta=pi/3-t >= pi/12`, with `theta<pi/2`. On this interval,

```math
\sin\theta\cos(\pi/12)-\cos\theta\sin(\pi/12)
 =\sin(\theta-\pi/12)\ge0.
```

Because both relevant cosines are positive,

```math
\sin\theta-\rho_0\cos\theta
 \ge(\tan(\pi/12)-\rho_0)\cos\theta>0.
```

This is exactly the positive initial value required for the existing function
`E(s)=sin(pi/3-t+s)-ratio(s)*cos(pi/3-t+s)`.
Keep the derivative identity and the whole-interval monotonicity argument
unchanged, using replacement B for `ratio_derivative_lt_one`.

The angle pi/12 is the smallest possible initial support angle. The new
comparison is tied to that geometry rather than to a decimal chosen to fit
between two separate estimates.

## 3. Optional exact proof of the unchanged 51/200 helper

An integrator who prefers to keep the old internal helper statement can also
avoid all square-root brackets. Clearing its positive denominator and using
`r^2=3` gives

```math
\frac{51}{200}(r-\tfrac45)-2r(\tfrac95-r)
 =\frac3{1000}(1932-1115r)>0.
```

There is one exact squared comparison:

```math
1932^2-3\,1115^2=2949>0.
```

These integers are the result of clearing the specified rational inequality;
they are not a fitted enclosure. This proves the *original* `ratio_zero_lt`
verbatim. Section 1 is preferable for exposition because it also eliminates
the arbitrary intermediate threshold 51/200.

## 4. Integration recipe

Suggested alternative helper:

```lean
-- Proposed statement; not yet an implemented Lean declaration.
lemma ratio_zero_lt_twelfth_tangent :
    ratio 0 < 2-Real.sqrt 3 := ...
```

Use `axialX 0=sqrt 3`, `axialY 0=1/2`, `Real.sq_sqrt`, denominator
positivity, and the displayed factored difference. Express the angle comparison
through the sine subtraction identity, so a separate tangent API is optional.
Only the initial-value subproof changes. The strict derivative and monotonicity
claims retain their exact original hypotheses and conclusions.

## Status

This removes the need for 17321/10000 on the proposed path. The optional
section preserves the old helper exactly. Neither option invokes numerical
search, a Bernstein certificate, or the result being replaced. Production
integration and Lean/kernel validation remain separate.
