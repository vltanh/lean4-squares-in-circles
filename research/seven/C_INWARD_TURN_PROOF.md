# C — inward axial turn: one square and an increasing tail

Baseline: `1dbbd4f106e9860752e9c0c612864196167df103`.
Target: `Seven.inward_turn_profile` in
`SquaresInCircles/Seven/InwardAxialTarget.lean`.

## Statement and the quantity to bound

For `0<=z<=pi/2`, define

```text
F(z)=sin z-(4/5)z cos z-(3/4)(1-cos z)-z/50.
```

The required theorem is `F(z)>=0`. The following proof gives strict positivity
for z>0, and equality at z=0. It uses no Bernstein expansion.

## 1. The unit interval: explain the Taylor remainder by a factorization

For `0<=z<=1`, the standard signed Taylor bounds give

```text
sin z >= z-z^3/6,
cos z <= 1-z^2/2+z^4/24,
cos z >= 1-z^2/2+z^4/24-z^6/720.
```

Apply the upper cosine bound to the negative term `-(4/5)z cos z` and the
lower bound to the positive term `(3/4)cos z`. Consequently

```text
F(z) >= z q(z),
q(z)=9/50-3z/8+7z^2/30+z^3/32-z^4/30-z^5/960.
```

Instead of six Bernstein coefficients, use this exact identity:

```text
q(z) = (9/40)(z-5/6)^2+19/800
       +(z^2/960)*[5+(1-z)(z^2+33z+3)].
```

Every term after the square is nonnegative on `[0,1]`, and the constant
`19/800` is positive. Thus

```text
F(z) >= z*[(9/40)(z-5/6)^2+19/800] >= 0.
```

This explains the sign before any arithmetic automation: a positive quadratic
core dominates the higher Taylor terms. The last bracket is a factored error,
not data supplied by a coefficient search.

## 2. The remaining interval: the original function is increasing

The derivative of the original trigonometric function is

```text
F'(z)=(1/5)cos z+((4/5)z-3/4)sin z-1/50.
```

For `1<=z<=pi/2`, both sine and cosine are nonnegative and
`(4/5)z-3/4>=1/20`. Therefore

```text
F'(z) >= (1/20)(cos z+sin z)-1/50 >= 3/100,
```

since `cos z+sin z>=1` on the first quadrant. The first part, at z=1,
gives `F(1)>=3/100`. Integration now gives

```text
F(z) >= F(1)+(3/100)(z-1) >= (3/100)z > 0.
```

This finishes the complete original domain.

## 3. Why the split at 1 is justified

This introduces one coarse analytic split, not a mesh. It has two explicit
roles: on `[0,1]` the Taylor error has the displayed nonnegative `(1-z)`
factor; on `[1,pi/2]` the sine coefficient in F' is at least `1/20`, which
makes F' uniformly positive. The estimates agree at 1. The number 1 is not
claimed to be a special geometric configuration or the actual critical point.

There is no need to preserve the old auxiliary polynomial's enlarged domain
`[0,79/50]`. That polynomial was only an implementation device. The replacement
proves the unchanged trigonometric theorem on exactly `[0,pi/2]`.

## 4. Lean integration sketch

Within the existing theorem, define F and q locally. Use
`Real.sin_ge_sub_cube`, `Seven.cos_upper_four`, and `Seven.cos_lower_six` to
obtain `z*q(z)<=F(z)`. Prove the displayed q identity with `ring` and its
nonnegative factors with `positivity`/`mul_nonneg`.

For z>=1, derive F' with `HasDerivAt`; prove the first-quadrant bound
`1<=cos z+sin z` from the unit-circle identity and nonnegative sine/cosine.
Apply `Seven.monoOn_of_hasDeriv_nonneg` to `F(z)-3z/100` on `[1,pi/2]`.
Only the body of `inward_turn_profile` changes; no downstream statement or
contact condition is weakened.

## Validation

The Taylor-to-q expansion and the completed-square/error identity were checked
by exact symbolic arithmetic. The proof does not assume those checks as a
premise. Lean code is a handoff sketch, not an executed kernel proof.
