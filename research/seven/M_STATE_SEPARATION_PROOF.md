# M — state bounds from projections and constrained corner distances

Baseline: `1dbbd4f106e9860752e9c0c612864196167df103`.
Targets in `Seven/Labels.lean`: `side_selected_label_gt`,
`side_selected_a_lt`, and `axial_sum_lt`.
These are hand proofs of the original statements; proposed Lean integration
is separate. No production source is changed.

Write `X=a+1/2`, `Y=u+1/2`. Admissibility gives
`X^2+Y^2 <= 13/4`, `a>=1/2`, `0<=u<=a`.
Use only `157/50 < pi < 22/7` below.

## 1. A short support bound in the direction (2,1)

Cauchy--Schwarz gives `(2X+Y)^2 <= 5(X^2+Y^2) <= 65/4`.
But

```math
(\tfrac{121}{30})^2-\tfrac{65}{4}=\tfrac4{225}>0.
```

Since `2X+Y` is positive, it follows that

```math
2a+u<\frac{121}{30}-\frac32=\frac{38}{15}.
```

This is a geometric disk projection, not a quadratic centered at an unexplained
point. The rational 38/15 is just a convenient strict upper bound for
`sqrt(65)/2-3/2` whose square comparison is particularly short.

## 2. Side-labelled states have label greater than 9/25

Put `t=label a u` and assume that the side term is selected. Then

```math
9a-4u=2\pi+7-12t,\qquad u\ge\frac45t.
```

Eliminating a gives

```math
2a+u=\frac{4\pi+14-24t+17u}{9}
 \ge\frac{4\pi+14-(52/5)t}{9}.
```

If `t<=9/25`, the elementary lower bound on pi yields

```math
2a+u>\frac{2852}{1125}
      =\frac{38}{15}+\frac2{1125},
```

contradicting section 1. Thus `t>9/25`.

The denominator 1125 occurs only when evaluating the displayed linear
expression at the proposed cutoff. There is no polynomial coefficient list;
the contradiction is that the label half-plane lies beyond the disk's
projection in direction (2,1).

## 3. Side-labelled states have a < 9/8

Suppose instead that `a>=9/8`. The side-label equation, `t>9/25` and
`pi<22/7` imply

```math
u=\frac{9a-2\pi-7+12t}{4}
  >\frac{1623}{5600}>\frac9{32}.
```

The last comparison has difference `3/350`. But then both disk coordinates
are larger than the corresponding coordinates of the corner
`(X,Y)=(13/8,25/32)`, and

```math
(\tfrac{13}{8})^2+(\tfrac{25}{32})^2
 =\frac{13}{4}+\frac1{1024}.
```

This contradicts the disk bound. It replaces the unexplained center
`2862/10000` by a corner forced by the assumed radial bound and a simple
transverse lower bound.

## 4. Axial-labelled states have a+u < 113/80

The axial/side tie inequality is `9a+11u <= 2pi+7`. Suppose
`a+u>=113/80`. Since

```math
9(a+u)+2u<\frac{93}{7},
```

we obtain `u<321/1120<23/80`. Put `v=23/80-u>0`.
Then `a >= 113/80-u = 9/8+v` and `u=23/80-v`. The admissible value
`Y=u+1/2` is positive, and `X>=13/8+v`. Therefore

```math
X^2+Y^2\ge(\tfrac{13}{8}+v)^2+(\tfrac{63}{80}-v)^2
 =\frac{13}{4}+\frac{69}{6400}+\frac{67}{40}v+2v^2
 >\frac{13}{4}.
```

Again the contradiction is a constrained corner-distance calculation. The
point `(a,u)=(9/8,23/80)` is not guessed independently: its coordinates sum
to the proposed threshold, and the tie inequality forces the actual point
away from it in a direction that increases squared radius.

## 5. Integration and strictness

All three conclusions and hypotheses are exactly the original production
statements. A useful new helper is

```lean
-- Proposed local helper; not an existing declaration.
lemma state_projection_2_1 {a u : ℝ} (h : Admissible a u) :
    2*a+u < (38 : ℝ)/15 := ...
```

Prove its squared Cauchy--Schwarz estimate by
`(2X+Y)^2+(X-2Y)^2=5(X^2+Y^2)`. Then use `label_le_axial`, the definition
of `side`, the elementary pi bounds, and the displayed corner identities.
`ring`, `linarith`, and `nlinarith` are closing the displayed human argument;
they are not searching for the separating direction or square center.

No equality configuration is lost: these are strict exclusions of states
outside the indicated open bounds. The useful existing
`side_remainder_quadratic` identity and its callers are unchanged.

## Validation boundary

All constants above result from explicit linear elimination or expansion of
one corner-distance identity. Exact rational and symbolic cross-checks can
verify those short calculations. No external computation is a premise of the
proof, and no Lean compilation/kernel acceptance is claimed.
