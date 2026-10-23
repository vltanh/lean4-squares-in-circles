# K — marker envelope from exact data at the origin

Production baseline: `1dbbd4f106e9860752e9c0c612864196167df103`.
Targets: the numerical proof of `Seven.arcEnvelope_bound` and its use in
`marker_vertical_endpoint`. This is a mathematical replacement, not compiled
Lean. No production file is changed.

## 1. The quantity and what the caller actually needs

Remove the constant pi/6 and write

```math
e(x)=\frac1{24}+\frac13\sqrt{\frac{13}4-(x+1)^2}
      +\arcsin x-\frac34x,\qquad 0\le x\le\frac34.
```

The caller needs `pi/6 + e(x) + 801/1600 < pi/2`, not the particular old
bound `e(x) <= 5443/10000`. We prove instead

```math
e(x)\le\frac{353}{648}-\frac1{16}(x-\tfrac29)^2
       \le\frac{353}{648}.
```

This slightly weaker envelope bound is sufficient for the same marker theorem.
**It is not a proof of the old internal `5443/10000` statement.** The integrator
should replace that helper's numerical conclusion and its caller together;
the original marker half-width and public results stay unchanged.

## 2. A uniform curvature bound, before polynomial expansion

Set `A=1-x^2`, `H=9-8x-4x^2`, `W=9-7x`. All are positive on the domain.
The second derivative is

```math
e''(x)=\frac1{A^{3/2}}
       \left(x-\frac{26}{3}\left(\frac{A}{H}\right)^{3/2}\right).
```

The simple ratio bound `H/A <= W` follows from

```math
WA-H=x(7x^2-5x+1)
     =x\left(7(x-\tfrac5{14})^2+\tfrac3{28}\right)\ge0.
```

To obtain a *quantitative* curvature bound, not merely concavity, maximize

```math
B(x)=9(x+\tfrac18)^2(9-7x)^3.
```

Its derivative has the sign of `123/280-x`: after discarding positive factors,
it is `18-35x-21/8`. Thus its maximum on the whole interval is at
`x=123/280`. At that point

```math
x+\tfrac18=\tfrac{79}{140}<\tfrac47,
\qquad 9-7x=\tfrac{237}{40}<6.
```

Consequently

```math
B(x)\le B(\tfrac{123}{280})
 <9(\tfrac47)^2 6^3=\frac{31104}{49}<676.
```

Both sides of the relevant square comparison are positive. Taking square
roots gives `x+1/8 < 26/(3 W^(3/2))`. The ratio bound then implies

```math
e''(x)<-\frac1{8 A^{3/2}}\le-\frac18.
```

The reason for this estimate is a comparison of two radial curvatures. The
short polynomial maximum only verifies its uniform reserve. There is no
Bernstein expansion, angle subdivision, or tabulated radical value.

## 3. Exact origin data and a tangent parabola

At the geometrically distinguished endpoint x=0, both radicals are elementary:

```math
e(0)=\frac{13}{24},\qquad
 e'(0)=1-\frac34-\frac{1}{3(3/2)}=\frac1{36}.
```

Integrate `e'' <= -1/8` twice, starting at zero:

```math
e(x)\le\frac{13}{24}+\frac{x}{36}-\frac{x^2}{16}
      =\frac{353}{648}-\frac1{16}(x-\tfrac29)^2.
```

The point 2/9 is derived by completing the tangent parabola's square; it is
not a sampled approximation to the actual maximizer. No claim that the true
maximizer is 2/9 is needed.

## 4. The unchanged marker reserve

The elementary bound `pi > 157/50` suffices, because

```math
\frac{157}{150}-\frac{353}{648}-\frac{801}{1600}
 =\frac{167}{129600}>0.
```

Therefore `pi/6 + e(x) + 801/1600 < pi/2`. Together with the unchanged
`side a u + arcsin(a-1/2) <= arcEnvelope(a-1/2)` argument, this gives the
original `marker_vertical_endpoint`.

The other two endpoint estimates in `marker_arc` remain in place. Their
constants have direct explanations: `1331/256000=(11/40)^3/4` is a cubic
arcsine remainder; the disk-support constant `2171/1200` is justified by one
squared Cauchy--Schwarz comparison. Neither is a numerical enclosure chain.

Finally `801/1600=1/2+1/1600`: its positive excess over a half-radian permits
symmetric perturbations smaller than that excess in the small-gap argument.
The existing choice `1/3200` is half the reserve, not a set of sample angles.

## 5. Integration recipe

Suggested new helper (a statement, not an existing declaration):

```lean
lemma arcEnvelopeSecond_le_neg_eighth {x : ℝ}
    (hx : 0 ≤ x ∧ x ≤ 3/4) :
    arcEnvelopeSecond x ≤ -(1/8 : ℝ) := ...
```

Reuse `arc_radicands`, the existing derivative identities, `ring` for the ratio
identity, and monotonicity on either side of the single *derived critical
point* of B. Alternatively prove the maximum by the derivative-sign theorem
in `Seven/Analysis.lean`. This is not interval certification.

Apply `Seven.curvature_tangent` to `-arcEnvelope`, with curvature 1/8 and
anchor 0. Exact origin values close by radical simplification and rational
arithmetic. State the replacement envelope bound with `353/648`, then update
only the internal call in `marker_vertical_endpoint`. The old tangent point,
all reciprocal/root brackets at 1/8, and the constants 5430/10000 and
5443/10000 are unnecessary on this route.

## Validation boundary

The ratio factorization, derivative critical point, squared comparison, tangent
parabola identity, and final rational reserve are directly checkable as written.
Lean elaboration, compilation and kernel acceptance have not been performed.
