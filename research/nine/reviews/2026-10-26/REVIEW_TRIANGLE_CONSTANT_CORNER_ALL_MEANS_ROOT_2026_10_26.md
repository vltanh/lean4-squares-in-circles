# Root review: one common Fermat point for every constant-corner mean

Date: October 26, 2026.

**Verdict: PASS for the entire scalar, geometric and original physical
statement in TRIANGLE_CONSTANT_CORNER_ALL_MEANS_RADIUS_TWO.md.** This is
a hand-proof audit. No Lean compilation or CI was run. Numerical
optimization is not a premise of this review or of the source theorem.

## 1. The uniform pair inequality

I checked the convention
`D^2=a^2+ab+b^2`, `E^2=2a^2+(1+sqrt(3))*a*b+b^2`.
For `a,b>=0`, not both zero, the proposed inequality is
`2D-max(E,sqrt(2)*D)>(5a+6b)/11`.

For its collapsed branch, expanding
`(124/3)D^2-(5a+6b)^2` gives exactly `(7a-4b)^2/3`.
The remaining fixed comparison is equivalent to
`1027>726*sqrt(2)` and has positive squared reserve577.
The compared quantities are positive; no reversed squaring is used.

For the original-corner branch, the case `a=0<b` is immediate.
With `t=b/a`, the first squared difference is
`H/121`, where `H=217+(303-121*sqrt(3))*t+327*t^2`.
Every coefficient is positive using `sqrt(3)<7/4`.
I reconstructed the second squared difference and its quartic:

```
22889 +(61322-64614*sqrt(3))*t
 +(201662-102366*sqrt(3))*t^2
 +(151698-96558*sqrt(3))*t^3 +89505*t^4.
```

Replacing each negative multiple of `sqrt(3)` by `7/4` gives the
displayed `Q(t)/2` lower bound on the complete half-line. The shift
`y=t-1/2` gives exactly the source's identity. Its bracket has
derivative at least144453 and endpoint value289487/2, so it is greater
than140000 for all `y>=-1/2`. The final quadratic is everywhere
positive by the stated discriminant bound. Thus the two positive
square-root steps recover the original strict unsquared inequality
for every `t>=0`, including zero. This is one analytic proof over the
entire domain, not a coefficient grid or sampled sign test.

## 2. The same point handles every independent mean

At a nonvertex Fermat point, the three outward rays have successive
angles120 degrees. Taking consecutive vectors
`a*(1,0)` and `b*(-1/2,sqrt(3)/2)`, I expanded
`f_previous+J*(f_previous-f_current)` to obtain the stated `E(a,b)`.
The other constant bit interchanges the arguments. The three linear
right sides `(5a+6b)/11` sum cyclically to the original Fermat distance
sum in either constant-bit convention.

The interpolation inequality is pointwise at that one Fermat point:
`g-delta*k-(1-delta)*o=(1-delta)*(g-o)+delta*(g-k)`.
Its second endpoint has norm `sqrt(2)*D`. Applying norm convexity
separately to each actual mean and then taking the maximum proves
the strict sum bound for the full independent cube `[0,1]^3`.
No separately minimized endpoint functional is combined with another.

## 3. Vertex and degenerate alternatives

At a vertex Fermat point, the two nonzero rays have angle at least120
degrees; hence `d^2>=p^2+p*q+q^2>=3*(p+q)^2/4`.
If one ray vanishes, these inequalities remain true. Three distinct
collinear points have their median as a Fermat vertex and angle180
degrees. These cases include every nonconstant degenerate triple.

For the constant-one bit, the first two corner maxima are at most
`sqrt(2)*q` and `sqrt(2)*p`; the remaining one is at most
`max(sqrt(2)*p+q,sqrt(2)*d)`. The opposite constant bit exchanges
`p,q`. The collapsed alternative follows strictly from
`d>(p+q)/sqrt(2)`. For the other alternative I expanded the exact
identity

```
4*(p^2+p*q+q^2)-((2*sqrt(2)-1)*p+sqrt(2)*q)^2
=2*(q-(1-sqrt(2)/2)*p)^2+(6*sqrt(2)-8)*p^2.
```

Its right side is positive whenever `p+q>0`, also at `p=0`.
Both sides before the final square root are nonnegative. This proves
the strict functional bound in every remaining case. The constant
triple has zero perimeter and is explicitly excluded from the
physical application rather than divided through by zero.

## 4. Original means, forces, closure and virial

The source uses the unchanged actual support vectors
`g_actual=g-delta*k`, with `delta=1-ell`. In the outgoing constant-one
case the support vector is `f_previous+J*F-delta*f_current`;
the incoming constant-zero case is
`f_current+J*F-delta*f_previous`. These are precisely the original
mean-preserving normal forms. A genuine contact with endpoint mean
`delta=0` keeps its genuine contact type.

At zero, the gradient of the first distance sum is `-sum(n_i)`;
the gradient of the second sum is `-sum(ell_i*u_i)`. Thus the actual
channel closure, with all original transmitters and sliders retained,
is exactly stationarity of this convex functional at zero. The exact
original virial value is `R*P`. Its common-point upper bound is
strictly below `2P`, with `P>0`, so the original physical core
necessarily has `R<2`.

The separately audited NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md applies
to these same nine unchanged physical units and gives `R>2`.
Consequently this source excludes the complete constant-corner family
with zero, one, two or three genuine shares and all actual means.
It does not assert that an isolated six-body core is impossible.

## 5. Exact certificate and gate scope

This analytic theorem replaces the two old constant-corner one-share
and two-share proofs as current dependencies, retiring exactly their
twelve rational three-by-three matrix positivity checks. The stronger
old `R<79/40` matrix proofs remain valid historical alternatives; this
source claims only the sufficient bound `R<2`.

The global radius-two measure remains a separately counted uniform
finite certificate. The present scalar/Fermat proof contributes none.
No new checklist label is introduced. No radial-load family, radial
parent, larger coarse cell, sharp unrestricted theorem, equality
classification or Lean integration is closed by this simplification.
