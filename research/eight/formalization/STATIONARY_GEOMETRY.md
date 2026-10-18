# Geometric stationary closure: formalization checkpoints

## Status and exact scope

These sources are uncompiled drafts.  Lean compilation, CI, and the large
certificate computations have deliberately not been run.  The new arguments
contain no `sorry`, new axiom, admitted analytic gate, interval subdivision,
or recursive root search.  Their elementary polynomial identities and the
rational margins have also been checked independently with exact rational
arithmetic; that check does not validate Lean elaboration.

The broad stationary root checker has **not** yet been removed.  The current
integration still calls `Generated.stationary_localization` in
`Stationary.stationary_local`.  Its import has been moved out of `Analysis`
and into `Stationary`, where that dependence is actually used.

## 1. Whole-domain fixed-tilt convexity

`ExactFamily/CircleConvexity.lean` works with the actual nested radicals

```
r = sqrt(q-u^2),             U = sqrt(q-(2-u)^2),
V = 3-U,                    Y = sqrt(q-V^2),
v = 2-Y,                    w = sqrt(q-v^2),
k1 = 2-c*(r-1)+s*u,         k2 = 1+c*v-s*(w-1),
F = k1^2+k2^2-q.
```

The domain consists of `u>=0` and the four nonnegative radicands.  For
`q<4`, the circle chord inequality, applied successively through this
chain, proves convexity of the domain and the component inequalities at
every weighted pair of domain points.  The first component inequality is
strict for distinct positions.  Both components are positive when
`0<c<=1` and `0<=s<=1`, so squaring and adding proves
`strictConvexOn_defect` on the **entire** radical domain, including its
endpoints.  `existsUnique_minimizer` adds compactness and an explicit
symmetric trial chain.

The bridge `Stationary.familyValue_geometric` identifies the existing
scalar `familyValue q (-u,z)` with these radicals for every `q,u,z`.
`Stationary.familyValue_position_strictConvex` consequently exposes this
whole-domain result for the scalar function used by the existing proof.

## 2. Whole-domain angular curvature

`ExactFamily/TiltCurvature.lean` proves the exact circle-energy identity

```
F_tt + 4*F > 91/45.
```

The proof uses the two top circles to derive `u+v>4/3`, bounds the lower
circle arcs by `r<2-u^2/4` and `w<2-v^2/4`, and finishes with explicit
squares.  `actual_tilt_curvature` differentiates the actual trigonometric
composition, so its conclusion is not conditional on an assumed second
derivative formula.  In particular `F_tt>0` wherever `F<=0`.

This estimate alone does not settle the curvature of the minimized
envelope: its mixed derivative must still be controlled.

## 3. Stationary-position localization without a root search

`ExactFamily/PositionLocalization.lean` proves that, throughout

```
(79/40)^2 <= q <= 9789/2500,
0 < c,  0 <= s,  c^2+s^2=1,  0 <= s/c <= 1/5,
```

every derivative-zero position on the full domain satisfies `u>87/100`.

There is a single comparison position, `u0=87/100`.  Successive square
comparisons give rational bounds for the actual radicals at `u0`, then
five coefficient bounds give the complete-angle estimate

```
F_u(q,u0,t)/(2*c^2) <= -81/20000 < 0.
```

More explicitly, with `x=u0/r`, `y=v/w`, `p=(2-u0)*V/(U*Y)`, `h=s/c`,
and `L=1/c`, the left side is

```
L*Lc-Qc + h*(L*Ls+J) + h^2*Qs,
Lc=2*x-p,                    Ls=2-p*y,
Qc=(r-1)*x+p*v,              Qs=u0+p*(w-1)*y,
J=u0*x-(r-1)-p*v*y+p*(w-1).
```

The five sufficient bounds are

```
Lc <= 5/16,  Ls <= 9/5,  Qc >= 61/80,
J <= 3/20,   Qs <= 17/16,
```

with `0<=h<=1/5` and `0<L<=51/50`.  No angle subdivision is involved.
Strict convexity and its two-point secant inequalities then exclude every
stationary position at or to the left of `u0`; differentiability is only
needed at the two compared points.  `position_deriv` supplies the actual
nested-radical derivative formula.

`stationary_coordinate_lower` instantiates this theorem for the existing
`Coordinates.IsStationary` predicate.  The integration
`Stationary.stationary_geometric_position_bounds` gives
`87/100 < -d.y < 1`; its upper bound uses the existing admissibility
predicate.  `stationary_local` now uses this genuine geometric bound for
its broad position guard before the remaining root checker.

`stationary_global_minimum` also proves that any derivative-zero position
is the global minimum on the entire domain.  This theorem requires only
the actual derivative at that position, not differentiability at all
radical endpoints.

## 4. A norm bound that includes positive envelope defect

`ExactFamily/EnvelopeNorm.lean` supplies the unconditional norm gate at
every position minimum.  At the single trial position `u=15/16`, successive
circle comparisons give, for every `q>=(79/40)^2` with `q<4`,

```
r > 1.738,   v < .546,   w > 1.898.
```

Writing `h=s/c`, the two positive components are consequently bounded by
`2+c*(-.738+(15/16)*h)` and `1+c*(.546-.898*h)`.  The circle equation for
`c,s` gives `1-h^2/2<=c<=1`.  Expanding the sum of squares therefore bounds
it by the explicit cubic

```
E(h)=5+2*(1-h^2/2)*(-.93+.977*h)
          +(.738-(15/16)*h)^2+(.546-.898*h)^2.
```

On the whole interval `0<=h<=1/5`, the difference between its endpoint
chord and `E(h)` factors as

```
h*(1/5-h)*(C-.977*(h+1/5)),
C=.93+(15/16)^2+.898^2.
```

All factors are nonnegative, and the two exact endpoint values are
`E(0)=3.982760` and `E(1/5)=3.99748321`, both below four.  Global position
minimality transfers that norm bound from the trial to every position
critical point.  `position_stationary_norm_lt_four` does not assume
`F<=0`; `Stationary.familyValue_position_stationary_norm_lt_four` is its
bridge to the existing scalar function.

## 5. The actual critical-chain mixed and normal Hessian bounds

`ExactFamily/CriticalStrip.lean` supplies circle support inequalities on
the complete closed strip `87/100<=u<=1`, at the same radii.  In addition
to the radical signs, its main bounds are

```
p > 3/2-u,               u*(1+p) > 141/100,
w-1-(6/7)*u > 3/70,
Z > (13/10)*(1+p),       q/r^3 < 4/5,
Z=q/((2-u)*U^2)+p*q/(Y*V^2).
```

The first bound follows directly from the rational circle supports
`U<1.128+.58*u`, `Y<1+u/2`.  With `t=1-u`, its remaining numerator is
`.011+.172*t+t^2*(2.159-.29*t)>0`.  This replaces integration of a bound
on `v''`.  The left-circle support follows from `U>.9+.8*u`, then
`v<1.52-u`, and one further square comparison.  There is no subdivision
of the position or radius intervals.

`ExactFamily/CriticalHessian.lean` defines `StripCritical` using only
that strip, the unit sine/cosine conditions, the small tilt, and the two
actual stationary equations `F_u=F_t=0`.  It **does not** assume `F=0`,
`F<=0`, a norm bound, or a Hessian sign.  It derives the norm bound from
section 4 and proves all six constants from `HUMAN_FAMILY_CLOSURE.md`:

```
kappa > 7/5,             0 < tau < 7/8,
nu > 9/100,              A0/k1 > 17/50,
kappa*sigma > 3,         sigma > 27/16.
```

Here `k_t=kappa*k_u`, `A0=|k_u|^2`, and `sigma`, `tau`, `nu` are the
position, mixed, and angular normal terms divided by `k1`.  The mixed
term uses the exact cancellation `tau=(1-(u/r)*(v/w))/(c+s*v/w)`.
The normal term uses the circle norm bound and the cone
`k1/2<k2<(7/6)*k1`.  In particular the proof retains `|k|^2` in its
angular normal term; replacing it by `q` would be invalid at positive
defect.

The last scalar comparison is explicit:

```
sigma*kappa^2-2*tau*kappa+nu > 46/25,
det(Hess F)/(4*k1^2)
  > (17/50)*(46/25)+(27/16)*(9/100)-(7/8)^2
  = 237/20000 > 0.
```

`StripCritical.hessian_reserve` proves the equivalent strict margin
`det(Hess F)>(237/5000)*k1^2`.

`ExactFamily/CriticalDifferentiation.lean` differentiates the nested
radicals, proves `p'=-p*Z`, and identifies the displayed position and
mixed Hessian entries with derivatives of the actual gradient formulas.
`actual_critical_hessian` packages those derivative identities together
with the positive position entry and determinant.  Its bridge
`stationary_isStripCritical` uses only the broad stationary predicate;
`Stationary.stationary_geometric_hessian_positive` exposes the conclusion
before local-box membership or root localization.

## 6. A fixed interior window for every position minimum

`ExactFamily/EnvelopePosition.lean` constructs the minimizing position on
one fixed compact window

```
87/100 <= u <= 11/10.
```

Throughout the complete radius strip this window has strictly positive
radicals; in particular `r>1.64`, `U>1.619`, `Y>1.411`, and `w>1.885`.
At the left endpoint section 3 gives the negative position derivative.
At the right endpoint the actual circle comparisons give

```
r < 1.65,  v < .47,  w > 1.91,  0 < p < .42,
u/r > 2/3,  0 < v/w < 1/4.
```

Consequently, with `a=s+c*u/r` and `b=p*(c+s*v/w)`,

```
k1 >= 1.35,  a > (2/3)*c,
k2 <= 1.47,  b <= .441*c,
F_u/2 = k1*a-k2*b > .25173*c > c/4 > 0.
```

Continuity of the actual derivative and the intermediate value theorem
therefore supply an interior root for every allowed tilt.  Full-domain
strict convexity makes it the unique global position minimum, including
comparison with all radical endpoints.  `windowMinimizer_geometric`
identifies the compactly chosen minimizer with that root and proves its
actual zero derivative and global minimum property.  Thus no implicit
assumption about radical-endpoint smoothness remains.

`positionEnvelope` is the infimum over this fixed window.  Its equality
with the value at `windowMinimizer` is proved directly by compactness, and
`positionEnvelope_continuous` follows from joint continuity of the actual
formula and compactness of the fixed parameter window.

The derivative interface in `CriticalDifferentiation.lean` now applies to
`SmoothDomain`, which records the full radical domain, `q<4`, and four
positive radicals.  In particular it covers the whole minimizing window,
not only `u<=1`.  `SmoothDomain.positionSecond_pos` proves

```
F_uu = 2*(a^2+b^2+k1*c*q/r^3
                  +k2*(p*Z*(c+s*v/w)+s*q*p^2/w^3)) > 0
```

at every such smooth position for unit tilts with `c>0`, `s>=0`.
All normal terms are positive because they are the curvatures of the
actual circles.  The new `positionHalf_deriv` theorem supplies the actual
derivative `F_uu/2` of the position-root equation.

## 7. Every envelope critical position is below one

`ExactFamily/EnvelopeCriticalPosition.lean` excludes the entire remaining
window `[1,11/10]` without any hypothesis on the sign of `F`.  Successive
circle comparisons give

```
1 < r < 1.71,  w > 1.9,  v > 0,  0 < p < .525,
p*r < .89775 < w-1.
```

Write `d=s*(r-1)+c*u` and `e=c*(w-1)+s*v`, so the position and tilt
stationary equations are `k1*a=k2*b` and `k1*d=k2*e`.  Their tangent cross
product has the exact expansion

```
b*d-a*e
 = c^2*(u/r)*(p*r-w+1)
   +c*s*(p*(r-1)-(w-1)+u*v*(p/w-1/r))
   +s^2*(v/w)*(p*(r-1)-w).
```

Each coefficient is negative on this whole interval.  Since `c>0` and
`s>=0`, the cross product is strictly negative, whereas the two stationary
equations force it to vanish.  This is the contradiction proving
`window_critical_below_one`.

`windowMinimizer_isStripCritical` combines that result with the interior
window theorem and supplies the actual `StripCritical` input for section
5 whenever the tilt derivative at the position minimum vanishes.  Thus the
positive determinant is available at **every** envelope critical point,
including critical points of positive defect.

## 8. Strict radius decrease by circle inclusion

`ExactFamily/RadiusMonotonicity.lean` proves a finite comparison on the
entire radical domain.  If `q0<q1<4`, increasing the radius gives

```
Domain(q0) subset Domain(q1),
r(q0,u) < r(q1,u),
v(q1,u) < v(q0,u),
w(q0,u) < w(q1,u).
```

Both positive corner components therefore strictly decrease for every
allowed nonnegative tilt, so

```
F(q1,u,t) < F(q0,u,t)-(q1-q0).
```

`EnvelopePosition.positionEnvelope_radius_decrease` transfers this
comparison to the actual position envelope by evaluating the larger-radius
minimum at the smaller-radius minimizing position.  It needs no derivative
of the minimizer with respect to radius.  The finite comparison also proves
`radius_eq_of_zero_global_minima`: once global angular minimality is
available, two zero minima cannot occur at different radii.

## 9. The actual envelope derivative and global critical-point argument

`ExactFamily/ImplicitEnvelope.lean` packages the scalar implicit-function
theorem from the pinned Mathlib revision. Joint smoothness of the actual
position-gradient equation and its nonzero position derivative produce a
local root. Uniqueness in the open position window identifies that root
with the previously chosen minimizer. The proof does not assume that the
chosen minimizer is continuous. Differentiating the equation gives
`u'(t)=-F_ut/F_uu`; differentiating the objective and its actual tilt
partial gives `M'(t)=F_t` and `M''(t)=F_tt-F_ut^2/F_uu`.

`ExactFamily/EnvelopeDifferentiation.lean` supplies every hypothesis from
the actual nested radicals. It proves joint smoothness of `F`, `F_u`, and
`F_t`, differentiates both mixed partials directly, and instantiates the
implicit theorem using the geometric window and strict convexity. Its
`positionEnvelope_second_derivative` is a derivative of the defined
`positionEnvelope`, rather than a relation between independent formal
symbols. At a critical tilt, `windowMinimizer_isStripCritical` supplies the
positive-defect Hessian estimate from section 5. The Schur complement is
therefore positive at every critical point on `0<t<atan(1/5)`.

`ExactFamily/EnvelopeUniqueness.lean` proves the remaining real-variable
argument. A positive second derivative at a critical point gives a strict
local minimum. Two strict minima would force an interior local maximum
between them; that maximum is another critical point and cannot be a
strict minimum. The same argument proves that each interior critical point
is the global minimum on the full closed interval, including comparison
with both endpoints. It does not require a connected nonpositive sublevel
set or derivative signs at the endpoints.

The resulting actual-family theorems are
`positionEnvelope_critical_strictMinimum`,
`positionEnvelope_critical_unique`, and
`positionEnvelope_critical_global_minimum`. None uses the root cover or
assumes the sign of the defect.

## 10. Original stationary-coordinate uniqueness and root-cover removal

`ExactFamily/GeometricStationary.lean` completes the adapter for the
original `Coordinates.IsStationary` predicate.  It sets

```
t = 2*atan(d.z),
cos(t) = d.c,  sin(t) = d.s,
0 < t < atan(1/5),
u(t) = -d.y.
```

The exact half-angle identities prove the frame equalities.  The original
strict tilt bound places `t` inside the envelope interval, and the actual
position derivative and full-domain strict convexity identify the selected
position minimizer with `-d.y`.  Consequently the algebraic defect and tilt
stationarity equations give `M(d.q,t)=0` and `M_t(d.q,t)=0` for the actual
envelope.  Section 9 then proves `M(d.q,v)>=0` at every other tilt in the
full closed interval.

If two stationary chains had `q0<q1`, the strict finite radius comparison
at the smaller-radius chain's tilt would give

```
0 <= M(q1,t0) < M(q0,t0)-(q1-q0) = -(q1-q0) < 0.
```

This contradiction identifies their radii.  Critical-point uniqueness
identifies their angles; injectivity of `atan` identifies their half-angle
parameters.  Equality of the unique position minima identifies their
heights, and the four positive/negative radical branches identify every
remaining coordinate.  `stationary_chain_unique` therefore proves global
uniqueness directly from the two original broad stationary predicates.
It assumes no local-box membership or independently postulated minimum
property.

`Stationary.stationary_unique` now applies that geometric theorem to the
analytically constructed `sharpData` witness.  `Stationary.stationary_local`
follows afterward by equality with that witness and its existing local-box
membership.  Its recursive root-checker call and the import of
`Generated.StationaryLocalization` have both been removed from the active
stationary proof path.  The existing local analytic existence construction
and rational brackets are retained.

## Scope and validation status

The stationary root subdivision is no longer needed to prove uniqueness
or localize a broad stationary chain.  The proof chain now runs through
actual disk convexity, circle curvature and support estimates, a fixed
interior minimizing window, the scalar implicit-function theorem, the
global critical-point argument, and finite radius inclusion.

The separate 256-box adaptive derivative, reserve, and perturbation bounds
are still present.  Their enclosure utility currently shares a module
with the old recursive checker; using the enclosure utility does not
reintroduce the stationary localization certificate.  Those adaptive
bounds remain a distinct target for further geometric reduction.

All new Lean sources in this note remain uncompiled, in accordance with
the explicit no-compilation and no-CI instruction.  Verification so far
consists of source review, pinned-Mathlib API reads, small exact rational
identity checks, and static dependency checks.  No claim of kernel
acceptance is made.
