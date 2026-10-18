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

## Remaining dependency to eliminate

To replace `stationary_local` itself, the global proof must still prove
uniqueness of the minimized envelope's critical point at each radius,
then strict radius monotonicity of its minimum.  The argument in
`HUMAN_FAMILY_CLOSURE.md`, section 4, requires a positive Hessian
determinant at **every** envelope critical point, including positive
defect.  Positive curvature only at stationary zeros is insufficient
because it does not exclude separated feasible components.

The next gates are therefore the geometric bounds on the mixed and normal Hessian
terms at envelope critical points, and the envelope uniqueness argument.
The recursive localization import can be deleted only once those gates
are proved and connected to the existing stationary uniqueness theorem.
