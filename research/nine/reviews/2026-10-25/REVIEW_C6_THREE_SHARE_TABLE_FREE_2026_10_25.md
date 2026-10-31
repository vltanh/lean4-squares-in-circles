# Independent review: table-free three-share C6 inequality

Date: October 25, 2026. Reviewer: root, independently of `c6_joint`.

**Verdict: PASS.** The complete source
`SIX_CYCLE_THREE_SHARED_MATCHING_TABLE_FREE.md` proves the same whole-angle,
all-positive-force scalar inequality as the earlier three-share theorem,
with the stronger explicit gap `sum(mu_i)/2500`. Its proof needs no
Bernstein coefficients, angular subdivisions or external sign certificate.
It removes the entire **45-coefficient three-share scalar packet** from
that theorem's proof dependency. It does not remove the separately
inherited 209-coefficient double-shared-channel prerequisite.

## 1. Original geometric scope

The actual force-value identity and both matching orientations were
checked against Sections 1--2 of
`SIX_CYCLE_THREE_SHARED_MATCHING_EXCLUSION.md`. The incoming shared mean
cancels by exact perpendicularity in the physical support work. It is
not moved to a vertex. The reflected/reversed outgoing matching retains
the original force magnitudes, circle corners, means, transmitter
positions and all three additional physical squares.

The new scalar lemma uses the same closed angle enlargement,
`pi/2<=theta_i<=3*pi/4`, with total turn `2*pi`. It introduces no
additional angle, force-ratio, transmitter-position or completion premise.
The unique physical circle corner remains essential for the identity
`R*sum |F_i|`; a radial two-corner mask is not silently substituted.

## 2. All force ratios are eliminated correctly

With positive normalized weights summing to one, the square-root chord
bound is valid on the full interval because the concave square root lies
above its secant between `s^2` and 1. The squared ratio
`(a-b)^2/(a+b)^2` lies in `[0,1]`, and all pair denominators are positive.
The exact half-angle coefficient obeys `1-s>3/40`; the displayed reserve
`569^2-2*400^2=3761` verifies the required strict comparison.

The sum of the three pair differences squared is exactly three times
the variance of the force weights. Completing the square on the full
zero-sum weight plane supplies a valid lower bound even if its formal
minimizer has a negative weight: enlarging this scalar domain only lowers
the minimum. The factors are exactly
`12*K*c_*=711/400` and `36*K*c_*=2133/400`.

## 3. The complete angle triangle and Taylor identities

After subtracting `pi/3`, the three deviations sum to zero and lie
in `[-pi/12,pi/6]`. The source's simplex argument gives
`S=sum(delta_i^2)<=pi^2/24`. Expanding the zero-sum relation verifies
`sum(delta_i^4)=S^2/2` and
`||P(delta^2)||^2=S^2/6`. The cubic polynomial with roots delta_i gives
the exact projected identity `P(delta^3)=(S/2)*delta`. Cauchy then gives
`|sum(delta_i^3)|<=S*sqrt(S/6)`.

These identities hold at the simplex vertices and along every edge;
they are not local approximations around equal angles. The elementary
bound `pi<22/7` follows from the displayed positive integral: polynomial
division gives quotient `x^6-4*x^5+5*x^4-4*x^2+4` and remainder -4 over
`1+x^2`, whose integrated identity is precisely `22/7-pi`.

The first Taylor argument has a uniform fourth derivative lower bound
`-sqrt(2)`. Each individual fourth-order remainder is therefore bounded
with the correct sign, even for negative delta. Summing the exact cubic
coefficients and retaining the negative sign of the cubic coefficient
gives the claimed `sum q_i>=3*q_eq+(19/80)*S` on the whole closed domain.

## 4. Variance estimate and controlled remainder

I independently differentiated both functions A and D at `pi/3` and
reconstructed the six coefficients `(a,b,c,d,p,q)`. The cyclic shift is
an isometry on the zero-sum plane and obeys
`z dot Cz=-||z||^2/2`, so the two circulant norm calculations are exact.
The cubic projection identity incorporates the entire cubic term into
the linear operator; it is not discarded as a small error.

The mixed squared-norm coefficient is less than `-1/40`, while the
quadratic coefficient is less than `1/300`. Since `S/2<1/4`, their
combined contribution is nonpositive. All four displayed field
identities in `Q(sqrt(3))` were reconstructed independently using pair
arithmetic, with no import of an author checker or coefficient packet.
Each stated rational reserve matched exactly.

The fourth derivative of A is negative throughout the full interval
and has absolute value at most `sqrt(2)`; that of D has absolute value
at most `K/16`. Projection has norm one. The vector bound on the entire
remainder follows from
`||delta^4||<=max|delta_i|^3*sqrt(S)` and includes both negative and
positive deviations. Hence, for S>0,

```
sqrt(V/S)<111/250+(303/500)*(11/42)+(77/1200)*(11/21)^3
         =153/250-101/1587600<153/250.
```

The reserve `3/8-(153/250)^2=57/125000>0` proves `V<(3/8)*S`.
At S=0 the three coefficients coincide, so V=0 exactly. There is no
division by zero at the equal-angle configuration.

## 5. Exact arithmetic and final physical join

An independent standard-library calculation reconstructed all six
derivative coefficients, the four circulant field identities, the
square-root bounding reserves, the sum and variance estimates and the
final constant. In particular it obtained exactly

```
B>2859/1088000,
B/(36*K*c_*)>953/1933920>1/2500.
```

The coefficient multiplying S in the final B estimate is negative, so
using the strict upper bound `S<121/294` has the direction stated in
the source. The lower bound on `q_eq` is strict. The final inequality
therefore remains strict also when all angles are equal or some force
weights are equal. Rescaling the original positive weights gives the
claimed whole-domain gap and, through the unchanged physical identity,
`R<79/40` for either three-share matching.

This is a source and physical-scope review of the new replacement. The
earlier strict-turn and double-share theorems remain accepted
dependencies; their full transitive foundational audit is not newly
claimed complete. The one-/two-share C6 completion problem, strictly
obtuse one-radial family, unrestricted nine-square theorem and original
equality classification remain open. No gate ID or coarse cell changes
because this replaces a proof of an already accepted feature exclusion.

No Lean compilation, CI, workflow dispatch, numerical sign sample or
computer-generated coefficient table is used as a proof premise.
