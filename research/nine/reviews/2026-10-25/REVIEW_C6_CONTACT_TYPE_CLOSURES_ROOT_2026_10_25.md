# Root review of the new whole C6 contact-type exclusions

Date: October 25, 2026 (America/Chicago).

**Verdict: accepted at the exact scopes stated below.** This review
independently checks the saved manuscripts, their physical hypotheses,
their full continuous domains, their analytic identities, and their
joins to the original force and contact equations. It does not close
the entire all-unique/shared C6 gate, any larger coarse cell, equality,
or the earlier prerequisite audit. No Lean compilation or CI was run.

## 1. One complete mixed one-share placement

Reviewed source:
`SIX_CYCLE_MIXED_ONE_SHARE_MIDDLE_EXCLUSION.md`.

The physical strict-turn and side-mean sources give exactly the
reduction used in this manuscript. With corner bits 110 and the only
share at loaded unit 1, that share is outgoing and has its actual
chord `ell_1(-J n_1)`, including `ell_1=1`. The other two loaded
units really are nonshared; their actual application chords have
length one. No singleton formula is applied to the shared unit.

I checked both nonshared support-vector formulas directly in the
incoming-normal frame. Their complete angular ranges imply the two
vertical estimates in (8), including the zero first coordinate at
the upper turn endpoint. The shared vertical contribution is at most
`1/sqrt(2)` because its actual chord length is at most one and its
turn is at most 135 degrees. Summing gives exactly

```
sin(theta_1)+1/sqrt(2)-(1+sqrt(2))sin(theta_0)<0.
```

The strict sign follows from the already proved actual
`theta_1>pi/2`; no discarded shared endpoint supplies strictness.
It contradicts the vertical component of the original channel
closure. The reflection/reversal carries the actual share along and
does not identify the other two mixed placements. Thus this one full
contact type is excluded, while the constant-bit one-share type and
the two other mixed placements retain their own obligations.

## 2. The complete constant-bit two-share orbit

Reviewed source:
`SIX_CYCLE_CONSTANT_CHI_TWO_SHARE_EXCLUSION.md`.

I independently checked the original force and support equations,
the genuine shared chord formulas, the vector expansion for the
nonshared unit, and the exact horizontal closure. Its angular
consequence (13) follows from the true actual side direction; it
does not follow merely from the virial identity. The optional
force-ratio factorization (15) also agrees by direct expansion using
`c^2+d^2=1`. The positive denominator and the upper-turn endpoint
are handled explicitly.

The convexity calculation in Section 3 proves the single triangular
enlargement of the whole angle domain. I checked the sine-Taylor
endpoint, its rational reserve, the radical comparison, and the
direction of the decreasing cosine-minus-sine implication. No
original angle is removed by that enlargement.

The homogeneous force reduction has the correct direction throughout.
The square-root chord lower bound and the normalized adjacent-force
sum give (23). The numerator norm majorant retains the mixed product
of the two actual forces and gives (24)--(25). Expanding the resulting
quadratic verifies each diagonal and off-diagonal in (27).

Both Taylor bounds in (28) follow from uniform second-derivative
bounds on the full closed angle interval, on either side of the
expansion point. Every entry of the force matrix is increasing in
the half-angle sine variables and decreasing in the `h` variables.
The resulting entrywise lower bound is used only on the positive
force vector; it is not incorrectly treated as a matrix inequality
on arbitrary signed vectors.

I independently rebuilt all six controls from (30)--(32) with a new
standard-library rational-interval calculation, using no values from
the author's scratch reconstruction. All 54 entry comparisons and
all six exact minimum reserve fractions agree with the manuscript.
I also independently reproduced both Machin-series endpoint reserves,
the four radical squared reserves, and the sine-Taylor reserve.
All six integer matrix-vector products in Section 6.3 agree exactly.
The weighted-square identity (38) proves the stated uniform
`21/5000` lower bound without an eigenvalue or determinant assumption.

The barycentric expansion (33) is the direct quadratic identity, with
nonnegative coefficients summing to one. The resulting normalized
gap is strictly greater than `7/5000`. Removing the force
normalization multiplies this gap by the original positive force
sum. The actual virial identity therefore contradicts `R>=79/40`.
The full constant-bit symmetry cover, all genuine shared endpoints,
all positive force ratios and all three extras remain included.

This proof has six explicitly displayed rational matrix checks. It
does not rely on an external coefficient packet and is not described
as having no finite positivity calculation.

## 3. Both force orderings of the mixed 0/2 two-share orbit

Reviewed sources:

* `SIX_CYCLE_MIXED_02_SMALL_FORCE_BRANCH_ANALYTIC.md`;
* `SIX_CYCLE_MIXED_02_LARGE_FORCE_BRANCH_ANALYTIC.md`.

The second source is root-authored and has separate independent
saved-source review in
`REVIEW_C6_MIXED_02_LARGE_FORCE_AND_JOIN_2026_10_26.md`. The first
has a separate independent review in
`REVIEW_C6_MIXED_02_SMALL_FORCE_BRANCH_2026_10_26.md`. This section
records root's additional complete physical and analytic join review.

The exact nonshared norm is `L^2=2+p^2+2p h_1`; the constant term
is 2. I checked both closure identities from the actual side vectors,
including `q>1` and the retained shared-mean endpoints. The small
branch's `q>=p` comparison is in the correct direction and gives
`c_1<=1/3`, then `p<1/7`, with every intermediate denominator
positive. Its Cauchy step eliminates every positive value of `q` by
a pointwise lower bound, without installing an optimized value in
the packing.

I rederived the derivative factorizations (14) and (22), the identity
`T^2-(B')^2=2(K-1)B-3-4s_1`, and the endpoint direction for each
of the three monotonicity reductions. The bounds on `C,T,B'` and
the concave cotangent comparison have the stated signs. The force
and angular derivative margins are `1/56` and `-1/56`, respectively.
The final radical corner gives the displayed positive normalized
reserve `11891/2835000`. These statements cover all original forces
in the full first ordering.

In the complementary ordering the actual physical unique corner of
unit 1 gives `p<27/10`; this is precisely the nonshared bit-one
local theorem in the complete-domain source. The two uniform scalar
gaps follow from monotonicity of the actual side direction in `p`,
the norm bound `L<=p+sqrt(2)`, and one Cauchy inequality. The fixed
rational lower reserves in (16) are strictly positive. The two
closure products and the exact angular sum bound then give
`(p-1)^2/p>8 epsilon`, incompatible with the displayed force range.
The endpoint `t_2=0` is contradicted by a strictly positive right
side before any division by `t_2` is used.

Finally `q>=p` and `q<p` are an exhaustive partition of the original
positive force ratios, including `q=p` in the first branch. They
share the same physical bit pattern, original shared interfaces,
normal convention and force normalization. Thus their reviewed join
excludes the entire mixed 110, shares 0/2 orbit. No force is deleted,
no physical square is replaced, and all three extra squares remain.

## 4. Exact bookkeeping boundary

The complete-domain source gives three two-share contact orbits.
The present accepted sources close the constant-bit orbit and the
mixed 0/2 orbit. The mixed 0/1 orbit requires a separate full proof
before the two-share family can be declared excluded. The one-share
theorem in Section 1 removes one full mixed placement only.

There is no pre-existing original gate for one of these smaller
contact-type improvements. No new gate is created and no original
checkbox is changed by this review. The larger all-unique/shared
completion gate and its central/exterior obligations remain open.
