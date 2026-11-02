# Independent audit of the central-right cone endpoint height reduction

November 2, 2026 UTC. Reviewer: `recover_low_floor` agent. This is an
independent geometry and evaluator review, not an arithmetic acceptance
of an unfinished finite cover. No Lean, Lake, or CI was run.

Reviewed manuscript: `CENTRAL_RIGHT_CONE_ENDPOINT_HIGH_SHOULDER_HAND_TABLE.md`,
Sections 1–5, and the independently written Fraction evaluator in
`verify_230_middle_low_right.py`. The finite table and replay were still
pending when this review was performed.

**Finding: no gap found in the complete physical reduction or in its
translation to the independent scalar evaluator.**

The reviewed hypotheses retain the original actual cone four-chain,
original cone triple, all independent frames, physical disjointness,
closed Q corner containment, and the coupled whole floor
`yP-hP >= 509/4960`. No extra projection edge or separator owner is used.

1. The endpoint rectangle argument includes horizontal, vertical, inward,
   outward, and downward original side normals. The positive-ratio ordering
   follows from `(a-b)(1/2+(Z-A)(a+b)) >= 0`; its uniform lower reserve
   is exactly `201/640`. The aligned endpoint is covered by the vertical
   alternative.
2. The four listed corner offsets are exactly those of side directions
   `(a,s*b)` and `(-s*b,a)`. Horizontal reflection changes the left frame
   sign, so its cap is correctly evaluated at `(Z,-sL)`. The full root
   makes all corner radicands positive.
3. Under `|V|<=D`, each negative-horizontal owned normal is dominated by
   one of the four positive-horizontal owner normals, with the same
   relative-square support. The comparison includes zero side components
   and diagonal frames; it uses no weak-link hypothesis.
4. The shared middle frame is retained across both physical pair tests.
   Taking independent maxima only over the two outer chirality choices is
   an outward relaxation. Signed vertical-gap intervals include both
   center orders and every cone equality. Their nonempty-interval and
   corner-height tests are necessary in every original configuration.
5. The Fraction evaluator reconstructs the relative support through the
   unnormalized dot product `1+s_i*s_j*t_i*t_j` and determinant
   `s_j*t_j-s_i*t_i`; this agrees with the normalized manuscript expression.
   Each projection uses the correct endpoint for its fixed vertical sign.
   The clipped physical ranges for b,h,k remain outward enclosures.
   Every leaf is recomputed with exact Fraction arithmetic and outward
   integer square-root bounds; recorded floating or derivative values are
   not accepted as proof evidence.

For a standalone statement, the common upper routing can be made explicit.
It also follows from the positive P floor: `yP>3/5`, while the lower routed
alternative would place an inner main more than `3/4` above P, contradicting
its universal upper bound `139/120`. Thus the reflected common-routing
bounds used in Section 1 do not change the sign of the stated floor.

**Acceptance boundary.** This review approves the geometry and independent
scalar formulas only. The whole conditional theorem still requires a
complete cover with an empty frontier and an independent exact replay of
all direct interval leaves. It makes no new mask-count claim.

## Reviewed direct-cover refinement

The final evaluator revision replaces natural frame enclosures with their
exact endpoint extrema on `[0,1]`: a and k decrease, while b and h increase.
Their derivatives have the asserted signs, including the h derivative
vanishing at t=1, so the four resulting endpoint intervals still cover the
whole folded frame. I inspected the implemented lower/upper endpoint
selection and found it correct.

The revision also takes the maximum of the computed relative support
lower bound and one. This is valid because both original units contain
centered disks of radius one half; equivalently
`|cos(delta)|+|sin(delta)|>=1`. It remains an outward lower enclosure and
may safely strengthen every owner-axis rejection. The producer now writes
direct interval leaves only. These two revisions introduce no new
geometric hypothesis and do not alter the independent review finding.

## Final support enclosure and accepted arithmetic

The last checker revision evaluates the same physical support in two
algebraically identical forms: the normalized components in the manuscript
and the slope numerator divided by `sqrt(1+ti^2)*sqrt(1+tj^2)`. I inspected
both expressions. Each separately encloses the same true value; therefore
the maximum of their lower bounds and one is a valid lower bound. The
interval maximum used in the implementation also remains an enclosure,
because both upper endpoints are at least the same true support.

The parent reports the complete independent Fraction replay PASS on
14,069 nodes / 7,035 leaves, depth25, and rejection of four damaged controls.
Certificate SHA256:
`2a170b17eea5b2325941f293ad4f4e3b71b50645728d6a2e7b1350a23ed56320`.
Together with this independently reviewed physical reduction and evaluator,
that closes the named central-right-endpoint height theorem. The separate
whole-occupancy caller remains the parent's assembly responsibility.
