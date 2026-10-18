# Independent audit: all same-sign OO zero-quarter pairs of0011011

**PASS.** I independently reviewed the full continuous proof in
`proof_integration/WRONG_0011011_SAME_OUTER_ZERO_HAND_PROOF.md`, inspected
its exact arithmetic companion, replayed all133 strict comparisons, and
reconstructed the coefficient bindings and key scalar comparisons without
using the companion's interval class or derivative functions.

The proof covers all16 declared retained-axis cases. The physical gap
premise `delta>.76` is used explicitly to limit a negative same-sign
frame increment to `phi>-.026`; all four separators are then infeasible.
For positive increments, the three direct-axis reductions have the correct
coordinate monotonicity, angle barriers and strict cost reserves.

I rederived the three displayed label derivative formulas. In particular,
`P''''>0` has numerator `(5v-.5)Q-2v²`, and the stated coarse comparison
is valid. The `L'` lower bound follows from global `L'''>2` and a single
quadratic completion; its upper bound follows from convexity and the two
endpoint values. All four labels are strictly increasing, as required
when moving a pair to its contact surface.

For the remaining source-secondary contact I checked the coordinate
identity, both positive contact speeds, `v²=q-z²`, and the formula for
`k/v`. The exact feasible contact boundary consists only of `B=0`,
`b=d`, and `phi=.7`. The impossible edges `B=d,b=0,phi=0` are excluded
before any minimum argument is made.

For `L,K`, the implication `C_phi<=0 => C_B>0` is valid on the whole
contact domain. The two target-coordinate ranges cover all possible
states, the positive denominators have the correct directions, and the
source-diagonal and upper-angle boundary arguments use feasible improving
directions. They force a minimum onto `B=0`. The ensuing strong-convexity
bound and increasing continuation have a reference point in their stated
physical interval.

For `P,J`, I rederived the change to `(b,B)` coordinates, the stationary
curve formula, and `q'=-2E/p³`. The bounds forcing `b>.6`, positivity and
decrease of `E`, and the decreasing target coordinate therefore describe
every possible interior critical point; they do not presume an optimizer's
list of critical points. Differentiating the contact ratio gives exactly
the displayed formula for `phi_BB`. Its coefficient bounds have the
correct signs even if the second bracket is negative. The two fixed
source intervals cover the full critical range and make the Hessian
determinant negative. Consequently an interior local minimum is impossible.

The three remaining `P,J` boundaries are all covered. I checked the
target-zero monotonicity, the explicit source-diagonal parameterization
and its two derivatives, and the upper-angle second derivative. All six
fixed diagonal-curvature rows yield the displayed common lower bound.
The one-point quadratic completions use valid physical reference points
and apply to connected boundary intervals.

The labels `P,J,L,K` match the exact integer role table, including the
reflection/reversal convention that supplies the other two same-sign
rows. No sign, ownership or endpoint case is missing. I found no required
correction.

Reproducible additional checks and SHA256 bindings are in
`audit_wrong_0011011_two_outer_components.py` and
`wrong_0011011_two_outer_components_independent_arithmetic.json`.
That independent script checks28 exact comparisons across this review
and the companion positive/negative quarter-row review; it binds both
133- and17-comparison replays to their source files.
