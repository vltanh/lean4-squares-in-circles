# Human-analytic acceptance standard for the n=6 proof

This is the active mathematical acceptance criterion for PR #7, following the
request to work towards a completely analytical hand proof. The single live
progress ledger is `STATUS.md`. The normalization, diagonal, and new
cardinal-south companions are `ANALYTIC_NORMALIZATION_PROOF.md`,
`ANALYTIC_DIAGONAL_PROOF.md`, and `ANALYTIC_CARDINAL_SOUTH_PROOF.md`.

The final n=6 proof may be formalized and checked by Lean, but its mathematics
must be a human analytic proof. The unrestricted lower bound and uniqueness may
not depend on exhaustive numerical search, interval-box certification,
generated stress tables, or an external program's success result.

The previous distinction remains important: an internal Lean finite checker is
not an external Python oracle, but it is still insufficient for this stronger
hand-proof target. The current public endpoint's remaining internal finite
classification must therefore be replaced, not relabelled as analytic.

## Allowed proof methods

- Exact algebraic identities and inequalities.
- Explicit geometry from the original `Packing`, `UnitSquare`,
  `openSquare`, `closedSquare`, support, and separation definitions.
- Symbolic differentiation with all hypotheses stated and proved.
- Monotonicity, convexity/concavity, and whole-domain endpoint reductions.
- Explicit Taylor inequalities with proved remainders or sign arguments.
- Small conceptual finite case splits justified by the geometry.
- Local `ring`, `norm_num`, `linarith`, and `nlinarith` after a visible
  mathematical reduction.
- Evaluation of finitely many geometrically forced endpoints.

## Disallowed mathematical dependencies

- Python, Arb/flint, floating/fixed-point, or exact-dyadic certificate output.
- Interval/box subdivision searches establishing substantive inequalities.
- Large generated finite tables whose mathematical content is only `by decide`.
- `ProofTools.Certificate.certify` or another exhaustive finite-cover engine.
- `FixedData/Checks`, `PairCertificateChecks`, or normalization
  `Certificates/Checks` on the final theorem's mathematical dependency path.
- Imported PASS flags, logs, hashes, sampled minima, or numerical minimizers.
- A range claim justified only because all cells of a machine partition passed.

Historical computational files may remain as exploratory or cross-check
material, but the final theorem may not depend on them. Small logical finite
case splits are not numerical certification.

## Source-complete analytic blocks

- [x] Strong-core and complete normalization through
      `Normalization.normalize_of_candidate`.
- [x] Analytic Appendix A and D-own.
- [x] Candidate constants and exact support formulas separated from reification.
- [x] Fixed-pair envelope on its explicit bit-dependent domain.
- [x] Corrected diagonal remainder, nonnegativity, and unique zero.
- [x] Low-diagonal exclusion and `d > 1/2`.
- [x] W/D primary/reverse-secondary classification.
- [x] Full-range forward-secondary D/S selection.
- [x] Double-D-secondary exclusion.
- [x] Conditional candidate/radius closure from explicit `ReductionHypotheses`.
- [x] Lower OWN-S tail and the stronger canonical sign `s>0`.
- [x] OWN-W outer tail derived from the two candidate D separators.
- [x] Both-cardinal wing branch.
- [x] D-sourced west gap greater than one and its consequence `d>3/5`.
- [x] Retained separator witnesses, eight-contact equality reconstruction,
      point-set congruence and absorption of the recorded reflection.
- [x] Unrestricted endpoints routed through the analytic pair/equality closure,
      with the remaining finite classification explicit in `Classification.Reduction`.
- [x] Sharper shared-center OWN/OWN budget `s-w<24/25`.
- [x] Entire cardinal-W missing-south branch, including large OWN-S, excluded
      by the four-edge weights `4,10,3,3` and six geometric endpoint inequalities.
- [x] In a two-OWN missing-west case, the strict reserve `d-s>1/25`.

## Remaining acceptance work

Exactly three independent analytic statements still supply the final reduction:

- [ ] Exclude `MissingWestWing` with at least one OWN wing and `d>3/5`.
      Cardinal W forces OWN S; two OWN wings additionally satisfy
      `s-w<24/25` and `d-s>1/25`.
- [ ] Exclude `MissingSouthWing` with W OWN. The cardinal-W exception is closed.
- [ ] Prove the canonical OWN-S upper tail `s<=11/25`.

The lower OWN-S tail and the OWN-W outer tail are not additional independent
open items. Once the three statements above are available:

- [ ] Replace the imports/body of `Classification.Reduction` using
      `reduction_iff_three_obligations`, without changing the public goals.
- [ ] Confirm no substantive certificate/table dependency is transitively reachable.
- [ ] Complete a human-readable final proof matching the entire formal argument.
- [ ] Compile and execute the final kernel/axiom audit and independent validation.

Compilation is a separate validation stage. Checked source items do not by
themselves assert elaboration or kernel acceptance. The new four-edge hand
argument and its source lemmas have not yet been checked by Lean.
