# Human-analytic acceptance standard for the n=6 proof

This file records the mathematical acceptance criterion for PR #7. The single
live progress ledger is `STATUS.md`; the normalization and diagonal companions
are `ANALYTIC_NORMALIZATION_PROOF.md` and `ANALYTIC_DIAGONAL_PROOF.md`.

The final n=6 proof may be formalized and checked by Lean, but its mathematics
must be a human analytic proof. The unrestricted lower bound and uniqueness may
not depend on exhaustive numerical search, interval-box certification,
generated stress tables, or an external program's success result.

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

## Remaining acceptance work

The live detailed list is in `STATUS.md`. In summary:

- [ ] Exclude both mixed missing-wing source cases analytically.
- [ ] Prove the three remaining OWN-wing tail inequalities.
- [ ] Construct `ReductionHypotheses` for every normalized packing.
- [ ] Rewire the unrestricted lower-bound/uniqueness path to the analytic closure.
- [ ] Verify equality reconstruction and the recorded reflection on that path.
- [ ] Confirm no substantive certificate/table dependency is transitively reachable.
- [ ] Complete a human-readable final proof matching the formal argument.
- [ ] Compile and execute the final kernel/axiom audit.

Compilation is a separate validation stage. Checked source items do not by
themselves assert elaboration or kernel acceptance.
