# Human-analytic acceptance standard for the n=6 proof

This file records the mathematical acceptance criterion for PR #7.

The final n=6 proof may be formalized and checked by Lean, but the mathematics
must be a human analytic proof. In particular, the proof of the unrestricted
lower bound and uniqueness may not depend on exhaustive numerical search,
interval-box certification, generated stress tables, or an external program's
success result.

## Allowed proof methods

- Exact algebraic identities and inequalities.
- Explicit geometric arguments from the repository's original Packing,
  UnitSquare, openSquare, closedSquare, support and separation definitions.
- Symbolic differentiation with hypotheses stated and checked.
- Monotonicity, convexity/concavity and endpoint reductions proved as ordinary
  real-analysis lemmas.
- Explicit Taylor inequalities whose remainder/sign argument is proved in Lean.
- Small conceptual finite case splits whose cases are written and justified
  mathematically.
- Local algebra tactics such as ring, norm_num, linarith and nlinarith after the
  substantive mathematical reduction is visible in the source.

## Not acceptable as a mathematical proof dependency

- Python, Arb/flint, exact-dyadic, floating-point or fixed-point certificate
  output.
- Proofs whose substantive content is an interval/box subdivision search.
- Large generated finite tables certified only by `by decide`.
- `ProofTools.Certificate.certify` or a similar exhaustive finite-cover
  computation establishing a substantive real inequality.
- `FixedData/Checks.lean`, `PairCertificateChecks.lean`, or normalization
  `Certificates/Checks.lean` as dependencies of the final theorem.
- Imported PASS flags, log files, source hashes, sampled minima or numerical
  minimizer searches.
- A theorem whose only explanation for a range is that all cells in a machine
  partition passed.

These files may remain in the repository as exploratory/audit material, but
the final theorem dependency graph must not use them.

## Current non-analytic dependencies to replace

### Normalization

- [ ] Replace `Normalization/Certificates/Checks.lean` uses in the strong-core
      forbidden arcs by explicit marker/SAT inequalities and monotonicity.
- [ ] Replace certificate-based five-pin covering by direct geometric/analytic
      pin inclusion arguments.
- [ ] Replace certificate-based angular windows and forbidden central axes by
      analytic separator estimates.
- [ ] Replace the certificate-based moving-pin inequality by an analytic proof.
- [ ] Replace the certificate-based W/D ordering check by an analytic
      four-axis argument.
- [ ] Reprove the final normalization theorem with no import of
      `ProofTools/Certificate` in its theorem dependency graph.

### Fixed D-edge classification

- [ ] Replace the 59 default, 99 Appendix-C, 53 hard-cell and auxiliary
      fixed-row certificate eliminations by a small set of analytic stress
      lemmas.
- [ ] Prove the support branch conditions explicitly; coordinate dominance is
      never a cap-branch criterion.
- [ ] Replace the hard A2.3 table by monotonicity/convexity/edge reductions and
      explicit one-variable endpoint inequalities.
- [ ] Reprove the universal candidate D-edge graph without
      `Stress/FixedData/Checks.lean`.

### Candidate graph

- [ ] Replace `Stress/PairCertificateChecks.lean` and all finite pair-envelope
      covers by analytic lower-envelope lemmas.
- [ ] Prove each support-wall transition analytically and prove the relevant
      derivatives/one-sided derivatives on the entire stated intervals.
- [ ] Derive the common pair bound from those analytic lemmas, not from a
      checked box partition.
- [ ] Prove the diagonal cap/vertex remainder analytically on both branches.
- [ ] Reprove balanced nonnegative defect and rigidity from those lemmas.

### Equality and endpoints

- [ ] Retain the geometric support-maximizer and reconstruction arguments once
      their scalar equality premises come from analytic proofs.
- [ ] Reprove `Six.lower_bound` through an analytic-only normalization and
      balanced closure chain.
- [ ] Reprove `Six.uniqueness` through the same analytic-only chain.
- [ ] Verify the public `Optimum 6` endpoint depends only on the analytic
      chain and the original problem predicates.

## Final dependency audit

Before the proof is called complete:

- [ ] Neither `Six.lower_bound` nor `Six.uniqueness` transitively depends on
      any certificate/check/table module listed above.
- [ ] Every substantive scalar inequality has a corresponding readable
      mathematical lemma explaining why it is true on the whole interval.
- [ ] The hand-proof manuscript can be read independently of Lean and contains
      the same reductions and inequalities used by Lean.
- [ ] Computational files are labelled exploratory/cross-check only.
- [ ] Compiler/kernel checking is a separate verification step; its success
      does not substitute for the human-analytic requirement.
