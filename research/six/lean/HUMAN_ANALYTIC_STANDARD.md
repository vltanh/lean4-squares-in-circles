# Human-analytic acceptance standard for the n=6 proof

This file records the mathematical acceptance criterion for PR #7.
The active detailed ledger is `ANALYTIC_PROGRESS.md`; the current mathematical
companion is `ANALYTIC_DIAGONAL_PROOF.md`.

The final n=6 proof may be formalized and checked by Lean, but the mathematics
must be a human analytic proof. In particular, the proof of the unrestricted
lower bound and uniqueness may not depend on exhaustive numerical search,
interval-box certification, generated stress tables, or an external program's
success result.

## Allowed proof methods

- Exact algebraic identities and inequalities.
- Explicit geometric arguments from the original Packing, UnitSquare,
  openSquare, closedSquare, support and separation definitions.
- Symbolic differentiation with hypotheses stated and checked.
- Monotonicity, convexity/concavity and endpoint reductions proved as ordinary
  real-analysis lemmas.
- Explicit Taylor inequalities with proved remainders or sign arguments.
- Small conceptual finite case splits, written and justified mathematically.
- Local ring, norm_num, linarith and nlinarith after the mathematical reduction
  is visible. Evaluating two explicit endpoint fractions is not a box search.

## Disallowed mathematical dependencies

- Python, Arb/flint, exact-dyadic, floating-point or fixed-point certificate output.
- Interval/box subdivision searches establishing substantive inequalities.
- Large generated finite tables certified only by `by decide`.
- `ProofTools.Certificate.certify` or similar exhaustive finite-cover computation.
- `FixedData/Checks.lean`, `PairCertificateChecks.lean`, or normalization
  `Certificates/Checks.lean` as dependencies of the final theorem.
- Imported PASS flags, logs, hashes, sampled minima or numerical minimizers.
- A range assertion justified only because every machine-partition cell passed.

Such files may remain as exploratory or cross-check material, but the final
theorem dependency graph must not use them. A noncomputable logical case
choice on a real proposition is not a numerical certification procedure.

## Normalization conversion

- [x] Replace all six cardinal-facing angle refinements by the analytic
      short-transverse-axis cap obstruction (`Analytic/CardinalFrame` and
      `Normalization/CardinalWindows`). This uses the broad windows as explicit
      inputs; it does not close their construction below.
- [ ] Replace the strong-core forbidden-arc certificates by analytic marker/SAT arguments.
- [ ] Replace certificate-based five-pin covering by direct pin-inclusion arguments.
- [ ] Replace broad angular windows and forbidden central-axis certificates.
- [ ] Replace the certificate-based OWN moving-pin inequality.
- [ ] Replace the certificate-based W/D order and Appendix A stress checks.
- [ ] Reprove normalization with no mathematical certificate dependency.

## Fixed D-edge classification

- [ ] Replace the 59 default, 99 Appendix-C, 53 hard-cell and auxiliary
      fixed-row certificate eliminations by structural analytic stress lemmas.
- [ ] Prove every required row-specific support-wall reduction explicitly;
      coordinate dominance is never a cap-branch criterion.
- [ ] Replace the hard A2.3 table by conceptual edge/monotonicity arguments.
- [ ] Reprove the candidate D-edge graph and common helper domain analytically.

## Candidate graph

- [x] Replace the two A22 weight-sign checks by the shifted-sine identity.
- [x] Separate constant algebra and real support formulas from computational reification.
- [x] Replace the diagonal coefficient check by exact candidate algebra.
- [x] Prove the diagonal cap/vertex remainder analytically on its stated
      DiagonalDomain, including the true switch condition and unique zero.
      The vertex proof uses concavity and two geometric-boundary quartics;
      it does not certify a subdivision. See `Stress/DiagonalRemainder`.
- [ ] Replace the common pair-envelope outer cover and derivative checks.
- [ ] Prove the remaining pair support-wall transitions and whole-domain reductions.
- [ ] Derive the common pair lower bound from those analytic arguments.
- [ ] Reprove balanced closure using only analytic geometric and scalar premises.

## Equality and unrestricted endpoints

- [ ] Reuse support-maximizer and reconstruction arguments only after their
      scalar equality inputs come from an analytic-only chain.
- [ ] Reprove Six.lower_bound through that analytic-only chain.
- [ ] Reprove Six.uniqueness through the same chain.
- [ ] Verify the public Optimum 6 endpoint uses only the analytic chain and
      unchanged problem predicates.

## Final acceptance audit

- [ ] Neither unrestricted endpoint transitively uses a substantive certificate,
      table checker or numerical search.
- [ ] Every substantive scalar bound has a human-readable explanation on its
      whole domain, not merely a generated arithmetic proof object.
- [ ] The complete hand manuscript can be read independently of Lean and
      contains the same argument. The diagonal companion is only one component.
- [ ] All computational files have clearly separated exploratory roles.
- [ ] Compiler/kernel checking, separately from the human-analytic criterion.

Checked items here denote written analytic proof bodies, not compiler acceptance.
Compilation remains deferred at the user's request. The complete human-analytic
n=6 lower bound and uniqueness have NOT yet been delivered.
