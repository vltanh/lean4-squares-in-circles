# Human-analytic acceptance standard for the n=6 proof

This file records the mathematical acceptance criterion for PR #7. The active
ledger is `ANALYTIC_PROGRESS.md`; the current companions are
`ANALYTIC_NORMALIZATION_PROOF.md` and `ANALYTIC_DIAGONAL_PROOF.md`.

The final n=6 proof may be formalized and checked by Lean, but the mathematics
must be a human analytic proof. The unrestricted lower bound and uniqueness
may not depend on exhaustive numerical search, interval-box certification,
generated stress tables or an external program's success result.

## Allowed proof methods

- Exact algebraic identities and inequalities.
- Explicit geometry from the original Packing, UnitSquare, openSquare,
  closedSquare, support and separation definitions.
- Symbolic differentiation with the required hypotheses stated and proved.
- Monotonicity, convexity/concavity and whole-domain endpoint reductions.
- Explicit Taylor inequalities with proved remainders or sign arguments.
- Small conceptual finite cases justified by the geometry.
- Local ring, norm_num, linarith and nlinarith after a visible mathematical
  reduction. Evaluating the vertices of a geometrically forced concavity
  reduction is not an interval subdivision search.

## Disallowed mathematical dependencies

- Python, Arb/flint, exact-dyadic, floating-point or fixed-point certificate output.
- Interval/box subdivision searches establishing substantive inequalities.
- Large generated finite tables certified only by `by decide`.
- `ProofTools.Certificate.certify` or another exhaustive finite-cover engine.
- FixedData/Checks, PairCertificateChecks or normalization Certificates/Checks
  on the mathematical dependency path of the final theorem.
- Imported PASS flags, logs, hashes, sampled minima or numerical minimizers.
- A range statement justified only by machine-partition cells passing.

Exploratory or old certificate files may remain in the repository, but the
final theorem may not use them. A logical choice on a real proposition or a
small finite index equality is not a numerical inequality certificate.

## Normalization conversion — source complete

- [x] Strong-core forbidden arcs from genuine markers and actual SAT, before pins/sectors.
- [x] Five-pin covering from direct geometry, including the universal sixty-degree completed-square argument.
- [x] Broad labelled windows from analytic profiles and uniqueness of the assigned pin.
- [x] Forbidden central axes from pin coordinates and the strong-core transverse bound.
- [x] Analytic OWN moving-pin polynomial and cardinal cap-piercing cases.
- [x] W/D order from all four actual pair axes.
- [x] Six cardinal-facing refinements from the short-transverse-axis obstruction.
- [x] Appendix A: two analytic secondary-source arguments with one multiplier triple, after primary/reversed axes are excluded geometrically.
- [x] D canonically OWN, with both core-exclusion inputs supplied to Appendix A.
- [x] Normalization constructor and reflection transport use the analytic lemmas; old covering/window/Appendix A checks are removed from this path.
- [x] `AnalyticNormalization.lean` exports normalize_of_candidate, N25+ and candidate-radius cardinal refinements independently of downstream certificates.
- [x] Human-readable companion and explicitly scoped static dependency review.

This is a source-completion statement, not Lean compiler or kernel acceptance.
The static review concerns the recorded Six-module imports and changed call
sites; it is not a fresh formal audit of the pre-existing Common/Seven/Mathlib
libraries. See `NORMALIZATION_DEPENDENCIES.md`.

## Fixed D-edge classification — still open

- [ ] Replace the 59 default, 99 Appendix-C, 53 hard-cell and auxiliary
  fixed-row eliminations by structural analytic arguments.
- [ ] Justify all required support-wall reductions; coordinate dominance never
  suffices to select the cap branch.
- [ ] Replace the hard A2.3 table and candidate tails/bridges.
- [ ] Derive the candidate D-edge graph and tighter common helper domain analytically.

## Candidate graph

- [x] Both A22 weight-sign checks replaced by the shifted-sine identity.
- [x] Constant algebra and real support formulas separated from reification.
- [x] Diagonal coefficient bound from exact candidate algebra.
- [x] Diagonal cap/vertex remainder on its stated domain, with the genuine
  switch and unique zero, from concavity and geometric boundary quartics.
- [ ] Replace the common pair-envelope outer cover and derivative checks.
- [ ] Prove the pair support-wall transitions and whole-domain reductions.
- [ ] Derive the common pair bound and balanced closure through those arguments.

## Equality and unrestricted endpoints

- [ ] Reuse support rigidity and reconstruction only after their scalar inputs
  and geometric domain reduction come from the analytic-only chain.
- [ ] Reconnect Six.lower_bound and Six.uniqueness through that chain.
- [ ] Verify the public Optimum 6 endpoint and unchanged problem predicates.

## Final acceptance audit — separate from normalization source closure

- [ ] Neither unrestricted endpoint transitively uses a substantive certificate,
  generated-table check or numerical search.
- [ ] Every remaining substantive inequality has a human-readable whole-domain proof.
- [ ] The complete hand proof contains the same final analytic argument.
- [ ] Old computational material has a clearly separated exploratory role.
- [ ] Compile and check the final kernel/axiom dependencies.

Compilation remains deferred at the user's request. The complete unrestricted
human-analytic n=6 theorem is still unfinished outside normalization. The
acceptance criterion has not been weakened to mark normalization complete.
