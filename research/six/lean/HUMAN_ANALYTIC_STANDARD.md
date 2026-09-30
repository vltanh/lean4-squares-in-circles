# Human-analytic acceptance standard for the n=6 proof

This file specifies the stronger mathematical standard used by the current
public n=6 source. It should be read together with `APPROACHES.md`, which
separates this route from the historical self-contained finite-classification
route.

## Criterion

The unrestricted lower bound and uniqueness may be formalized in Lean, but
their substantive mathematics must be a human-readable analytical proof.

The final endpoint path must not depend on exhaustive numerical search,
interval-box certification, generated stress tables, or an external program's
success result.

An internal Lean finite checker is not an external oracle. It is nevertheless
outside this stronger acceptance standard when it is the substantive reason a
continuous range or classification is known.

## Allowed methods

- exact algebraic identities and inequalities;
- geometry from the original `Packing`, square and separating-axis
  definitions;
- exact support inequalities;
- symbolic differentiation with stated hypotheses;
- monotonicity, convexity and concavity on whole intervals;
- exact Taylor inequalities with proved remainders/signs;
- finitely many endpoints forced by a proved whole-domain reduction;
- small conceptual case splits dictated by geometry or sign;
- local `ring`, `norm_num`, `linarith` and `nlinarith` after the
  mathematical reduction is explicit.

## Disallowed endpoint dependencies

- Python/Arb/flint or other external numerical success as a premise;
- sampled minima or numerically fitted bounds without proof;
- exhaustive angle-box subdivision as the substantive proof;
- generated fixed-row tables whose conclusion is accepted only by exhaustive
  checking;
- `Stress.ExactCover`, `ProofTools.Certificate.certify`, fixed-row checkers,
  or analogous finite-cover engines on the final theorem dependency path;
- imported logs, PASS flags or hashes as mathematical evidence.

Historical files using these techniques may remain in the repository if they
are not dependencies of the advertised analytical theorem path.

## Source-complete analytical blocks

- [x] strong-core normalization and `normalize_of_candidate`;
- [x] exact candidate constants and construction;
- [x] analytic fixed-pair envelope;
- [x] corrected diagonal remainder and unique equality case;
- [x] secondary-source selection and double-D exclusion;
- [x] low-diagonal and high-gap restrictions;
- [x] complete `MissingSouthWing` exclusion;
- [x] complete `MissingWestWing` exclusion;
- [x] final canonical OWN-S upper tail;
- [x] unconditional `Analytic.FixedPair.complete_reduction`;
- [x] retained selected-source witnesses through equality;
- [x] eight-contact coordinate rigidity;
- [x] point-set reconstruction and reflection absorption;
- [x] unrestricted lower bound using `complete_reduction` directly;
- [x] unrestricted uniqueness using `complete_reduction` directly;
- [x] removal of the finite-classification route from the public endpoint
      imports at source level;
- [x] human-readable analytical notes for the normalization, diagonal,
      cardinal-south and final south-tail arguments.

## Important proof-design points

Several places deliberately avoid shortcuts that would make the proof look
stronger than what was established:

- scalar reflection is used only after proving the reflected angle domain;
- the final OWN-S tail does not claim the first rectangular OWN scalar profile
  is positive at its exceptional corner;
- at that corner the proof derives a narrow diagonal support cone and applies a
  separate completed-square support estimate;
- endpoint checks occur only after monotonicity/concavity has reduced a whole
  interval to those endpoints.

These distinctions are part of the mathematical proof, not merely
implementation details.

## Remaining acceptance work

No substantive analytical lemma is currently listed as open.

The remaining gates are formal validation:

- [ ] compile every new analytical module;
- [ ] repair any elaboration/type errors found by the build;
- [ ] execute the axiom audit and confirm only the intended standard axioms;
- [ ] inspect the elaborated dependency path for old finite-cover/table
      declarations;
- [ ] run Comparator and independent replay;
- [ ] keep the reader-facing proof chapter synchronized with the accepted
      source.

Until those gates pass, "source-complete analytical proof" is the accurate
description; "kernel-verified analytical proof" is not yet established.
