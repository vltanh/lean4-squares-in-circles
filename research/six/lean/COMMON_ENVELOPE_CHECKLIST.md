# Common-envelope completion route

This is the active continuation of DOWNSTREAM_CHECKLIST.md, starting from
`dc5f05a5648d9e10b396d51d72e969750e4906d0`. A checked box means a Lean proof
body and its source dependencies have been written, not compiler/kernel
acceptance. Compilation remains deferred. The unrestricted theorem is still
open until the final endpoint boxes below are checked.

## Why a common envelope

After the existing exact fixed-stress D-edge classification and candidate tails,
all bit cases fit a common compact rectangle. A new balanced adjacent-pair
stress has a single weaker linear envelope on that rectangle. Combining two
such envelopes with the diagonal term can replace the remaining separate
candidate-pattern scalar chains; it does not replace or assume the existing
geometric D-edge classification.

For the N/W pair the proposed proved-source bound is

  pairValue(no,wo,u,n,w) >= pairBase + pairLine(w) + |n|/1000,
  pairLine(w) = (73/100) max(-w,0) - (13/50) max(w,0).

The E/S pair uses the same expression at (-e,-s). Every bit combination and
all four directed sources are retained. The two noncandidate pair sources
have a strict reserve even at zero angles.

## Source ledger

- [x] Candidate diagonal symmetry with unchanged orientation-preserving Congruent — Equality/Reflection.lean.
- [x] Unique disk/vertex and axial-cap maximizing centers — Equality/SupportMaximizers.lean.
- [x] All four positive balanced pair-weight choices and exact resultant identities — Stress/BalancedPair.lean.
- [x] Universally valid smooth vertex upper support and exact candidate base identities — Stress/VertexEnvelope.lean.
- [x] Symbolic differentiation with explicit regularity guards — ProofTools/Smooth.lean.
- [x] Closed-segment continuity/monotonicity from actual HasDerivAt proofs — ProofTools/SmoothCalculus.lean.
- [x] Exact radical constants, force reification, sixteen outer claims and six local sectors — Stress/PairCertificateModel.lean.
- [x] Concrete ordinary-kernel reduction bodies for sixteen outer checks and ninety-six guarded derivatives — Stress/PairCertificateChecks.lean.
- [x] Exact coverage and local lower bound across n=0, w=0 and n=w — Stress/PairLocal.lean.
- [x] Common pair lower bound and strict alternative-source bound — Stress/PairLowerBound.lean.
- [ ] Exact diagonal-force reduction and the genuine cap/vertex condition.
- [ ] Analytic global cap-branch lower bound with equality conditions.
- [ ] Vertex-branch strict certificate and its real interpretation.
- [ ] Uniform helper rectangle derived from all existing candidate-tail cases.
- [ ] Actual balanced eight-edge system for every canonical-bit case.
- [ ] Exact geometric pair/diagonal factorization and nonpositive defect.
- [ ] Global nonnegative defect and forcing of all candidate angles/sources.
- [ ] Radius equality using the existing strict-support theorem.
- [ ] Reconstruct all six centers, actual point sets and permitted congruence.
- [ ] Inhabit the unrestricted LowerBound and Uniqueness goals.
- [ ] Public optimum integration, imports and final dependency/checklist audit.
- [ ] Compile and execute the kernel/axiom audit — DEFERRED, never inferred from source or Python.

## Independently executed development checks

The existing exact 52-bit outward-dyadic arithmetic was used internally, not
GitHub or a remote runner. Current successful runs:

- Sixteen outer pair covers: 85,910 examined nodes in total; all passed.
- Ninety-six local smooth partial derivatives: all positive on the whole ray
  square [0,1/128]^2, with weakest enclosed derivative above 0.0487.
- Diagonal vertex branch: 56,833 nodes, 28,417 terminal leaves, maximum depth 24;
  all passed. Boxes certified outside the vertex premise are explicitly skipped.

These mirror results motivate and check the mathematical predicates. They are
not imported as Lean success assumptions. Earlier exploratory diagonal covers
that did not finish are not counted as passes. The cap branch will instead use
the explicit analytic estimate in the source.

## Commits in this route

- c02e521: candidate reflection and orientation-case absorption.
- 62269a1: unique active-support maximizers.
- ddd6ced: balanced pair definitions and weights.
- b2bb303: smooth support upper bound and exact candidate base.
- ba3868c: derivative soundness, including all regularity premises.
- 4d63d66: closed-segment calculus and coordinate monotonicity.
- e8b3774: exact real interpretation of pair expressions.
- 7e88419: concrete outer/derivative arithmetic proof bodies.
- e7f42fe: six-sector local proof, with boundaries included.
- 12502cc: common global pair bound for all sources and bits.
