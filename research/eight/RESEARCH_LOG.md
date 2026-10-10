# Eight-square mathematical research log

Scope: PR #9, branch `research/eight-proof`; all work stays under `research/eight/`.
Production baseline: `35c72e0aa740b17f012584e625bd13367c9726ff`.

## Method and status

### 2026-10-10 continuation

The current user request is to proceed with a pen-and-paper proof and frequent
`[skip ci]` commits, without writing Lean. The new orientation and dependency
audit are in [PEN_AND_PAPER_ROADMAP.md](PEN_AND_PAPER_ROADMAP.md). New work aims
to replace certificate-only arguments by analytic ones and close the global
structural gap. The previous paragraph below records the earlier session's
method; it is not an instruction to substitute new interval searches for the
present pen-and-paper task.

### Earlier session method

The current instruction permits a rigorously checked computational certificate as an intermediate proof, to be made analytical later. This supersedes the initial tracker's restriction against developing such a certificate. An unverified numerical optimization or a sampled minimum is not a proof. No Lean formalization is to be started before a complete mathematical proof exists.

Record positive results, counterexamples to proposed reductions, and unsuccessful experiments separately. Do not infer global optimality from a construction, a stationary point, a local stress, or convergence of numerical runs. Keep CI skipped on research commits.

## Starting evidence

- Friedman's Squares in Circles page lists Cantrell's March 2002 eight-square construction at radius 1.97877+, without an optimality claim for eight squares: https://erich-friedman.github.io/packing/squincir/
- The publicly displayed MinMax Arena solution supplies decimal centers and half-edge vectors for an independently submitted near-matching construction: https://minmaxarena.com/en/problems/tilted-squares-in-circle/p05-n8-v2 . Those decimals are discovery data, not exact candidate equations or lower-bound evidence.
- The existing six/seven proofs are available in the production baseline. Their radius-specific normalization conclusions cannot simply be applied at the larger eight-square radius.

Current mathematical deliverable: none beyond the existing general lower bounds. First task: recover and verify the exact contact equations from the displayed candidate, then examine global reductions and certificate routes.

