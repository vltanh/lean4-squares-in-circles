# n=6 Lean formalization status

Updated 2026-09-29 after the audit of `six_close_proof.zip` and its matching patch.

**The unrestricted n=6 Lean proof is not complete. Compilation and kernel
acceptance are deferred at the user's request.** Written proof bodies and
independently executed arithmetic checks are recorded separately below.

## Source implementation

The repository contains candidate algebra and attainment, the original-packing
normalization chain, the strong central box, actual pin-labelled geometry and
windows, the recorded diagonal reflection, W/D order, moving pins, cap piercing,
opposite-cardinal budgets and Appendix A's D-own exclusion.

`Normalization.StrongCore` supplies a proof body for
`Six.Goals.StrongCentralBox`. `Normalization.normalize_of_candidate` supplies
the normalization interface without seeding Packing with pins, sectors, a
small central box or an A2 conclusion. The exact candidate-radius central box
and two-branch center support are in `Stress/CandidateRadius.lean` and
`Stress/ExactSupport.lean`.

The audit added three modules:

- `Normalization/StrongCardinal.lean`: N25+ for cardinal E and N,
  |e|, |n| < 203/1000, with an analytic cap proof and canonical-bit wrappers.
- `Stress/CandidateCardinal.lean`: the sharper candidate-radius N26 bounds with
  4*cStar, retaining BOTH opposite-cardinal hypotheses.
- `Stress/StrictSupport.lean`: strict cap/vertex support for nonzero forces
  under smaller-radius containment, the required noncentral nonzero force,
  and the generic radius inference from a proved nonnegative stress defect.

The old development root and axiom-audit file still referenced the earlier cap
checkpoint at the start of this audit. They now import and list the later
normalization, candidate-radius and new audit-stage endpoints. Configuring
`#print axioms` is not execution of an axiom audit.

## What remains open

The complete directed pattern classification, the repaired A2.1/A2.2/A2.3
inequalities and survivor chains, Pattern 8's global scalar closure, equality
reconstruction and the candidate reflection-symmetry step still need their
Lean implementations. `Six.Goals.LowerBound` and `Six.Goals.Uniqueness` remain
uninhabited. The generic strict-radius theorem requires the concrete defect
inequality; it does not prove those missing case closures.

The updated task ledger is `CHECKLIST.md`. No public Packing, Congruent,
Geometry, Challenge, optimum statement, lake configuration or workflow was
changed in this audit.

## Independent arithmetic audit

See `UPLOAD_AUDIT.md` for findings and scope. Fresh internal executions gave:

- 95 scalar leaves and 23 direct normalization groups, zero unresolved, at
  each of Q0 and QSTAR; 11 unit tests and 14 sharpness controls per mode.
- 32/32 final supplied downstream configurations passed, including all 115
  default and 99 Appendix-C direct stress rows. Initial adapter failures and
  their successful retries are preserved in the execution records.
- All 214 direct rows passed again after the checker was hardened.
- 27 exact stated-domain coverage checks, 214 symbolic force balances, nine
  new guard tests, three hostile controls and ten new Lean algebra checks passed.

Normalization used the supplied standard-library 96-bit exact-dyadic backend.
Downstream programs ran with a conservative exact-dyadic audit adapter or their
existing exact-rational/fixed-point arithmetic. **Native Arb was not run.**
Numerical identity and sample-agreement checks remain sanity checks, not proofs
of exact equality. No GitHub runner or remote computation was used.

The two older JSON mirror statistics are internally consistent but lack the
source/root/evaluator hashes needed for independent reproduction. The upload's
64 archived run configurations were not independently rerun. Passing the
supplied programs is not an exhaustive audit of every manuscript inference.

## Research integration boundary

The full 47-file uploaded research revision and the audit's checker/citation
corrections are delivered as `six_close_proof_audited.patch`, separately from
the targeted Lean and audit commits. They have not been silently substituted
into the branch's live manuscripts. The committed `closure_hardening.patch`
is the incremental delta to apply after the original upload; the full audited
patch already incorporates it.

The downloadable bundle contains the revised research copy, original inputs,
actual logs, replay tools, failure/retry records and `AUDIT_MANIFEST.json`.
Earlier SOURCE_AUDIT/CAP_LOCAL_MANIFEST/compiler-failure logs in this repository
are historical records; their old file counts and hashes do not cover this
new checkpoint and must not be presented as current Lean acceptance.
