# n=6 Lean source-completion checklist

Updated 2026-09-29 after auditing `six_close_proof.zip` and its matching patch.
`[x]` under source development means a proof body and source dependencies are
written, NOT compilation or kernel acceptance. Arithmetic replay items state
what actually ran. Conditional lemmas do not discharge their own hypotheses.
No admission, custom axiom, native-decide axiom, external success flag or change
to Packing/Congruent may discharge an item.

## Candidate and original-packing input

- [x] Exact candidate radicals, polynomial, active-radius identities and qStar < Q0.
- [x] Candidate attainment, including the genuinely rotated diagonal square.
- [x] Unique containing square from the existing Seven exterior theorem.
- [x] Initial translation/alignment and nonnegative central coordinates by quarter-turns, without reflection.
- [x] Five exterior sorted charts, genuine Seven markers and strict separation.
- [x] Real signed-chart correspondence, cyclic marker gaps and empty-arc contradiction.

## Normalization source chain

- [x] Exact cap constants, genuine cap/corner branch and analytic tilt budget.
- [x] Actual closed/open square projections and all seven directed central SAT alternatives.
- [x] Strong central box proved before pins/sectors; source inhabitant of Goals.StrongCentralBox.
- [x] N16 and chart bounds, affine marker selection and actual side-nearest foot.
- [x] Five-pin covering and finite counting, assembled into an actual PinPacking.
- [x] Labelled angular windows and cardinal-or-OWN alternatives.
- [x] Single global D diagonal normalization, with reflection explicitly recorded.
- [x] W/D and remaining cyclic primary order using all four actual pair axes.
- [x] Cardinal cap transport, one helper per side and both moving pins.
- [x] Opposite-cardinal budgets with BOTH cardinal hypotheses at Q0.
- [x] Appendix A eight-stress source proof and D canonically OWN.
- [x] normalize_of_candidate constructs this interface from the original Packing predicate.

## Audited additions from the supplied closure revision

- [x] N25+: cardinal E/N angles below 203/1000, from analytic cap inequalities, not an added premise — Normalization/StrongCardinal.lean.
- [x] Candidate-radius central box cStar and exterior containment — Stress/CandidateRadius.lean.
- [x] Genuine two-branch support at a parameter radius — Stress/ExactSupport.lean.
- [x] N26 with 4*cStar, retaining BOTH cardinal hypotheses — Stress/CandidateCardinal.lean.
- [x] Strict support on both branches under strictly smaller-radius containment — Stress/StrictSupport.lean.
- [x] Positive stress threshold forces a nonzero noncentral force by incidence balance.
- [x] Generic radius equality from a proved nonnegative defect; concrete case closures remain required.
- [x] Import these modules through Six.lean and configure their axiom-audit commands.
- [x] Correct the stale Goals comment without changing any target proposition.

## Exact arithmetic and upload audit — executed independently

- [x] Safe archive paths, identical ZIP/standalone patch, all 47 preimages/postimages and patch application checks.
- [x] All 51 supplied Python files parsed.
- [x] Normalization at Q0: 95 scalar leaves, 23 direct groups, 11 unit tests and 14 sharpness controls; zero unresolved.
- [x] Same independent exact-dyadic normalization replay at QSTAR.
- [x] 32/32 final downstream run configurations passed; initial adapter failures and retries retained in the logs.
- [x] 115 default plus 99 Appendix-C exact-support rows; hardened checker rerun on all 214 rows.
- [x] 27 exact stated-domain coverage checks, including the 53 hard cells and A23 upper corner.
- [x] 214 symbolic force balances and normalized nonnegative stress weights.
- [x] Nine harness regression tests and three hostile stress controls.
- [x] Ten rational/polynomial sanity checks for the new Lean proof bodies.
- [x] Audit older mirror JSON statistics; identify their missing source/root/evaluator provenance.
- [x] Fix empty-filter false certification, unknown options/inventory checks, exact-root enclosure and domain-witness guards in the revised research copy.
- [x] Correct Appendix D's high-s cross-check/certificate distinction in the revised research copy.
- [x] Build and validate the full 47-file audited research integration patch; deliver it separately from the committed Lean changes.
- [ ] Independently replay the 64 archived configurations absent from the upload.
- [ ] Exhaustively certify every prose inference and geometric domain reduction; not implied by passing scalar programs or rectangle coverage.

Native Arb was NOT run in this audit. Normalization used the supplied 96-bit
exact-dyadic backend. Downstream replays used a conservative exact-dyadic adapter
or the scripts' existing rational/fixed-point arithmetic. Four identity checks
per normalization run are sanity checks, not exact identity proofs. See
UPLOAD_AUDIT.md and the downloadable AUDIT_MANIFEST.json for full provenance.

## Downstream A2 and survivors — still required in Lean

- [x] General reverse-stress summation and support/contact equality propagation.
- [x] Non-strict and strict candidate-radius support interfaces.
- [ ] Canonical finite-pattern encoding and complete directed source-axis inventory.
- [ ] A2.1 Patterns 10, 14, 26, including repaired support branches and high-s stress.
- [ ] A2.2 Patterns 12, 13: all D-edge families, R22-c, R22-d and NEG-upper.
- [ ] A2.3 Patterns 28–31: repaired non-hard rows, 53 hard cells and full tail coverage.
- [ ] Adjacent-pair source/envelope proofs with every range extension and support wall.
- [ ] Direct survivors 9, 11, 15, 24, 25, 27, without extra global reflection.
- [ ] Pattern 8 scalar inequality and exact equality propagation.
- [ ] Equality reconstruction and absorption of the candidate's actual reflection symmetry.

Passing the supplied Python certificates does not tick any of these Lean items.
The checked generic strict-radius theorem does not supply the missing defects.

## Unrestricted endpoints and acceptance

- [ ] Prove Goals.LowerBound for the original unrestricted Packing predicate.
- [ ] Prove Goals.Uniqueness with the unchanged Congruent definition.
- [ ] Integrate the public optimum endpoint and comparator.
- [ ] Audit the complete endpoint dependencies for hidden mathematical assumptions.
- [ ] Refresh the full-project source/declaration inventory after downstream completion.
- [ ] Compile and run the final kernel/axiom audit — explicitly DEFERRED.

## Audit-stage commit journal

- 4fa7b4b: pinned upload audit scope and input identities.
- 3e09626: analytic N25+ proof and canonical-cardinal wrappers.
- 2573557: strict cap/vertex support, nonzero-force and radius inference.
- 45c839b: exact candidate-radius N26 proof.
- 7794a85: incremental checker/provenance hardening patch against the uploaded revision.
- 8a4c897, bd572c4, f7be53b, f7ede37: repair stale development imports and axiom inventory.
- 76305df: correct goal status comments; all target propositions unchanged.
- f6e359e: independent audit findings, executed scope, limitations and publication boundaries.
