# Audit of the supplied closure revision

Date: 2026-09-29. The scope below is completed. Lean compilation remains
explicitly deferred. No GitHub runner or remote computation service was used.

**Result:** the supplied arithmetic claims exercised in this audit passed
independent exact-arithmetic replays. The audit found and repaired a false-pass
checker path, a certificate-role inconsistency, missing Lean consequences and
stale development imports. It is not an exhaustive certification of every
prose inference or of archived programs absent from the upload. The complete
unrestricted n=6 Lean lower bound and uniqueness remain unfinished.

## Pinned inputs and archive integrity

- Initial live PR #7 head: `fcdb50232d341ce705b9ecf20e3b222d44e25111`.
- ZIP SHA-256: `b8dc9ad4de70b330f8d4bfadb7744cf99833d1627228652fa85556f87b5d9c3e`.
- Original patch SHA-256: `bf3ea1514f64d62dc6fffb9176e6b4a4525ec5d92d3ed9a2ec8d71046eeab6b7`.
- The standalone patch is byte-identical to the patch inside the ZIP.
- All 47 changed paths are under `research/six/`; the upload contains no Lean
  changes. Safe archive paths, every preimage/postimage Git blob prefix, and
  reverse/forward patch application were checked. All 51 supplied Python
  files parsed without syntax errors.

## Independently executed checks

| Scope | Actual result | Arithmetic boundary |
|---|---|---|
| Normalization at Q0 | 95 scalar leaves, 23 direct groups, zero unresolved; 11 unit tests and 14 sharpness controls | Unmodified supplied 96-bit exact-dyadic backend |
| Normalization at QSTAR | Same inventory and results | Same exact-dyadic backend |
| Downstream programs | 32/32 final run configurations passed | Conservative audit adapter over exact dyadics, or the scripts' existing exact rational/fixed-point arithmetic |
| Direct fixed stresses | 115/115 default rows and 99/99 Appendix-C rows passed | Exact support and stated rational margins; minimizer-location search was not run |
| Hardened direct checker | All 214 rows rerun and passed | 128-bit exact-dyadic adapter, with empty-selection and root/witness guards enabled |
| Domain inventory | 27/27 exact coverage checks passed | Includes closed boundaries, the 53-cell hard region, nine R22-d cells and the A23 upper corner |
| Force bookkeeping | 214/214 symbolic incidence balances passed | Exact coefficient-by-coefficient identities |
| Checker guards | 9/9 regression tests passed | Bad filters/options/inventories, root coverage and padded-domain witnesses |
| Hostile stress controls | 3/3 rejected as intended | Reversed normal signs and an overstated positive margin |
| New Lean algebra sanity | 10/10 rational/identity checks passed | Not Lean execution |

Each normalization run also performed four numerical identity sanity checks;
these do not replace algebraic proofs of the identities. Sharpness controls
include deliberately rejected values; rejection alone is not a sharpness proof.

The downstream replays cover the supplied R22-c source/envelope/monotonicity
chain, widened E/S strips, R22-d half-strip, Pattern-14 and Pattern-26 repairs,
pair closures, exceptional A23 rows and the 53-cell hard table, survivor
bridge/tails/faces, P17 and first-principles stress checks. The exact table-cover
checks establish coverage of the stated domains, not the separate geometric
arguments placing a packing in those domains.

Native python-flint/Arb was not executed in this audit. The adapter replaces
only interval arithmetic operations, never certificate predicates or success
flags. Finite operations round outward; nonfinite derivative intervals cannot
certify a box. Runs using `n6_a2_scalar` retain exact Fractions, Taylor bounds
and certified rational roots; `n6_a2_fixed` retains its outward fixed-point
backend. Logs identify the actual backend and source hash.

Four initial downstream runs failed because the adapter lacked dispatch or
compatibility operations. They passed after adapter repair, without changing
the supplied certificate sources. A separate 96-bit model retry missed a
1e-25 numerical sanity tolerance; the 128-bit retry passed. Initial failures
and retries are preserved, not discarded or reported as first-attempt passes.

## Findings and proof updates

### 1. An empty row selection falsely claimed certification

The original command

```sh
python check_A2_direct_stresses.py AUDIT_NONEXISTENT_ROW --nomin
```

exited zero and printed `ALL ROWS CERTIFIED` with zero rows. This is a genuine
fail-open harness defect, not a counterexample to any stress inequality.

The hardened checker rejects unmatched filters (including one bad filter mixed
with a good one), unknown options, empty inventories, duplicate keys, changed
115/99 inventories and invalid stress weights. It verifies outward root
coverage explicitly. A point used as a minimum/counterexample witness must lie
inside the exact domain, not merely the padded floating root. All 214 rows
still pass after these changes.

### 2. Appendix D contradicted the proof's certificate boundary

The narrative correctly treats `check_A2_survivor_high_s_pair.py` as a cross-check
because its internal cap test is invalid, but Appendix D called it a certificate.
The corrected index demotes it to a cross-check and attributes G27-5b, G27-6 and
G27-6a to the independently passing `check_A2_survivor_EoSo_face_cert.py`.
No theorem depends on the invalid high-s cap test.

### 3. N25+ was absent from the Lean interface

The upload needs cardinal E/N deviations below 203/1000 in the R22-d and
Pattern-28/29 reserves. The prior Lean interface exported only 2/5.
`Normalization/StrongCardinal.lean` now derives N25+ from the existing cap
support and nonnegative central coordinates. Its analytic scalar bound has
reserve 754573/12000000000. Actual cardinal hypotheses and canonical-bit
wrappers are retained; no such bound is asserted for OWN helpers.

### 4. Candidate-radius N26 needed its own proof

The repaired manuscript uses 4*cStar, whereas the existing budget used 4*c0.
`Stress/CandidateCardinal.lean` derives the sharper estimate directly from
candidate-radius containment. Its low-angle branch proves the actual cap
condition; its high-angle branch uses the universally valid far-vertex bound.
Both opposite-cardinal hypotheses remain required. Neither cStar=c0 nor an
extra property of a normalized packing is assumed.

### 5. The concluding strict-radius implication needed formal support

`Stress/StrictSupport.lean` proves strict support for every nonzero exterior
force when containment is at a strictly smaller radius, on both cap and vertex
branches. Finite incidence balance proves that a positive stress threshold
requires a nonzero noncentral force. The resulting
`System.radius_eq_of_nonnegative_defect` supplies the generic radius step of
§8 once actual separator inequalities and a nonnegative defect are proved.
It does not supply the missing concrete A2 or survivor inequalities.

### 6. Existing source was not fully reached by the development imports

At the pinned live head, `Six.lean` and `SixAxiomAudit.lean` still referred to
the old cap checkpoint despite the later normalization and candidate-radius
files existing. The imports and audit inventory now reach those modules and
the three new ones above. Goals comments, the checklist and status are being
synchronized without altering the problem statements. Kernel acceptance is
not inferred from import reachability.

## Publication and reproducibility

The targeted Lean modules, development imports, audit inventory and this audit
record are committed on PR #7. The full 47-file research revision is not
silently substituted into the live manuscripts. It is delivered separately as
`six_close_proof_audited.patch`, which incorporates the upload plus the checker
and citation corrections above. Its SHA-256 is
`f842232ec2cc12ba9afc1de890ce555619ee4206e51e1b2f263d192cf608c905`.
It applies cleanly to the reconstructed original preimages, and all 47 final
postimages were matched byte-for-byte.

The committed `closure_hardening.patch` is only the incremental two-file delta;
apply it AFTER the original uploaded patch, or use the full audited patch
instead. It has SHA-256
`279130f10adbb2054786f174160db93f65b0cbca747993cef48e4fc908d0ebfd`.

The downloadable audit bundle contains original and corrected sources, the
adapter and replay tools, actual logs including failed attempts, exact coverage
and algebra results, source/output hashes and `AUDIT_MANIFEST.json`. Historical
logs supplied by the user remain separately identified as historical records.

## Limits and remaining work

The two older JSON mirror files have internally consistent 36-cell/eight-stress
statistics, but contain no evaluator, source or root hashes. They cannot by
themselves reproduce their claimed computations and are not used as current
proof evidence. The 64 archived run configurations cited in the upload were not
independently repeated in this audit.

No new failing mathematical certificate was found among the supplied programs
and domains exercised here. That statement is narrower than asserting every
line of the manuscript is a complete proof. A2 classification and survivor
formalization, equality reconstruction, candidate reflection symmetry, and
`Six.Goals.LowerBound` / `Six.Goals.Uniqueness` remain open in Lean. Compilation
and the final kernel/axiom audit are deferred, not passed. Public Packing,
Congruent, Geometry, Challenge and optimum statements are unchanged.
