# PR10 source-draft handoff — 2026-10-22

## Scope and verification status

Continue the written hand proof, without optimization. This remains an uncompiled Lean source draft. No Lean/lake invocation, elaboration, CI, certificate replay, or whole-repository audit was performed in this pass. Source statements described below as drafted are not claims of kernel verification.

The last branch head independently confirmed in the retained working context was `2e2cc04efc3621ae9316662c09203d878d50b13c`. Additional A-reduction source files were submitted through the GitHub connector afterward. Readbacks ceased returning usable content in the session; their presence and the latest branch head must be checked before continuing. Do not infer that this handoff itself proves that every preceding submission succeeded.

## Completed source packages through the confirmed head

### Nonnegative selected A and E totals, BT2

The source chain beginning with `GlobalGANonnegativeTotalsData.lean` now includes the literal triangle/rectangle coefficients, twelve rational numerator certificates, whole-domain positivity, coefficient ranges, support-charge envelopes, original norm comparisons, split concavity, signed budgets, and original force-sum adapters.

The two original branches have source entry points:

- `GlobalGA.NonnegativeTotals.Source.actual_false`: nonnegative TD2 error.
- `GlobalGA.NonnegativeTotals.TD0.actual_false`: arbitrary signed TD0 error.

Their callers supply original geometric conditions and weak owners, not polynomial positivity or endpoint certificates.

### Nonnegative selected A and E totals, nonpositive TD2

The chain `GlobalGANonnegativeTotalsNegativeTD*.lean` supplies the E-dependent coefficient family, sharp secant gain, eight scalar endpoint families, nine negative-endpoint boundary certificates, the actual shifted support join, absolute negative derivative reserve, signed concentration, and original force-sum comparison.

The final entry points are:

- `GlobalGA.NonnegativeTotals.NegativeTD.Source.actual_false`.
- `GlobalGA.NonnegativeTotals.all_TD_false`.
- `GlobalGA.NonnegativeTotals.frame_all_TD_false`.

The latter two assemble TD0 and both TD2 signs under BT2. The A and E totals are selected signed sums; opposite signs inside either pair are retained.

`GlobalGANonnegativeTotalsNegativeTDSourceData.lean` was corrected at the confirmed head to use scalar `ε` instead of shadowing the candidate vertex `E`.

## Subsequent source submissions to verify

The following files were submitted after the confirmed head. Verify their actual presence before creating or replacing them:

1. `GlobalGAMixedNegativeACaps.lean`
2. `GlobalGAMixedNegativeACapSlopes.lean`
3. `GlobalGAMixedNegativeAMotion.lean`
4. `GlobalGANegativeANormalForm.lean`
5. `GlobalGANegativeABothMotion.lean`
6. `GlobalGANegativeAReduction.lean`
7. `GlobalGANegativeACycle.lean`

They transcribe `HAND_G3_MIXED_NEGATIVE_A_PRIMARY_ERRORS_REDUCE_TO_ONE.md` and its original entry lemma. The upper cap constant is **minus one half**:

`Uminus(P,r) = -1/2 + (P - (13/12) sin r) / cos r`.

`Uplus(P,r) = -1/2 + (P + (1/12) sin r) / cos r`.

The lower caps have constant plus one half and parameter `1/2 - B`. The mixed motions are exactly the written max/min constructions. The both-negative motion is the existing G5 transport on the reflected triple `(B*, A*, G*)`.

`NegativeANormalForm.Result` records either a nonnegative selected A total or one remaining negative flat-core primary with its original angle cut. `CycleResult` changes only A and retains all other points, frames, and nonincident weak inequalities. It is a transport of necessary signed data, **not a claimed new packing**. No marker theorem may be reapplied after this transport.

### Two known immediate source corrections

These were noticed while drafting and have not been confirmed corrected:

1. `GlobalGANegativeANormalForm.lean` uses `PairedE.selected`; add a direct import of `GlobalGAPairedECharge.lean` if absent. An import in a later dependent module does not repair this module's own dependency.
2. In `GlobalGAMixedNegativeAMotion.lean`, `AB_motion` contains an unused `have hlow` using `min_le_iff.not.mpr`. Remove that invalid unused derivation. The immediately following `hlow' := le_min (hL.trans hAB) hroom` is the intended bound and is the one used by the result.

The exact raw G5 transport signature and reflection lemma names in `GlobalGANegativeABothMotion.lean` also need to be reconciled with the existing source before treating this assembly as complete. No compilation has checked those applications.

## Next unfinished source work

### Single negative A, nonnegative E, positive TD2

Read and transcribe:

- `HAND_G3_NEGATIVE_A_PRIMARY_DOMINATES_SHORTER_E_TOTAL.md`
- `HAND_G3_NEGATIVE_A_PRIMARY_WITH_LONGER_E_TOTAL_EXCLUSION.md`

The first file was requested at the end of the session, but no usable readback was available; do not assume its contents were successfully read or formalized.

The nonnegative-A outcome is already handled by `NonnegativeTotals.all_TD_false`. The single-negative-A outcome with TD0, or with a nonpositive TD2 error, can use the existing `PairedE.Negative` source theorem. The positive-TD2 outcome still needs the two listed comparisons.

### Remaining global owner cases

The following are not closed merely by the new nonnegative-total package:

- Negative selected E total, including the paired negative core-E transports and the shorter/longer signed-excess cases.
- Joint negative A and core-E with positive TD2.
- Positive BT3 with arbitrary TD0: the sorted-D endpoint certificates exist, but the full two-angle envelope and physical source assembly are not thereby complete.
- Joint negative A/core-E with positive BT3 and the remaining DE3/EH1 alternatives.
- The full original high-GA owner exclusion and its original-owner case cover.

Use `HAND_G3_GLOBAL_GA_OWNER_RIGIDITY.md` as the original case ledger. Do not replace any original-owner theorem with a theorem assuming its scalar conclusion or its terminal owner.

### Final assembly after all G3 cases

Connect the original global owner theorem to the actual G4 paired transports, their retained source contacts, and the unconditional sharp source entry. Preserve the original-point equality pullback and uniqueness data. The existence of scalar endpoints, a necessary-system transport, or a terminal theorem under hard owners does not by itself close this assembly.

## Delivery discipline

Commit source increments with `[skip ci]`. Do not compile or start an optimization/audit detour. Do not report the entire formalization finished while any listed original-owner case or unconditional source connection remains open. Update this handoff against the actual branch before making further completion claims.
