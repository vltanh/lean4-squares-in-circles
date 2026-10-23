# Table-free source recovery and continuation — 21 October 2026

> This document preserves the recovery snapshot. For subsequent reconstructed
> results and the current task-by-task implementation status, see the
> [live table-free formalization roadmap](TABLE_FREE_FORMALIZATION_PROGRESS.md).

## Current state

The executor disconnected during proof drafting and reconnected with an older
workspace snapshot at local commit `874971c`, corresponding to published
checkpoint `bb8b49da`. Later uncommitted source files were absent. Recovery
searches did not locate a newer filesystem snapshot, and Personal Context was
unavailable. Previously published commits remain intact.

The formalization is still incomplete. The public theorem continues to use
the existing generated-capture compatibility path. None of the recovered or
new sources has been compiled, typechecked, tested, replayed, or audited.
All publication commits carry `[skip ci]`.

## Sources preserved after reconnection

The first five recovery checkpoints preserve 62 Lean files: 38 source changes
that survived in the returned workspace, followed by 24 complete retained
patches reconstructed from the agents' available source text.

| Published checkpoint | Preserved source group |
| --- | --- |
| `427729c8fcf8392aaf35aa05c59a378d225ff0c6` | Original core/high frame pair and all-axis source drafts |
| `4e7823c72c7be1340cf5974598104d8b279950e2` | Widened E-contact geometry and nonpositive outer reductions |
| `dcc9e8f4177b163bd93b00aa81c7fcf58effe5c7` | Mixed-zero short-word contact and original-owner drafts |
| `c3660092721e11ca13b00911944d37c0c5d86a99` | Eight retained second-word mixed upper-angle modules |
| `7202b20ca378698498fdcdbdb6309fe4e7d45a9a` | Sixteen retained second-word opposite outer contact modules |

Two further saved Lean sources are
`SecondMixedPositiveEarlyPolynomial.lean` and
`SecondOuterNegativeThreeStationaryAlgebra.lean`. The first proves the drafted
whole-interval polynomial inequality; its radical and geometric transfer is
not yet supplied. The second contains three retained rational estimates; it
does not assert the remaining NegativeThree contact theorem.

Detailed recovery records:

- [Second-word outer-pair record](RECOVERY_SECOND_WORD_OUTER_DRAFTS.md)
- [Hard-chain and NegativeThree record](SOURCE_RECOVERY_AFTER_EXECUTOR_RESET.md)

These records distinguish retained mathematical interfaces from available
proof bodies. References to pre-outage completed drafts do not imply that
those source files survived or that any theorem was checked.

## Reconstruction and remaining assembly

Reconstruction is proceeding from the committed hand proofs and retained
derivations, with small source batches published promptly. The first priorities
are the missing G1 pair matrix and physical frame transport, the hard-class
sharpness and original-witness recovery chain, and shared SecondWord sources
needed by the recovered opposite edge-two owner join.

Other work was still unfinished before the interruption: remaining second-word
families, global normal-anchor/owner entry, sole-E scalar-to-geometric transfer,
the complete positive-primary case matrix, and the unrestricted public theorem
and original equality bridge. Recovering the missing files alone does not
complete those arguments.

Throughout reconstruction, retain the actual common radius, original points
and weak owner witnesses, and the strict-loss ledger for rigid anchors. Do not
replace missing proofs with axioms, admitted terms, assumed endpoint results,
or generated capture. Compilation and the requested final audit remain
separate from the current drafting work.
