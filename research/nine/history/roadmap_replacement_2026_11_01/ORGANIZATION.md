# n=9 research — organized file map (PR #11)

**Start with the [single central progress ledger](PROGRESS.md).** It is the authoritative status index for all **58 original coarse cases, 140 currently open detailed obligations**, and the remaining unrestricted sharp-radius/equality/certificate gates. The original 2,513 fine-gate denominator is preserved. No new case is closed by reorganizing files.

## Directory layout

| Location | Role | Status policy |
|---|---|---|
| [PROGRESS.md](PROGRESS.md) | **One live ledger** for current progress, open case IDs and closure criteria | Authoritative summary; no duplicate live counters |
| [CYCLIC_CELL_LEDGER.md](CYCLIC_CELL_LEDGER.md) | Original 58 coarse-ID flags and detailed source cases | Authoritative original coarse case identifiers |
| [DEEP_GATED_ROADMAP.md](DEEP_GATED_ROADMAP.md) | Original detailed fine-gate checkboxes and subgate dependency source | Retain 2,513 original IDs and evidence |
| [gates/](gates/README.md) | Supplemental 296-record refined hierarchy with complete 140-parent mapping | Distinct scoped proof tasks, blocked audits and deferred future tasks; no new canonical fine IDs |
| [areas/](areas/README.md) | Browsable topic indexes: geometry, stress, cycles, articulations, D02 and equality | Links to the unchanged original source manuscripts |
| [reviews/](reviews/README.md) | **1,739 relocated hand-review records**, seven date directories with browsable indexes | Historical evidence, not accepted status by itself |
| [history/](history/README.md) | Handoff and adoption indexes, plus earlier progress chronology | Preserve original documents and old counts as history |
| [areas/evidence/](areas/evidence/README.md) | Index of scripts, JSON and compressed artifacts | Leave executable/checker paths unchanged; not proof premises |
| [certificates/](certificates/) | Existing structured certificate subdirectory | Retained verbatim |
| [checkpoints/](checkpoints/) | Existing saved checkpoint directories | Retained verbatim |
| [recovered_variants/](recovered_variants/) | Existing recovered manuscript variants | Retained verbatim |
| [LeanDrafts/](LeanDrafts/) | Existing uncompiled or experimental Lean drafts | Not run or checked during this reorganization |

## Why not move the whole proof library?

The research tree originally had **4,071 flat files** in `research/nine/`, of which **1,739** were dated `REVIEW_*.md` records. Moving these original review blobs into `reviews/YYYY-MM-DD/` removes the largest source of browse clutter. Original mathematical proof manuscripts, adoption files, and relative-path-dependent scripts remain at their old locations to protect thousands of cross-references, source pins, and checker imports. Use [topic indexes](areas/README.md) for browsing them without duplicating copies.

No theorem file or review source was altered as part of the review move. Search for a review by its original `REVIEW_...` filename within the dated [review index](reviews/README.md). Historical plain-text review references are preserved; newly authored links should point to the dated review location.

## Workflow for ongoing work

1. Read [PROGRESS.md](PROGRESS.md), choose an open **complete original parent** or a mathematically general extraction/completion theorem.
2. Read the detailed original caller in [CYCLIC_CELL_LEDGER.md](CYCLIC_CELL_LEDGER.md) and the exact fine gates in [DEEP_GATED_ROADMAP.md](DEEP_GATED_ROADMAP.md).
3. Put a new mathematical manuscript in the stable root proof library until the existing source-reference closure can be audited; do not create a second live progress ledger.
4. Put independent mathematical review manuscripts under `reviews/YYYY-MM-DD/`, and add an entry to that day's index. Record only actual performed reviews.
5. Tick an original flag only after a full original nine-square physical-caller proof, preserving all actual squares, degrees, means, masks and common normal selection. Then reconcile the single progress ledger.
6. Under the present contract: **hand proof only, no Lean/Lake/CI**, and no proof-by-external-script. Git maintenance operations are not mathematical proof checks.

The existing PR is a research draft. The unrestricted claim `R² >= 1105/256`, complete equality characterization and G4.2.c common-certificate integration are **not proved** by this file reorganization.
