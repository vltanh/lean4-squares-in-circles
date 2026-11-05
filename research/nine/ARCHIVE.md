# Earlier research and recovery

The complete pre-cleanup work is preserved at the immutable commit
[`6a9a45e0ad997c8e143b0f22a0de88370d9d7adb`](https://github.com/vltanh/lean4-squares-in-circles/commit/6a9a45e0ad997c8e143b0f22a0de88370d9d7adb).
It remains an ancestor of this PR. No history was rewritten.

- [Full nine-square research tree](https://github.com/vltanh/lean4-squares-in-circles/tree/6a9a45e0ad997c8e143b0f22a0de88370d9d7adb/research/nine)
- [Computational certificates and replay packages](https://github.com/vltanh/lean4-squares-in-circles/tree/6a9a45e0ad997c8e143b0f22a0de88370d9d7adb/research/nine/computer_assisted)
- [Last stopped-frontier handoff](https://github.com/vltanh/lean4-squares-in-circles/blob/6a9a45e0ad997c8e143b0f22a0de88370d9d7adb/research/nine/HANDOFF_2026_11_05_PACKUP_AND_NEXT_TASKS.md)
- [Fixed original-cell register](https://github.com/vltanh/lean4-squares-in-circles/blob/6a9a45e0ad997c8e143b0f22a0de88370d9d7adb/research/nine/gates/A2_00100_FIXED_FRONTIER.json)
- [Full-mask register](https://github.com/vltanh/lean4-squares-in-circles/blob/6a9a45e0ad997c8e143b0f22a0de88370d9d7adb/research/nine/gates/A2_MASK_FRONTIER.json)
- [Earlier stress/contact-graph ledger](https://github.com/vltanh/lean4-squares-in-circles/blob/6a9a45e0ad997c8e143b0f22a0de88370d9d7adb/research/nine/CYCLIC_CELL_LEDGER.md)
- [Earlier scripts](https://github.com/vltanh/lean4-squares-in-circles/tree/6a9a45e0ad997c8e143b0f22a0de88370d9d7adb/scripts)

Before cleanup, `research/nine` contained 9,590 tracked files totaling
3,339,454,419 bytes. The active tree retains selected mathematical sources
and a short proof draft, plan and audit. Superseded directives, handoffs,
review copies, detailed graph-case campaigns, computational archives,
search/replay programs and unused Lean drafts are available in the snapshot.
Their historical claims have not been erased or upgraded to paper proofs.

The cleanup retains 45 mathematical source documents and six navigation,
roadmap, outline and audit documents: 51 files in all. It removes 9,544 legacy
research files and 16 obsolete nine-square scripts from the current tree.
The original research README is replaced, and the retained sources are moved.
The retained mathematical text was compared with the snapshot after
normalizing link changes; local links and newly pinned archive targets were
checked. No Lean build, numerical search or certificate replay was needed
for this documentation cleanup.

Retained source arguments are moved into `sources/`. Their mathematical text
is preserved; links are adjusted for the move or pinned to archived material.
Old bare filenames that describe exploratory provenance can be located in
the snapshot. The source filenames retain their original names for lookup.

To read any old tracked file without changing the current checkout:

```sh
git show 6a9a45e0ad997c8e143b0f22a0de88370d9d7adb:research/nine/PATH
```

For a full old working tree, use a separate detached worktree at that commit.
Any byte-bound manifest or reproduction procedure belongs to that exact
snapshot, including its full transitive archive dependencies. Current-source
link edits are not claimed to preserve old manuscript hashes.

The [audit](AUDIT.md) distinguishes source review from fresh arithmetic
verification. The archived instructions to run searches or pursue particular
cells are historical; the [paper-proof plan](PROOF_PLAN.md) governs the current
task.
