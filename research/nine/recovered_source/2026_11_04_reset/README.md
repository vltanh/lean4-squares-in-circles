# Source recovery before the November 4 disk reset

The user requested deletion of intermediate proof runs and a fresh start.
This archive preserves historical scripts, hand notes, solver models, and
configuration source from the removed scratch workspaces. It contains no
expanded search trees or run logs. It is source recovery, not an accepted
mathematical certificate; accepted proof packets remain unchanged under
`research/nine/computer_assisted/`.

## Inventory

- 222 explicitly scanned roots, covering every planned cleanup root.
- 22,109 original source paths mapped to 3,686 distinct byte sequences.
- 31,783,691 bytes of distinct source; 5,498,648 bytes compressed.
- Archive: `sources.tar.xz`.
- SHA-256: `157bbd24c778cef8f44e0e357ac47322bbd527aac0dbc6c751b66d5b0eb7546d`.
- No missing roots or source-read errors. Every archived content was rehashed.

The archive contains `PATHS.json`, which maps each original source path to
its content hash and byte length. Each content appears once at
`sources/<sha256>`. Restore only the scripts or notes needed for new work.

The accepted proof baseline is commit
`064e4aa0444a20b79d108b4e6bfc12de3a12b9cb`. All 8,102 tracked paths
(7,892 unique blobs) were locally present before cleanup, including the
complete D6c5, B340 and D821 packets and recovered B16a quarters.
No proof search or mathematical replay was performed for this reset.

See [the operative handoff](../../HANDOFF_A2_FIXED_CLOSURE.md) for current
accepted progress and how to start a new disposable run.
