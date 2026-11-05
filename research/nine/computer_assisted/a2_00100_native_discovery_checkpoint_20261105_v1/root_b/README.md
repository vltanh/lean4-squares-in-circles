# Native discovery checkpoint: remaining B searches

This checkpoint preserves the exact saved bytes of five partial search covers.
It does **not** establish any new original-cell or mask exclusion. The accepted
count remains **222/231 original cells closed, 9 open**, with `001/00` and its
reversal `100/00` open.

| Saved search | Nodes | Candidate excluded leaves | Explicit open leaves |
| --- | ---: | ---: | ---: |
| Whole Bf14 original | 525 | 334 | 16 |
| Bf14 conditional future node 209 | 103 | 60 | 11 |
| Whole B7c60 original | 429 | 233 | 23 |
| B7c60 conditional node 260 | 357 | 178 | 1 |
| B7c60 positive H/I vertical-difference half | 69 | 27 | 8 |

The native manifests retain every saved alternative, original ID/path, and
shared closed face. Conditional searches remain conditional. In particular,
the node-260 cover has only one of its two vertical-order cases completed;
the other case remains open. The separately saved positive-half search is
still partial and has not been grafted into the whole-original cover.

The checkpoint includes discovery drivers, independent adapters, original
input anchors, and a ten-node original ancestry prefix for node 260. It pins
external accepted ancestry rather than duplicating old archives. See
`RESTORE_BINDINGS.json` for exact original-path-to-payload bindings and the
required prior B16 archive. The archive is a native recovery checkpoint;
its absolute source paths require the recorded path bindings when restored.
It is not a standalone portable proof package.

## Restore and integrity check

Each base64 part is independently encoded, below 1 MB, and listed in order
in `PARTS.json`, with both encoded and decoded SHA-256 hashes. Keeping the
parts as text allows recovery through tools that cannot fetch binary blobs.

```sh
python -B -S restore_checkpoint.py
python -B -S restore_checkpoint.py --destination /new/empty-checkpoint-path
```

The first command validates all parts, the joined compressed archive, and
all 1,618 regular archive members without extracting files. The second also
extracts to a new directory. Symlinks, hard links, duplicate files, unlisted
files, and parent-directory paths are rejected.

**The restore check is an integrity check only.** No fresh arithmetic replay
of these entire snapshots was performed. A complete original-cell claim still
requires independent rational replay, exact original-domain and complete-cover
checks, fresh portable replay, archive/member audit, and the hand terminal
table. No ledger was advanced. No Lean, Lake, compilation, or CI was run.
