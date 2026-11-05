# B recovery and accepted-center continuation checkpoint

This deterministic archive preserves exactly 185 immutable selected files:
the complete 45-node B16a I21/I22 OPEN seed, complete 37-node B7c OPEN seed,
five newly attached original-quarter proof wrappers, the local accepted-center
weighted fixture, source code, diffs, hand attachments, exact receipts, source
bindings, and independent/root reviews. It contains no live run tree, log, or
software-only callback fixture. The expanded source files were hash-checked
before, during, and after streaming compression and remain unchanged.

The B16a evidence accounts for fourteen complete original quarters and the
remaining OPEN I21/I22 pair. B7c and the local B580 center fixture remain OPEN.
The new center-enabled atomic driver has not been launched by this preparation.
No original-cell, mask, positional-root, or roadmap register is changed.

`PUBLICATION_FILE_SELECTION.json` binds every raw source/member name, size, and
SHA256. `MEMBER_MANIFEST.json` independently enumerates every logical regular
tar member and the compressed archive hash. The archive uses sorted member
names, mode0644, zero UID/GID/mtime, empty owner names, and xz preset1. It was
streamed directly: no uncompressed tar intermediate was created.

The existing published bulk ancestry is referenced, not recopied.
`REQUIRED_PUBLISHED_ANCESTRY.json` binds eight existing proof/policy archives,
the committed source recovery archive, the accepted center weighted-use packet,
and the original-definition comparison register. The selected native receipts
give the committed Git blob identities and archive/member audits. The archive
is a source-bound continuation/recovery checkpoint, not a standalone portable
proof. Reproduction of arithmetic still requires those exact accepted ancestors
and the ordinary physical/domain/coverage checks. Saved PASS labels are not
substitutes for those checks.

The independent streaming checker hashes every regular member without
extracting it and rejects missing/extra/duplicate/special members, changed
metadata, changed source selection, or changed prerequisite binding. Run:

```
python -B -S verify_b_recovery_transport_v1.py . --expected-manifest-sha256 b378e221ee25b1aa129a80284b38496f6d9a7eef97768bb65e8696e50b8b7935 --report FRESH_TRANSPORT_REPLAY.json
```

Expected manifest SHA256: `b378e221ee25b1aa129a80284b38496f6d9a7eef97768bb65e8696e50b8b7935`.

That command checks byte transport only. It does not rerun arithmetic or grant
proof credit. The separately retained fresh exact reports identify their own
scopes and observed process results. No Lean, Lake, CI, or optimization search
was run by this packaging step.
