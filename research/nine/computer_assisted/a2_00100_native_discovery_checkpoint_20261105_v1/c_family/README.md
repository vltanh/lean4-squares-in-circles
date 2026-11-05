# Native discovery checkpoint: c_family

This is a recovery snapshot of ongoing computer-assisted searches for mask
`001/00`. It establishes no new original-cell or mask exclusion. Accepted
counts remain **222/231 original cells closed and 9 open**.

`SOURCE_RECEIPT.json` records each frozen search, original or conditional
scope, candidate exclusions, and pending alternatives. Every saved case and
shared closed face remains present. The archive includes the corresponding
drivers, adapters, source bindings, and explicit external ancestry requirements.
Large previously published ancestry archives are not duplicated. The original
archive's `README.md` supplies the detailed scope and native restoration notes.

The archive has **1129 regular files**, individually hashed in
`ARCHIVE_FILES.json`. It is stored as **142 independently encoded
base64 parts**, each below 1 MB and listed in order in `PARTS.json`. Both the
encoded and decoded part bytes have SHA-256 hashes. This text format permits
recovery through tools that cannot fetch binary blobs.

```sh
python -B -S restore_checkpoint.py
python -B -S restore_checkpoint.py --destination /new/empty-checkpoint-path
```

The first command checks all part, whole-archive, and member hashes without
extracting files. The second also extracts to a new directory. Links, duplicate
or unlisted files, and parent-directory paths are rejected.

**No mathematical replay is performed by these restore checks.** This is not
a standalone portable proof. Whole original-cell credit still requires fresh
independent rational replay, original-domain and complete-cover attachment,
fresh portable replay, archive/member audit, and a hand terminal table. No
ledger was advanced. No Lean, Lake, compilation, or CI was run.
