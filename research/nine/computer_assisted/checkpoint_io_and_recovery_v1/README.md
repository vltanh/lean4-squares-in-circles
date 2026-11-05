# Atomic checkpoints and recovery of committed proof inputs

This is an execution-recovery checkpoint. It adds **zero original cells and
zero masks**. The unchanged fixed register is **222 CLOSED / 9 OPEN out of
231**, and the whole-mask ledger is **8 CLOSED / 24 OPEN out of 32**. The
7,915 positional roots and 15 roadmap IDs are unchanged. Eventual `001/00`
and `100/00` assembly retains strict-radius scope. No Lean, Lake or CI ran.

## What happened and what remains available

Numerical continuation was paused after actual disk-full checkpoint errors.
The then-readable stopped trees were inspected, and separate recovery
candidates were prepared. During the subsequent session, many of those
working files became unavailable, including recently reviewed helper and
continuation sources. The old process-session handles were also unavailable.
The subsequently discovered concurrent [source-reset checkpoint](../../recovered_source/2026_11_04_reset/README.md),
commit `d989c83b8a537b9d028350d4d6f3853fe4eebc9b`, records the removal of
intermediate runs and preserves their source. That commit is retained as this
publication's parent. No missing search record is inferred from its remembered
hash. The earlier capacity-observation receipt remains an unchanged record of
what was known before that reset provenance was found.

The accepted Git history remains available at parent commit
`064e4aa0444a20b79d108b4e6bfc12de3a12b9cb`. Its concurrent restoration of the
B16a I20/I31/I33 proofs is preserved: fourteen quarters are reproducibly
excluded, while I21/I22 remain OPEN. The fixed register still has SHA-256
`3dfaff7a880ab358930fb0ea835a1fdbe9959711f3c08ac47ee9817e7c693dde`.

The receipts in this package distinguish restored committed bytes from
unavailable later search work. They establish the following availability:

| Restored item | Fresh byte checks |
| --- | --- |
| A open checkpoint, complete A1 delta, shared-bound evidence and all-mask design publications | 284 Git files; 128,712,505 bytes; every blob identity and SHA-256 checked |
| Published A open archive | All six parts, complete archive hash and 1,431 regular archive members checked |
| Published complete A1 delta | All eight parts, complete archive hash and 859 regular archive members checked |
| Assembled A1 proof packet | 2,249 input files; 1,091,622,669 bytes; exact published input-manifest hash |
| Native shared-bound evidence aliases | 73 exact paths restored from committed source bytes, without overwriting a differing file |
| Atomic checkpoint helper and its original controls | All five source/control/hand/freeze files recovered with their original hashes; eight controls rerun successfully |
| Concurrent source-reset archive | 22,109 source-path identities and all 3,686 distinct source contents verified against the preserved archive |

The A-base release audit separately reports an unlisted file observed after
archive extraction. It was preserved. Every declared release member still
matches its hash; equality of the entire current directory to the declared
member set is expressly **not** claimed. The archive restoration receipt
records exactly the members delivered by the verified archive. An unlisted
working file is not promoted to a proof input.

These restoration checks do not repeat the original weighted arithmetic.
The existing published exact replays and physical arguments retain their
original scope. Later uncommitted frontiers are not represented as recovered.
New continuation must start from an available, exactly attached checkpoint,
and final closure still requires complete exact replay, physical review and
the full hand/table assembly.

The reset archive contains scripts, hand notes and configuration source, not
expanded search states or run logs. It permits exact recovery of the latest
driver and model source where listed, but cannot restore the later numerical
frontiers. New disposable runs belong under `research/nine/.runs/`, which the
concurrent reset commit excludes from Git. Only needed source and accepted
proof dependencies should be materialized, with explicit hash checks.

## Atomic single-file writes

The helper in `atomic_checkpoint/` preserves the established JSON encoding:
`json.dump(value, indent=2)` followed by a newline. It writes an exclusive
sibling, flushes and fsyncs its data, preserves an existing regular file's
permission mode, atomically replaces the destination, and fsyncs its directory.
New files receive mode 0644. A symlink destination is rejected.

Injected ENOSPC before serialization, within serialization and at file fsync,
plus a replacement failure, leave the previous destination bytes and inode
intact and retain the diagnostic staging file. A directory-fsync failure
after replacement explicitly reports that the new file has already been
installed. The original exception is propagated. Exact serialization,
permission preservation, new-file mode and symlink rejection are also checked.

The independent source review and root's fresh eight-control review are under
`reviews/`. The helper is a single-file operation, not a node/manifest
transaction. New immutable search drivers must rethrow `OSError` at their
outer branch boundary and retain the exit-time node/manifest hash audit.
No frozen old driver or proof record was edited by this checkpoint.
The original helper's final blank line is retained deliberately so its reviewed
source hash remains exact; the publication manifest records that one whitespace
exception.

## Reproducible byte restoration

`restore_git_packet_v1.py` reads an explicitly pinned commit and one or more
tree prefixes into a new destination. It rejects an existing destination,
nonregular Git objects, duplicate or escaping paths, and verifies each Git
blob identity and SHA-256 after writing. It does not change the checkout or
its index. `receipts/GIT_RESTORATION_RECEIPT.json` lists the precise prefixes.

`restore_frozen_archive_v1.py` requires the exact hash of an archive manifest,
checks every ordered part and the complete archive, and extracts only regular
files and ordinary directories into a new root. Links, duplicate names and
escaping paths are rejected. Its receipts list every extracted regular member.
This deliberately limited reader is suitable for the two A archives recorded
here; it does not claim to accept every historical archive representation.

The assembled A1 packet was produced by its unchanged published materializer,
using the restored A-base and A1 delta. Its recorded input-manifest hash is
`d8ca6d465aa3831e26d6d0149b8ce734a1043c51694f81a9ce9b9a4e3baaf965`.

At this checkpoint all numerical lanes remain paused while exact source and
checkpoint dependencies are recovered. Measured filesystem capacity returned
above the restart threshold, but capacity alone does not authorize use of a
missing or unattached state. The prepared D821 private-sharing and A3
historical-sharing operations were not executed. No success or reclaimed-byte
claim is made for those prepared operations.
