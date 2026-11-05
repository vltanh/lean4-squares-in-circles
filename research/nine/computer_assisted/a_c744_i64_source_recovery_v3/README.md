# Recovered A-c744 source and original-wide I64 attachment

The exact seven-round A-c744 source record is preserved again, together with
its source map and an explicit proof that `y_B+y_D-2y_I <= -16/25` is necessary
on the unchanged original. The record contains 813 deductions. This is a
source-recovery checkpoint; a new weighted replay is still required before
those endpoints are installed in a new runtime.

The [physical attachment](ORIGINAL_WIDE_I64_IMPLICATION.md) uses the complete
old components 0, 1, 2 and 4, the whole-original D/G and ordering guards,
the accepted `16/25` theorem, and the original strictly weak CD equality
blocker. It does not import a selected child, an OPEN leaf, a numerical point
or a new angle restriction. A-c744 remains OPEN, and the full `001/00` and
`100/00` conclusions remain strict-radius targets.

## Preserved bytes

The deterministic archive contains 28 regular files, totaling 6,720,340 bytes
before compression. Its SHA-256 is
`2ac4146142e260d62aa8b2156e7e01962ce4f8abb69f8429171c6fa7f26ce86c`.
`I64_ARCHIVE_INVENTORY.json` pins every member's exact size and SHA-256.
The root read the entire transport helper and freshly extracted and rehashed
all 28 members into a new directory. Fifteen transport rejection controls
and a deterministic repeat build are preserved separately.

The source attachment check rehashes all 2,249 files of the existing A1
materialization, including the complete 41-node and 757-node old covers.
It checks the whole-parent guards, the unchanged five-round prefix, the two
I64 literals, 131 universal center literals, 125 height-identity cases and
12 damaged controls. It expressly does not rerun the weighted or scalar
proofs. The root independently reviewed that checker and the full physical
attachment and rehashed all 40 declared theorem files and prerequisites.

Extract into a directory that does not already exist:

```sh
python -B -S i64_transport_v1.py extract \
  i64_source_checkpoint_v3.tar.xz I64_ARCHIVE_INVENTORY.json \
  /absolute/path/to/a-new-i64-checkpoint
```

The extracted README identifies the published A-base/A1 archives and the
commands for the attachment check. These large previously published proofs
remain explicit dependencies. `RAW_CHECKPOINT.json` and
`RAW_SOURCE_BINDINGS.json` are exact readable copies of their archived
counterparts; their relative paths refer to the extracted checkpoint.

## Evidence retained separately

The earlier successful seven-round gate receipt and the 235-node consumer
snapshot became unavailable during the workspace interruption. They are not
recreated or used as cache inputs. The interrupted consumer replay is not a
mathematical failure or a completed proof. Historical source wrappers are
preserved as source only.

The original-wide implication is a mathematical attachment to complete old
proofs. The new seven-round arithmetic gate and any later endpoint-family or
consumer-cover gate must retain their own explicit source bindings and
scope. No numerical search, original closure or mask closure is claimed by
this checkpoint. No Lean, Lake or CI was run.
