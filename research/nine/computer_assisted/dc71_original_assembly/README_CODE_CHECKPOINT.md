# Dc71 exact cover assembler: source checkpoint

This directory contains the reviewed outer assembly engine for the unchanged
original `positive-c71dc2feef1abb0b`, plus focused coverage/provenance tests and a
literal-round accounting audit. It does not declare a complete original-cell or
mask exclusion. The immutable denominators remain231 original cells and32 masks.

`verify_dc71_original_cover_v3.py` requires a complete frozen portable context,
its literal16-I/56-H index and `ASSEMBLY_MANIFEST.json`. It freshly runs the
accepted geometric and interval proofs, replays every selected exact component,
and attaches complete recursive closed slope partitions. A missing sibling is
rejected; an explicit OPEN leaf prevents original-cell credit. The accepted
sharp-row leaf evaluates the reviewed physical guard on its same freshly
reconstructed OPEN state, retaining the raw OPEN certificate unchanged.

The historical sources are retained so the independently reviewed deltas can be
inspected. V2 changes only dependency routing for absolute packet-local report
paths, retaining the manifest/hash checks. V3 adds the source-pinned sharp guard.
No numerical checker, original predicate, branch identity or denominator changed.

## Exact evidence already completed

The V2 fresh run checked the complete domain cover:13 of16 I rectangles excluded,
with I21,I22,I23 retained OPEN and14 explicit OPEN leaves. Its result is
`PASS_COMPLETE_DECLARED_COVER_WITH_EXPLICIT_OPEN_LEAVES`, with zero original or
mask credit. The report SHA-256 is
`d7c3cffb4295111384c85109c4d08384d349abca65e9f4eb357df47963685f30`.
All702 frozen inputs remained unchanged. The completed875-input V3 assembly is a
separate running task at this source checkpoint; its outcome is not presumed.

The independent literal accounting audit checks109 SHA-distinct records and249
same-domain round identities:44,199 deductions and61,675 total printed-row
occurrences, including1,462 terminal rows. Of the249 rounds,81 are retained in
cumulative continuations and168 are newly appended local rounds. No old prefix
is counted again alongside its cumulative continuation. The original whole
prefix remains a separately retained antecedent.

## Focused checks and use

The39 focused actual outer-gate tests use assembly-only fixture reports. The14
sharp-leaf tests use the pinned real exact guard evaluator and an explicitly
stubbed physical reconstruction. They test routing, closed boundaries, caller
attachment, unchanged source bytes and rejection behavior; they do not replace
physical arithmetic replay.

```bash
python -B -S exercise_dc71_cover_gates_v3.py
python -B -S exercise_dc71_sharp_leaf_v2.py --source-context /absolute/frozen/context
python -B -S verify_dc71_original_cover_v3.py --packet /absolute/frozen/packet
python -B -S audit_dc71_bound_accounting_v2.py /absolute/frozen/packet /absolute/report.json /absolute/new_accounting.json
```

The focused test commands refuse to overwrite their already frozen output
reports; run them in a fresh copy when repeating them. The source-context for
the sharp test must contain the three exact physical hand/helper inputs named
by `SHARP_PINS`. The complete replay requires every pinned component and all
immutable antecedent sources, not merely this code checkpoint.

The optional index builder selects candidates only. Its labels carry no proof
authority. It leaves unresolved I22/I23 H domains at their completed H6 OPEN
parent states until complete H subcovers are available. All frozen discovery
sources remain in the portable core. A separate final mask register is required
even after a full original-cell exclusion.

No Lean, Lake, CI or numerical optimizer runs in these exact engines.
