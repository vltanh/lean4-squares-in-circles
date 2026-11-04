# A c744: complete component 1, portable consequence checkpoint

The complete component 1 of `positive-c744bc031d40ee64` is excluded by a
fresh isolated exact replay. Its necessary consequence on the unchanged
original is `y_D - y_B <= 3/5`. The actual component 3 consumer freshly
replays the complete source before using that inequality.

The whole original remains OPEN because component 3 is unfinished. This
checkpoint adds **zero original cells and zero masks**. The fixed ledgers
remain **221/231 original cells** and **8/32 masks** closed. It preserves
all nine original squares, 36 corners, 36 physical pairs, five center cones
and the exact marked conditions. No Lean, Lake or CI was run.

## Complete proof and scope

| Independently replayed item | Result |
| --- | --- |
| Complete component 1 cover | 757 nodes; 566 excluded leaves; zero OPEN leaves |
| Component 1 arithmetic | 230 rounds; 74,846 deductions; 134,855 premise rows |
| Actual component 3 source record | Seven rounds; 565 deductions; 1,436 premise rows |
| New A1 consequence in that record | Two weighted occurrences |
| Literal/scope controls | Four valid cases; 17 damaged cases rejected |
| Portable input inventory | 2,249 files; 1,091,622,669 bytes |

Component 1 is the closed alternative `y_B - y_D <= -3/5`. Its complete
exclusion implies `y_D - y_B < 3/5`, and therefore the transported weak
closed inequality. Keeping the excluded equality face is a valid weakening.
Only the original-variable row is transported. The older source checker
cannot consume that row, so there is no circular dependency. Together with
the distinct component 3 condition `y_B + y_D - 2*y_I <= -3/5`, it gives
`y_D <= y_I` within component 3. That conditional order is not asserted on
the whole original or another component.

The physical proof and closed-negation derivation are directly available
under `physical_proof/`. `TRANSPORT_AND_REPLAY.md` records the full source
and replay protocol. `fresh_replay_v2/PORTABLE_RECEIPT.json` binds the fresh
arithmetic reports. Root independently checks the compressed archive,
every shipped member and the report bindings; that byte audit is separate
from the recorded fresh arithmetic replay.

## Reconstruct the exact portable packet

This is a thin archive. It requires the previously published sibling
`a2_00100_a_c744_portable_open_checkpoint`, whose archive SHA-256 is
`e7ddb4f4e5b943a6f69a0aa861f6721ca49835311fa595ef40a10881b62e4343`.
The base bytes are reused without modification. `ARCHIVE_MANIFEST.json`
pins every ordered part and the complete new archive.

1. Join each package's parts in its own manifest order and verify the
   complete SHA-256. Extract both archives into a fresh directory.
2. Use the extracted base's `packet` directory as `--a-base`. The new
   extracted root is `complete_a1_consequence_delta_v2`.
3. With Python 3.12, materialize outside `/workspace` and run the replay
   into a separate fresh output directory:

```sh
python3.12 -B -S complete_a1_consequence_delta_v2/materialize_a1_checkpoint.py \
  --delta complete_a1_consequence_delta_v2 \
  --a-base a_c744_portable_open_checkpoint/packet \
  --output /tmp/a1_packet

python3.12 -B -S /tmp/a1_packet/replay_portable_a1_checkpoint_v2.py \
  --packet /tmp/a1_packet --output /tmp/a1_replay
```

The new archive has 859 regular members and 63,425,472 compressed bytes;
its SHA-256 is
`8378b765edebbba407e394ed98743193a556255687f7ddb8480bafe31d5710f2`.
It contains 846 new mathematical payload files and reuses 1,392 exact
base-member aliases. The materializer verifies every source hash and
rejects missing members or conflicting aliases. The small outer
`delta_v2/` directory holds provenance metadata, not the complete payload;
extract the archive before materializing.

Every arithmetic child forbids numerical imports, old-workspace reads,
unlisted packet reads and all input mutations. All inputs are rehashed at
completion. The v1 diagnostic-write rejection and its logs are preserved;
v2 changes only one explicitly disjoint output route. Every mathematical
payload hash is unchanged between those transport versions.

The frozen reference register is explicitly historical commit `ec6b94c`.
The publication register retains the later B340 independent review and
the same 231 original definitions and statuses. No whole-mask or closed-Q
promotion follows from this component checkpoint. The eventual `001/00`
whole-mask assembly retains its established strict-radius scope.
