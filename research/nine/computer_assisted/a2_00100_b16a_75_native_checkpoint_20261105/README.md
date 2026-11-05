# B16a: three completed inherited regions, original still OPEN

This native checkpoint extends the accepted 45-node merged I21/I22 cover of
`negative-16a2fc93c8d133f0`. The unchanged independent rational checker freshly
accepts **75 nodes, 34 excluded terminal domains and 16 OPEN terminal domains**.
It checks 28 rounds, 3,299 deductions and 11,974 printed-row occurrences. All
12 four-way proxy unions and 13 two-way closed slope unions retain their faces.

The newly completed inherited regions are **1, 5 and 13**. Region 5 has a
complete 20-node extension with 16 excluded terminal descendants. Regions 1
and 13 have direct positive rational-reserve terminals. This gives 18 new
terminal exclusions relative to the 45-node checkpoint. The continuation
below region 18 remains incomplete, and all other unresolved alternatives
remain explicit. Frontier sizes before and after subdivision are different
partitions, not comparable completion fractions.

The scope remains the same closed merged rectangle
`x_I ∈ [-163627/2097152,2457813/4194304]`, `y_I ∈ [-91/120,91/120]`,
with all nine original squares, original corner/pair premises, selected cones,
marked links and strict weak CD retained. The report explicitly rejects a
whole-original claim. The radius claim is only `q < 1105/256`.

**Zero original-cell or mask credit.** Counts remain **224/231 originals**
and **8/32 masks CLOSED**. No independent manuscript review or standalone
cold replay is claimed. No Lean, Lake, compilation or CI was run.

## Evidence and recovery

`FRESH_EXACT_REPLAY.json` and its raw log record this session's completed
independent arithmetic replay. `MANIFEST.json` binds them and the archive.
`INPUTS.json` maps all 346 retained native input paths to 337 distinct content
blobs in `inputs.tar.xz`; every source was rehashed and every compressed member
was independently read and checked. The archive is 6,248,776 bytes, SHA256
`a6089f712ff8107dd58222d43b9869cc607aa4017e9e3b9fb91a3e69a36c043c`.

Verify transport with `python -B -S restore_inputs.py`. Add `--restore` to
install missing exact native input paths; an existing different file is an
error. This is byte recovery, not arithmetic replay. The transitive published
ancestry remains required as declared by the
[45-node checkpoint](../b16_interval_terminal_continuation_v1/native_checkpoint/README.md).
The input bundle does not replace those proof archives or claim that its
source map enumerates every transitive file opened by their loaders.

After restoring that ancestry and these inputs, repeat arithmetic with:

```sh
python -B -S /workspace/scratch/f9f48fcfb253/b_work/verify_b_accepted_center_disk_tree_v1.py \
  /workspace/scratch/f9f48fcfb253/b_work/b16_broad_phase_20261105/manifest.json \
  /tmp/B16_75_FRESH_EXACT_REPLAY.json \
  --packet /workspace/scratch/f9f48fcfb253/b_work/b16a_I32_complete_H_checkpoint \
  --cap-proof-dir /workspace/scratch/f9f48fcfb253/b_work/recovery_20261105/extracted_b340/unpacked/b340_complete_original_package/accepted_repo/research/nine/computer_assisted/full_angle_common_side_row_v1
```

Discovery stopped refinement after 30 new nodes, preserving a consistent
atomic checkpoint. A separate zero-round phase pass then visited all 16
survivors and found no additional immediate exclusion. Neither numerical
status nor a saved PASS label substitutes for the independent replay.
