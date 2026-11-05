# B16a: finite H/I cover, still OPEN

This extends the [verified 75-node cover](../a2_00100_b16a_75_native_checkpoint_20261105/README.md)
by all eight physical H/I separating alternatives on each of its 16 OPEN
terminal domains. Fresh independent rational replay accepts the complete
**203-node cover: 115 excluded terminal domains and 47 OPEN terminal domains**.
It checks 28 bound rounds, 3,299 deductions and 13,234 printed-row occurrences.
The 12 proxy unions, 13 closed slope unions and 16 eight-way physical unions
are all complete. Every inherited initial state and bound prefix is retained.

The finite attempt adds 128 children, excludes 81 and leaves 47 unresolved.
**Every one of the 16 parents still has a survivor. Zero additional inherited
regions, original cells or masks close.** The different leaf counts are
different partitions, not completion fractions. This attempt is stopped;
no numerical search is left running.

| Inherited domain | H/I children excluded | H/I children OPEN |
| --- | ---: | ---: |
| 21 | 6 | 2 |
| 24 | 6 | 2 |
| 26 | 6 | 2 |
| 28 | 6 | 2 |
| 33 | 6 | 2 |
| 34 | 4 | 4 |
| 36 | 5 | 3 |
| 38 | 3 | 5 |
| 40 | 2 | 6 |
| 42 | 3 | 5 |
| 66 | 4 | 4 |
| 68 | 6 | 2 |
| 70 | 6 | 2 |
| 72 | 6 | 2 |
| 73 | 6 | 2 |
| 74 | 6 | 2 |

`HI_FRONTIER.json` identifies every child, its original owner/axis/sign choice
and its status. These are internal proof domains, not new mandatory gate IDs.
The full original and mask registers remain **224/231 and 8/32 CLOSED**.

## Coverage and arithmetic

For two original physical squares with disjoint interiors, the separating-axis
theorem supplies a normal along one of either square's two frame axes, with
either sign. Thus the owner choices H/I, axis choices 0/1 and sign choices
−1/+1 give eight necessary alternatives. Each alternative uses the original
frames and physical support widths. Closed inequalities preserve every contact
face; the cover neither assumes an axis owner nor discards a sign.

The independent checker reconstructs each child from its exact parent, visits
all eight siblings and independently reconstructs every printed premise.
For a weighted terminal, positive rational weights combine necessary rows
to `c·z ≤ b`; certified absolute bounds give `c·z ≥ −Σ M_j |c_j|`.
The recorded positive reserve `−b−Σ M_j|c_j|` is contradictory. Interval
terminals are replayed by the unchanged independent propagation rules.
Numerical solver statuses alone are never accepted as exclusions.

This retains the same nine distinct originals, all corner/pair premises,
marked cones and links, strict weak CD and closed merged I21/I22 rectangle.
The scope is strict `q < 1105/256`. The report explicitly retains a restricted
domain and an incomplete result. It grants no equality conclusion.

## Recovery and limitations

`FRESH_EXACT_REPLAY.json` and its raw log preserve the completed arithmetic
run. `discovery.py` and `DISCOVERY.log` preserve the successful bounded
discovery source/run. `MANIFEST.json` hashes the evidence. `INPUTS.json`
maps all 476 retained native input paths to 467 distinct blobs; every source
and compressed archive member was rehashed. The 6,556,440-byte archive has
SHA256 `f34dbf2278d05692a1b0f8bba015042b693c32f8c268bfa44a3ddb5c137ebabb`.

Run `python -B -S restore_inputs.py` for a byte audit; add `--restore` to
install missing exact native paths, refusing different existing files.
One input is the discovery source under the repository's ignored `.runs/`
directory. All other inputs are under `/workspace/scratch/f9f48fcfb253`.
This is a native checkpoint, **not a standalone cold proof**. Restore the
published ancestry declared by the 45-node checkpoint before replaying:

```sh
python -B -S /workspace/scratch/f9f48fcfb253/b_work/verify_b_accepted_center_disk_tree_v1.py \
  /workspace/scratch/f9f48fcfb253/b_work/b16_hi_cover_v2_20261105/manifest.json \
  /tmp/B16_HI_FRESH_EXACT_REPLAY.json \
  --packet /workspace/scratch/f9f48fcfb253/b_work/b16a_I32_complete_H_checkpoint \
  --cap-proof-dir /workspace/scratch/f9f48fcfb253/b_work/recovery_20261105/extracted_b340/unpacked/b340_complete_original_package/accepted_repo/research/nine/computer_assisted/full_angle_common_side_row_v1
```

There was no new independent manuscript review. No Lean, Lake, compilation
or CI was run. The blocker is the remaining continuous physical geometry:
neither the phase-only H/I test nor the earlier slope refinement excludes
the surviving domains. A complete proof must still discharge them and join
the result to B16a's 14 previously proved I rectangles. The 75-node checkpoint
remains a smaller valid starting point for a different method.
