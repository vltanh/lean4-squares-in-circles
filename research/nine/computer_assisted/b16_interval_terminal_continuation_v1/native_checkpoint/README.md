# B16: fourteen exact interval terminals in the retained regional cover

This checkpoint independently excludes fourteen formerly OPEN leaves of the
retained B16 45-node tree. The completed full exact replay now reports
**16 excluded leaves and 14 OPEN leaves**, with every parent, completed bound
round and closed cover retained. Original `negative-16a2fc93c8d133f0` remains
OPEN; no original-cell or mask credit is added.

## Precise regional scope

The tree covers only the merged closed I21/I22 region of mask `001/00`:

\[
x_I\in[-163627/2097152,\;2457813/4194304],\qquad
y_I\in[-91/120,\;91/120].
\]

Its unchanged parent restriction has SHA256
`142b74254b59e00267298ea59fa27bef68b392a220f9509aa4a88221f514d5cc`.
The independently checked whole-domain attachment explicitly returns false.
The other fourteen original I-quarter proofs remain separate accepted evidence.
This regional continuation neither replaces them nor completes the original.

All nine original physical squares, 36 corners, 36 pairs, the five marked
cones, actual AB/BC/EF/FG links, strict weak CD and shared closed faces are
preserved through the unchanged ancestry and independent checker.

## Fourteen exact exclusions

The new terminal leaves are **2, 3, 6, 8, 10, 12, 20, 22, 35, 37, 39, 41, 43
and 44**. Every one was a zero-round leaf with identical old initial and final
states. Its new record changes only the status and existing terminal literal,
and removes the old final-state field.

Thirteen leaves are excluded by the unchanged necessary center-interval
propagator. Leaf 43 is excluded by the incompatible F/I vertical-difference
bounds

\[
-14586234245506722041/34587645138205409280
\le y_I-y_F\le -640855/1048576.
\]

The lower endpoint exceeds the upper by the exact positive rational
`6552591481044932359/34587645138205409280`. No new row family, terminal rule,
rounding convention or geometric assumption is introduced.

The other **31 node payloads are byte-identical** to the published source,
including every parent and the two earlier exact-reserve leaves. All seven
four-way proxy unions and eight two-way closed-angle unions remain complete.
There were no ancestor status changes in this actual result.

## Completed exact replay and independent review

Root observed the full fresh checker process, session **16960**, exit 0.
The saved report and raw log are under `native/d_work/`. The report SHA256 is
`03754a15723bc8e9fc67a685a980ccaa50d034487ca94b827849d1acc31be451`.
It freshly replays the original and regional parent ancestry, all 45 node
records, **21 rounds, 2,324 deductions and 7,865 printed rows**. The complete new
manifest SHA256 is
`941243cf54bde2070916a29c95c1a2bdba7b5c5e8651ec690c1f482788c210db`.

The separate independent source, byte, physical-scope and cover review is in
`independent_review/`. Its audit observed session 2743 exit 0, rehashed all 293
source identities in the full report, independently compared all old/new node
payloads, checked the exact manifest delta and visited all complete covers.
This review did not repeat the full weighted arithmetic.

The constructor's manifest and attachment retain their historical pending-gate
fields because those bytes were the inputs to the completed replay. The final
report and this README record completion without modifying frozen proof inputs.
`OBSERVED_EXECUTION.json` distinguishes the root-observed full replay from the
reviewer's directly observed byte audit.

## Thin payload and published dependencies

This folder includes the new screen and constructor, screen result, full fresh
report and raw log, complete manifest and attachment, fourteen changed node
payloads, independent review and exact metadata. It references the 31 unchanged
payloads by path, length and SHA256 in `PUBLISHED_DEPENDENCIES.json`.

Those payloads are members of the already published 185-member transport in
`research/nine/computer_assisted/b_recovery_center_continuations_v1`, commit
`35ac6d675d74f013a59804ef5506b74b005b59d6`, archive SHA256
`ddba86d2dda6c261e1a3b2868459ddbb7eced058fc0c91c8b72d56254d6f6e93`.
The source/readiness recovery checkpoint was published at commit
`89f274da05abb8337573caf048407540fb318ab0` in
`research/nine/computer_assisted/b_recovered_center_moment_readiness_v2`.
Their exact metadata and the older required-archive inventory are copied under
`published_dependency_metadata/`.

This is a native continuation checkpoint with explicit published dependencies,
not a new self-contained cold portable proof. The unchanged independent
checker and its exact canonical source/ancestry paths must be restored using
the published recovery bindings before repeating the full native replay.

## Reproduction

Use Python 3.12 with assertions enabled. The following first checks package
identities and the exact old/new delta, then materializes all 45 node payloads
into a fresh directory from the retained prior tree and fourteen new files:

```sh
python3.12 -B -S verify_packet.py \
  --prior-tree /path/to/reassembled_B16a_published_prefix_v1

python3.12 -B -S materialize_tree.py \
  --prior-tree /path/to/reassembled_B16a_published_prefix_v1 \
  --output /tmp/b16_interval_continuation_fresh
```

These two commands check bytes and attachment consistency; they do not repeat
weighted arithmetic. After exact restoration of the declared native source
paths, the unchanged full checker can be invoked with the reconstructed tree:

```sh
python3.12 -B -S /workspace/scratch/f9f48fcfb253/b_work/verify_b_accepted_center_disk_tree_v1.py \
  /tmp/b16_interval_continuation_fresh/manifest.json \
  /tmp/b16_interval_continuation_fresh_replay.json \
  --packet /workspace/scratch/f9f48fcfb253/b_work/b16a_I32_complete_H_checkpoint \
  --cap-proof-dir /workspace/scratch/f9f48fcfb253/b_work/recovery_20261105/extracted_b340/unpacked/b340_complete_original_package/accepted_repo/research/nine/computer_assisted/full_angle_common_side_row_v1
```

The new native screen, constructor and screen-result paths named in the
manifest are part of this package under `native/`; they must be restored
byte-exactly alongside the previously published dependencies. Do not rewrite
their hashes, the manifest or the mathematical record contents to bypass a
missing dependency.

No numerical search, active tree, ledger, Git/index, Lean, Lake or CI operation
is part of this checkpoint.
