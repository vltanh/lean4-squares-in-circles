# C original height consequences and shared bounds

This package supplies three necessary height inequalities on two remaining original cells of mask `001/00`, plus 414 certified original-variable bounds on C887 and an exact certificate that uses those bounds. Both original cells remain **OPEN**. The package claims **zero new original cells and zero new masks**.

## Fresh portable result

The final fresh portable replay passed in 330.58 seconds. It rehashed all 2,015 inputs at completion and independently repeated every archived source exclusion, the unsplit C887 root, and the first weighted shared-bound cover. The receipt SHA256 is `0ec2356ee2becd7b1b56c80929f7dab6dfcf7ae272b85ce990a6e454e621fe8d`. The final transport controls also passed eleven positive checks and twelve rejected mutation/access cases.

## The proved consequences

The archived checkers exclude the following entire closed height domains while preserving the complete original-cell hypotheses. Negating each excluded closed halfspace gives a strict necessary inequality; weakening it gives the displayed closed row.

| Original cell | Archived closed domain excluded | Necessary weak inequality |
| --- | --- | --- |
| `negative-887236b78100baf3` | Branch 7: `y_A - y_D <= -23/100` | `y_D - y_A <= 23/100` |
| `negative-b882d8ade0cf9ea0` | Branch 4: `y_A + y_D - 2*y_H <= -23/100` | `2*y_H - y_A - y_D <= 23/100` |
| `negative-b882d8ade0cf9ea0` | Branch 7: `y_A - y_D <= -23/100` | `y_D - y_A <= 23/100` |

Every row is bound to its exact original ID and original path. No selected SAT alternative, child orientation cut, or child interval is transported to the original cell. All nine original squares, 36 original corner predicates, 36 original pair predicates, the five marked cones, actual AB/BC/EF/FG links, the strict weak CD link, and shared equality faces are retained.

The C887 whole-root source also uses a separately replayed complete eight-alternative D/G cover. That cover joins only necessary bounds on the original variables. Its surviving alternatives are retained; its purpose is stronger original bounds, not an original-cell exclusion.

## Shared C887 bounds

An unsplit C887 root certificate has six exact bound rounds, 416 deductions and 858 checked printed rows. Two weighted row occurrences use the new archived-height consequence. The independently reconstructed final state yields 414 affine necessary bounds on original coordinates, frame scalars, slopes, pair differences and diagonal differences. No SAT auxiliary or selected child predicate is carried into this source state.

The first-use certificate is a complete 91-node cover with 73 explicit leaf domains. It contains 57 rounds, 8,780 deductions, 39,146 printed rows, 14 weighted uses of the shared C887 root bounds and 783 weighted four-product corner rows. Its remaining domains are explicitly OPEN. The current numerical search is outside this frozen publication checkpoint.

## Reproducing the portable replay

Use **Python 3.12**, with assertions enabled and both `-B` and `-S`. The tested pathlib output routing relies on Python 3.12 path-join behavior. NumPy, SciPy, HiGHS, Lean, Lake and CI are not used by the replay.

Concatenate the two delta parts in `ARCHIVE_MANIFEST.json` order. The resulting `c_original_height_consequences_v1_delta.tar.xz` has SHA256 `d17d9582e5ebfdde535be70dea47853d5a8d2fa4b0bddc0a287b35255caa745b`. Extract it and use the extracted `c_original_height_consequences_v1_delta` directory as `delta` in the commands below. The archive byte audit checked all 181 regular members.

Extract the two previously published bases:

- The A portable OPEN checkpoint, under `research/nine/computer_assisted/a2_00100_a_c744_portable_open_checkpoint`. Its assembled input-manifest SHA256 is `6b730ae5e0dabed264d7e71ba6de72bc15f744d7bba619ed8f6c27a86b9097cf`.
- The Cb882 whole-eight checkpoint, `research/nine/computer_assisted/a2_00100_cb882_whole_eight_checkpoint.tar.xz`. Its extracted manifest SHA256 is `3186ac6e498fe09bfc010d50f4b294f8bb1b2f351c18529e527af22e7dda97f2`.

Materialize the packet into a fresh `/tmp` directory. Replace the three input paths below with the extracted directories:

```sh
python3.12 -B -S delta/materialize_c_height_publication.py \
  --delta delta \
  --a-base /path/to/A_packet \
  --cb-base /path/to/cb882_whole_eight_checkpoint_package \
  --output /tmp/c_height_packet

python3.12 -B -S /tmp/c_height_packet/replay_portable_c_height_packet_v3.py \
  --packet /tmp/c_height_packet \
  --output /tmp/c_height_fresh_replay
```

Both output paths must be fresh. The whole packet and output belong under `/tmp`; the unchanged archived checkers retain their historical strict `/workspace` guards. The outer launcher independently blocks every unbound workspace read and every unlisted packet read in all subprocesses.

An optional separate control run uses another fresh output directory and adds `--transport-controls`. It verifies exact file/reference aliases, unchanged mathematical strings, known diagnostic output routing, and rejection of packet writes/mutations, unlisted reads, numerical imports, and resolved output-symlink escapes.

## Input identity and transport

The thin delta has 172 new mathematical files, totaling 143,575,284 uncompressed bytes. Materialization reuses 1,380 byte-identified A payload members and 456 Cb882 members. The complete A base is included in the inventory so transitive imports and strict package hash checks remain explicit. Unused base members are inventory-only; they do not become proof premises.

The final assembled input manifest contains 2,015 files totaling 687,782,645 bytes. Its SHA256 is `06115f494173bc344821932525d7a8522df8ea2ed80b400f735f3b68d4a1b58b`.

No mathematical source or certificate byte is rewritten. Filename transport maps only exact inventoried absolute strings, with dictionary keys mapped only for explicit file aliases. Raw byte reads and SHA256 semantics are unchanged. All packet writes and mutations are forbidden. The old checkers' diagnostic report directories are routed into fresh output; their full subtrees are disjoint from every frozen input. Every isolated child installs the same path checks and rehashes all inputs at completion.

The full protocol freshly repeats all three archived closed-domain exclusions, the strengthened C887 root and the first weighted shared-bound use. Saved PASS reports are never accepted as substitutes for these replays.

## Publication review and scope

The `reviews/` directory contains the physical/domain reviews, independent bound review, transport design review and final root acceptance. `fresh_replay/` preserves every report and log from the completed portable run. `PUBLICATION_MANIFEST.json` binds all outer publication files; the archive and input manifests separately bind the exact proof payload. The frozen inner README preserves the inventory preparation history; this outer README records the final completed replay.

The stable ledger remains **220/231 original cells and 8/32 masks closed**. No positional-root or roadmap credit is added. The PR remains draft.
