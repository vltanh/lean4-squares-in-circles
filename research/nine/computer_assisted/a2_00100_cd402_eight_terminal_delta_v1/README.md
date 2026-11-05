# Cd402: eight exact frontier substitutions

This checkpoint excludes eight existing closed frontier domains of
`negative-d4021ade840b985c`, mask `001/00`, in the unchanged strict-radius
original-nine caller `q < Q = 1105/256`.
The frozen frontier decreases from 25 to 17 pending alternatives. The whole
original and the whole mask remain OPEN; this packet earns zero original,
mask, positional-root or roadmap credit.

## Delivered evidence

| Item | Result |
|---|---|
| New excluded frontier indices | 40, 41, 471, 472, 478, 479, 486, 487 |
| Fresh original-bound replay | Three rounds; 556 deductions; 948 printed rows |
| Necessary old ancestor records replayed | Ten, with every relevant child state reconstructed |
| Total fresh deductions and printed rows | 1,628 deductions; 4,053 printed rows |
| New terminal rows within that total | 50 |
| Complete child covers structurally checked | 141, with all sibling alternatives retained |
| Compressed delta | 89 regular files; 970,456 bytes |
| Proof scope | Native replay of the original-to-eight-terminal ancestry union |

`HAND_TABLE.md` gives the physical table and an exact three-row cancellation
for domain41. Its five original physical rows combine with positive rational
weights to give zero coefficients and strictly negative right side.
`NATIVE_REPLAY.json` is the fresh successful replay after relocating the
delivered records. It independently derives all eight starting states from
the unchanged original, then checks their exclusions. Numerical modules,
Lean, Lake and CI were not used.

The other inherited branches are not freshly replayed here. Their complete
manifest entries and source hashes remain present, and no unfinished sibling
is omitted. The latest independent substitution applies to one frozen
manifest; a later live search may already have proved an overlapping leaf.
Such overlap does not add another domain or original-cell exclusion.

## Reproduce the native replay

Use Python 3.12 with assertions enabled, `-B` and `-S`. Supply the retained
native C checker directory and a fresh output directory:

```sh
python3.12 -B -S replay_native_delta.py \
  --native-c-family-root /path/to/research/nine/.runs/c_family \
  --output /tmp/cd402-eight-terminal-native-replay
```

The launcher verifies the archive and every extracted file, checks the
native runtime source hashes, and replays the saved original bound, ten
ancestors, eight terminals and the exact hand cancellation. The expected
status is `PASS_NATIVE_ANCESTRY_AND_EIGHT_TERMINAL_SUBSTITUTIONS`.

This command requires the published legacy bases and their retained native
import/fixture layout. `NATIVE_DEPENDENCIES.json` records the exact runtime
source identities; `DEPENDENCIES.json` pins the published bases. The archive
preserves source snapshots for future transport, but this delta does not
implement cold transport. See `SOURCE_BOUNDARY.md`.

## Archive layout

The archive root is `payload/`:

- `terminals/`: all eight new certificates, unchanged.
- `ancestry/`: all ten needed old node records, the original three-round
  bound certificate, and the fixed original register.
- `evidence/`: source and grafted complete manifests, full inherited-node
  hashes, initial local exact reports, and the exact hand cancellation.
- `runtime_source_snapshots/`: the 48 hash-bound native checker sources.
- `published_dependencies/`: the two published packages' exact metadata.
- `discovery_sources/`: bounded numerical procedure and preparation sources.
- `diagnostics/`: unsuccessful broad-ancestor and stopped BFS receipts.

The numerical sweep used 21 phase LPs to examine 24 siblings. It used no
coordinate-bound rounds. Seven broad-ancestor LP tests stayed feasible;
a smaller-row BFS was stopped when one sibling expanded into 67 pending
alternatives without closing the sibling. Those diagnostics add no proof
claim. There is no running job associated with this checkpoint.
