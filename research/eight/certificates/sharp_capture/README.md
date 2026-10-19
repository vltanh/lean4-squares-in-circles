# Completed sharp-capture evidence

This package preserves the complete continuous capture used by
[UNRESTRICTED_EIGHT_SQUARE_SHARPNESS.md](../../UNRESTRICTED_EIGHT_SQUARE_SHARPNESS.md).
The unrestricted radius theorem is complete with exact computer assistance.
The requested hand proof is a separate, active gate: archiving a certificate
does not turn it into an analytic proof.

## Contents and integrity

| Archive | Contents | Bytes | SHA256 |
|---|---|---:|---|
| `sharp_capture_completed_evidence.tar.xz` | All 123 completed ordinary exclusions, four complementary-owner certificates, four selected terminal budgets, immutable sources/data/headers, complete logs, original manifests and independent audits | 4,835,656 | `37b3a67bf69b7e72328df9d95277632c9de32a0f61ed1083d9f4f1628be70eaa` |
| `sharp_capture_interfaces.tar.xz` | Symbolic domain covers, terminal frame and slider interfaces, broad stationary-graph and dual-coefficient proofs, and their exact dependencies | 368,268 | `cc3327adabb5db9fc9343262be3bc3f7605d98a96b04d22ffacd66c266edc257` |

`BUNDLE_MANIFEST.json` binds both archives. The numeric archive contains
28,039 evidence files and its internal hash manifest. The supplemental
archive contains 170 additional files and its internal replay/manifest
record. The original directory hierarchy is retained so that the audit
programs can be replayed without rewriting hashed source files.

The [certificate index](../../SHARP_CAPTURE_CERTIFICATE_INDEX.md) gives
counts, exact ceilings, and the selected/complementary SAT partition. The
[independent global audit](../../COMPLETE_BOUNDARY_CAPTURE_INDEPENDENT_AUDIT.md)
checks the completed manifests and the global domain interfaces. The
[mean-value audit](../../MEAN_VALUE_PAIR_KERNEL_AUDIT.md) explains the exact
arithmetic acceptance tests and the optional analytic acceleration.

## Portable interface replay

Python 3.12 and the standard library suffice. From a repository checkout,
run, choosing a destination that does not already exist:

```bash
python research/eight/certificates/sharp_capture/replay_bundle.py /tmp/eight-square-capture-replay
```

The script authenticates both compressed archives, permits only regular
relative-path members, checks every extracted size and SHA256, then runs
all thirteen mathematical interface audits in the fresh destination.
It writes `PORTABLE_REPLAY.json` there. Use `--extract-only` to authenticate
and extract without running those audits.

The thirteen replays cover the rational upper bound for 2π, all three
global closed-domain unions, all four terminal frame lifts, the broad
stationary graph and reduced curvature, an independent check of every
dual-owner coefficient, and both one-core and all-outer slider bounds.
The two-core slider interface is included in its terminal proof note.

This replay **does not rerun the original 123 subdivision trees**.
Those completed exact executions and their independent binding/coverage
audits are preserved in full. To rerun a tree, follow the corresponding
entry in `m5_agent/completed_capture_registry.json`, regenerate its
header from the recorded rational JSON, compile the recorded source with
undefined-behavior sanitization, and run its recorded driver into a new
output directory. The original manifests bind the original executable
and source hashes; a newly compiled executable needs a new replay manifest.

The elementary central-core, four-type, three-core, and short-two-core
certificate packages precede this capture and remain in their existing
locations under `research/eight`. No incomplete or rejected discovery
input is counted as a proof in this package.
