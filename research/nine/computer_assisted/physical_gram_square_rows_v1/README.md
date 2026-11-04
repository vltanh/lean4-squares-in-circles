# Exact square-norm rows in existing physical SAT variables

These two conditional row families strengthen the relaxation of a retained
physical separating-axis alternative. Every emitted row follows from an
ordinary nonnegative squared Euclidean norm. Numerical eigenvectors only
suggest rational parameters; they are not proof evidence.

The [frame proof](PHYSICAL_PAIR_FRAME_SQUARE_HAND_PROOF.md) couples both
original unit frames and their existing four cross products. The
[projection proof](PHYSICAL_PROJECTION_SQUARE_HAND_PROOF.md) couples the
same original-owned unit normal, original center difference, and existing
two projection products. Neither family introduces a new auxiliary, a
new separator, or a restriction on the rational parameter vector.

The [root physical review](ROOT_PHYSICAL_REVIEW.md) records the geometric
identities and exact caller obligations. [PREMISE_BINDINGS.json](PREMISE_BINDINGS.json)
binds all delivered sources and distinguishes universal row validity from
the separate task of proving a complete original-cell cover.

## Reproduce the independent arithmetic controls

From this directory, run:

```sh
python -B -S verify_all.py --output replay.json
```

The standard-library driver checks the source hashes, copies only the
standalone producers, independent checkers, and controls into a temporary
directory, and reruns both exact suites. It does not import an optimizer,
the B search runtime, Lean, or Lake. The two suites independently reconstruct
560 rows, evaluate 32,224 rational physical instances, and reject 16 altered
right sides. `ROOT_FRAME_REPLAY.json` and `ROOT_PROJECTION_REPLAY.json` retain
the separate fresh root replay receipts.

The `*_separation.py` files and `b_*_runtime.py` files are frozen discovery
and integration snapshots. The latter require the enclosing B caller and
are not standalone proof drivers. Their numerical outputs must always be
reconstructed by the independent literal checkers and the caller's exact
nonnegative-multiplier replay.

This package closes **zero original cells and zero masks**. It leaves the
fixed registers at 220/231 original cells and 8/32 masks closed. Future
applications must prove every source interval and retain all nine original
frames, all 36 original pairs and corners, all five center-cone comparisons,
and the unchanged marked predicates and closed branch faces.
