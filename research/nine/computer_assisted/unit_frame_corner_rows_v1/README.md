# Exact original-corner rows using the physical unit-frame identity

The [continuous hand proof](UNIT_FRAME_CORNER_HAND_PROOF.md) expands each
original corner's squared norm using the original orthogonal unit frame.
Its square-offset contribution is exactly 1/2. A tangent lower bound for
the center norm and two rectangle lower bounds then give a necessary row
in four existing original variables, with no new auxiliary or separator.

The [independent physical/code review](UNIT_FRAME_CORNER_B_REVIEW.md)
accepts the complete residual identity, coefficient signs, closed interval
faces and independent row reconstruction. Each application must supply
independently proved intervals for that same original center and signed
frame. This is an essential premise: coefficients must be rebuilt on the
current caller's intervals even when rational parameters are cached.

These rows strengthen the ordinary corner supporting rows by retaining
the exact unit contribution before relaxation. The control suite exhibits
a deliberately nonunit relaxed frame whose displayed corners all lie
inside Q but which violates one new necessary row by exactly
`4623/160000`. This is a relaxation diagnostic, not a physical packing.

## Exact replay

Run `python -B -S verify_all.py --output replay.json` from this directory.
The standard-library driver verifies all source hashes and reruns both
arithmetic suites in a temporary directory. The main suite reconstructs
864 rows, checks 12,096 physical expansions, includes 432 rows with
zero-width intervals, and rejects 1,728 damaged literals. The separate
review suite checks 720 exact residual and physical-corner identities.

## Caller interface and proof scope

The producer exposes `row(positions, scalar, *parameters)`. The numerical
separator returns `(parameters, violation)` pairs for optional discovery.
The independent exact adapter calls
`verify_literal(row, positions, scalar)` with its own independently
reconstructed propagated bounds. Every row then participates in the
ordinary exact multiplier, residual and bound replay.

Only parameters may be reused across different interval states. A row
derived on a child box cannot be copied unchanged to a wider parent.
No floating-point optimization result supplies validity. All original
frames, corners, pairs, center cones and marked predicates remain.

The source-only freeze receipt predates the separate accepted review;
the final packet binding records their joint acceptance. No original
cell or mask closes from this helper alone. The ledger stays at 220/231
original cells and 8/32 masks closed. No Lean, Lake or CI.
