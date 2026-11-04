# Adaptive exact supporting rows for the original disk corners

The [continuous physical proof](ADAPTIVE_ORIGINAL_CORNER_DISK_HAND_PROOF.md)
turns an arbitrary rational direction into a necessary supporting row for
one of the original 36 corners. Its coefficients use four of the existing
54 original variables. It adds no auxiliary, separator, interval assumption
or restriction of the original caller.

A numerical point may suggest a useful direction. The support bound is
rounded upward by exact integer arithmetic, and the independent checker
validates it by a separate rational squared inequality. The
[independent physical/code review](ADAPTIVE_CORNER_DISK_B_REVIEW.md)
and exact controls pass. The discovery routine is optional; the validity
of every row follows from the original closed disk predicate.

## Replay

Run `python -B -S verify_all.py --output replay.json` from this directory.
The standard-library driver checks all source hashes and reruns the
arithmetic controls in a temporary directory. The controls reconstruct
504 rows, check 31,752 exact corner expansions and 4,032 exact disk-boundary
cases, and reject 1,008 invalid literals. A separate independent review
also checked 144 rows and 576 exact expansions.

## Integration

`physical_corner_disk_separation.violated_parameters(point)` returns
`(parameters, violation)` pairs. Call `physical_corner_disk_rows.row(*parameters)`
to construct a row. The exact replay dispatches every printed row with
prefix `physical_corner_disk_` to
`independent_physical_corner_disk_rows.verify_literal(row)`.

Rows remain valid across child domains because they use no child interval
or selected separator premise. They must still be included in the same
exact row-index, multiplier and residual replay as all other necessary
inequalities. Appending a row must not change an earlier row's index.

This package adds zero original-cell and mask closures. The ledger remains
220/231 original cells and 8/32 masks closed; complete original ancestry
and closed covers are still required for any change. No Lean, Lake or CI.
