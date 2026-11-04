# Four independent product planes for an original disk corner

This [continuous proof](FOUR_RECTANGLE_UNIT_CORNER_HAND_PROOF.md) strengthens
the accepted corner rows that retain the physical unit-frame identity.
It bounds each of the four signed center/frame products independently,
giving sixteen valid affine inequalities on the same original domain.
The previous four grouped planes are included exactly.

Each row uses four of the existing 54 original variables. It introduces
no auxiliary, physical separator or new branch assumption. Repeated
appearances of the same center or frame component are retained at their
same actual values throughout the proof. Every interval must already be
certified for the current original caller.

The [root physical/code review](ROOT_PHYSICAL_REVIEW.md) and fresh
relocated exact controls pass. The suite checks 3,456 literal expansions
and physical residual identities, 864 exact reproductions of the grouped
family, all 36 signed original corners and all sixteen plane patterns.
Five damaged literals or substitutions of wider caller bounds are rejected.

## Replay

Run `python -B -S verify_all.py --output replay.json` from this directory.
The driver verifies the entire source inventory and recreates the original
relative directory layout in a temporary directory. It runs the unchanged
standard-library control program there. The frozen accepted grouped
producer is included only to check exact containment of the earlier family;
the independent new-row checker imports neither producer.

## Integration

The producer exposes
`row(positions, scalar, original, epsilon, tau, px, py, choices)` with four
binary entries in `choices`. The exact adapter calls
`verify_literal(row, positions, scalar)` with independently propagated
current original intervals. The distinct prefix is
`physical_unit_four_corner_`.

Parameter tuples may be cached, but coefficients and right sides must
be rebuilt for every current interval state. A child row cannot be moved
unchanged to a wider parent. Numerical selection only decides which valid
rows to propose; all weighted literals, multipliers and residuals still
undergo exact replay.

These sixteen choices are sixteen simultaneously valid inequalities,
not sixteen new domains requiring a cover. This helper grants zero
original-cell and mask credit. The fixed registers remain at 220/231
original cells and 8/32 masks closed. No Lean, Lake or CI.
