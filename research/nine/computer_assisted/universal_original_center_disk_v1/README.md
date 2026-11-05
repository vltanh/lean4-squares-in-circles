# Universal supports for the nine original square centers

For a physical unit square whose four original corners lie in the closed disk of squared radius `Q=1105/256`, its center satisfies `||c|| < 91/60`. The hand proof derives this from the exact four-corner expansion and the positive rational reserve `31/57600`.

Consequently, rational coefficients `a,b,s` with `s>=0` and `3600*s*s>=8281*(a*a+b*b)` give the necessary row `a*x_i+b*y_i<=s`. The independent checker reconstructs the two original coordinate columns and checks this squared inequality using only rational arithmetic. There are no orientation, pair-separator, mask-bit or child-domain premises.

The family now participates in fresh B, A and C discovery. The first Bf14 whole-original partial cover was independently replayed with 1,034 weighted occurrences of these rows. That partial cover does not close an original; the complete tree certificate must account for every remaining branch before the fixed ledger changes. This directory establishes the universal row family, not a whole-cell or whole-mask closure.

## Exact checks

Run from the repository root:

```sh
python -B -S research/nine/computer_assisted/universal_original_center_disk_v1/check_universal_center_disk.py --output /tmp/center-controls.json
```

The controls include exact physical corner expansions, signed and zero directions, all nine original column pairs, rational supporting-circle boundaries, and rejection of damaged literals. The numerical separator only proposes directions; every accepted weighted row must pass `independent_physical_center_disk_rows.verify_literal` in the consuming exact checker.

## Caller attachment

Each index `i` must identify a retained physical original unit square with its orthonormal frame and all four original corner bounds at the same `Q`. The caller keeps its strict-radius target and the full original physical problem. Appending these rows changes no original path, exact mask bit, actual link, strict weak link, or closed covering face. A tree replay must invoke the independent literal checker for every weighted occurrence and retain its normal physical ancestry checks.

The source files are preserved separately from running search contexts. No Lean, Lake, compilation or CI is used. Original-cell credit: **0**. Mask credit: **0**.
