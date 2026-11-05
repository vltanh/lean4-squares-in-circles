# Relative-support chords for an original pair

This family strengthens the existing unit-incircle chord using the relative
orientation of the same two original squares. It adds no square, product
variable, separation-axis choice, or case restriction. **No original cell or
mask is closed by this checkpoint.**

## Physical implication

The accepted signed and folded relative-frame argument gives
`norm(center_j-center_i) >= h`, where
`h = (1 + C + abs(S))/2` and `1 <= h <= 121/100`.
Let `d` be a certified nonnegative signed coordinate difference and let `t`
be the transverse coordinate, with proved interval `[L,U]`. Then `t/h` lies
in `[min(L,100L/121), max(U,100U/121)]`.

An affine chord `m*z+b` below `sqrt(1-z*z)` on that entire closed ratio
interval proves `d >= m*t+b*h`. When `b >= 0`, substitute the lower bound
`h >= (1+C+epsilon*S)/2`, then independently valid lower planes for each
of the four frame products. The resulting necessary row is linear in the
original center and frame variables. Both endpoint faces are included.

`INDEPENDENT_REVIEW.md` gives the complete chord argument and guards.
`OWNER_FREE_RELATIVE_SUPPORT_HAND_PROOF.md` supplies the original geometric
support theorem, including the folded-frame comparison. The independent
decoder imports only `Fraction` and reconstructs all coefficients from the
same physical scalar and difference intervals.

## Checks and actual use

Run the portable literal checks with:

```sh
python -B -S check_controls.py
python -B -S check_weighted_new_rows.py
```

The controls check 1,792 literals in 28 interval domains and reject 19 damaged
literals or caller guards. The second command checks the ten actual new
rows in the saved B7 conditional bound record and verifies that each receives
a positive rational multiplier. It is explicitly conditional on the saved
input intervals and does not reconstruct the other row families.

Separately, `NATIVE_PREFIX_REPLAY.json` records a fresh independent replay of
the original B7 ancestry, all ten nodes of its prefix to saved node 260,
and the complete new bound round: 105 deductions and 441 printed row
occurrences, including those ten new rows. That native check passes with
numerical producers absent. The conditional state remains OPEN.

`B7_CONDITIONAL_BOUND_RECORD.json.gz` contains the full numerical certificate
record, with exact uncompressed SHA in `WEIGHTED_SCOPE.json`. The native
adapter and prefix entry are retained under `native_context`. Their full
original ancestry remains an explicit external dependency; this packet does
not claim a new portable whole-original proof.

Small phase-only probes found no new large branch exclusion attributable to
this family. Main search adoption therefore remains a separate continuation
decision. All closure ledgers remain unchanged at 222/231 current-mask cells
and 8/32 masks CLOSED. No Lean, Lake, compilation, or CI was run.
