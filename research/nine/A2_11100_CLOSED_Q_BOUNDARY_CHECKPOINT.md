# The full 111/00 boundary domain is nonempty with strict marked margins

November 4, 2026. Exact discovery, independent rational replay, and a
complete hand/table proof. No Lean, Lake, or CI.

## Accepted boundary classification

There is a physical packing of nine original unit squares at squared
radius **Q=1105/256** admitting the exact fixed mask `111/00`. Its witness
has all five cone comparisons strict, both actual short-link comparisons
strict, and all three weak main-link comparisons strict. Thus the example
does not depend on a marked cone or projection equality face.

The [complete hand/table proof](A2_11100_CLOSED_Q_BOUNDARY_HAND_PROOF.md)
gives nine rational centers, seven aligned original frames, two rational
tilted frames, the orthonormal witness frame `(20,7)/sqrt(449)`, the full
permutation, every physical pair, and the exact five-bit table. The minimum
cone, actual-bit, and weak-bit reserves are respectively
`1/(2 sqrt(449))`, `11/(101 sqrt(449))`, and `7/sqrt(449)`.

Some original corners attain Q and physical contacts remain. Consequently
this is a boundary witness, not a packing below Q. It demonstrates that
discarding marked equality faces alone cannot make the whole closed-Q
`111/00` predicate empty.

Together with the [previous four-mask boundary proof](FOUR_FULL_NINE_MASK_CLOSED_Q_BOUNDARY_CHECKPOINT.md),
all four `111/*` closed-Q domains and `101/11` are now explicitly known
to be nonempty. Their strict-radius obligations remain OPEN.

## Exact evidence and portable replay

The author and root independently executed the standard-library
integer/Fraction checker; the resulting reports are byte-identical.
The root also reviewed its complete source and the physical hand table.
Every original frame, all 36 corners, all 36 full-square pair separators,
the witness frame, the full-nine permutation, and all five comparisons
are reconstructed. Five damaged controls reject. All immutable packet
inputs are rehashed after replay. No human or proof-kernel verification
is claimed.

The [portable exact packet](computer_assisted/mask_11100_full_nine_closed_q_boundary.tar.xz)
and [hash inventory](computer_assisted/mask_11100_full_nine_closed_q_boundary_manifest.json)
retain the table, rational control, checker, proof, fixed physical
contract, both raw replays, and root review. From the extracted
`mask_11100_closed_q_boundary` directory:

```text
python verify_11100_boundary.py --directory . --negative-controls --output FRESH_REPLAY.json
```

The previous four-mask packet is unchanged and is not a runtime dependency
of this supplement. No discovery optimizer or angular sampling is needed
for the finite direct verification.

## Closure accounting

This commits **zero new strict-mask closures and zero new original-cell
closures**. Every original closure register is unchanged: the denominators
remain 32 masks, 231 current-mask cells, 7,915 positional roots, and 15
roadmap IDs. A.2, the unrestricted lower bound, and the full equality
classification remain OPEN.
