# Verified whole-mask closure: 000/01 and 000/10

November 2, 2026, America/Chicago. Baseline PR head:
`add3c530e760ddf15cb936a72ee4761a1fcdbe73`.

## Result

The complete fixed nine-square predicates `D_000/01^le` and
`D_000/10^le` are empty at `Q=1105/256`. In particular their strict-radius
obligations are closed. The proof retains all nine original squares,
their independent frames, all 36 corner constraints, all 36 physical
pair constraints, and the original center-cone and strict-weak bit
conventions. No additional height, tilt, owner, or placement hypothesis
has been added to either mask.

The main proof is
[A2_000_01_WHOLE_DOMAIN_HAND_TABLE_PROOF.md](A2_000_01_WHOLE_DOMAIN_HAND_TABLE_PROOF.md).
Its exact tables and standalone replay code are in `computer_assisted/`.
The proof was recovered from saved work, checked against the current
fixed-domain contract, independently reviewed, and freshly replayed
before changing the frontier. Recovery alone was not treated as closure.

## How the complete argument closes

The actual four-chain supplies an adjusted endpoint span `D>=2`.
The established routing places the selected short-chain shoulders L,R
in explicit upper side bands. Split on the whole floor of the original
middle square P at `1/10`.

If P has high floor, it is the central square U used by the sharp cap.
If P has low floor, the complete side barriers and dynamic original
inner insets force both remaining squares into the central strip.
At most one can lie below the two inner mains. A complete table places
the other above P, and a second complete table proves its whole floor
is greater than `1/10`. This is an original physical square U, not a
replacement or a proxy. Thus the two branches supply the same cap
with every hypothesis proved.

The cap retains the same central square in both support terms. Four
outer support envelopes and one central transfer give

    46 D + 27/2 <= 211/2,

strictly below Q. Since `D>=2`, this is a contradiction at every
strict radius, however close to Q. At closed Q the strict central
transfer forces horizontal central separators. Equality in the
original two-square caps then aligns the right shoulder. The original
actual L--P and cone P--R comparisons force P to align as well, making
P--R actual and contradicting its strictly weak bit. Simultaneous
coordinate and chain reversal supplies `000/10`.

## Exact replay and independent review

| Component | Strict interval leaves | Additional analytic leaves |
|---|---:|---:|
| Left-side extra barrier | 11,744 | 0 |
| Low-floor inner-main heights | 59,225 | 0 |
| Central upper extra at or below P | 62,000 | 0 |
| Central upper extra whole floor | 356 | 0 |
| Shoulder-owned negative envelope | 1,700 | 0 |
| Shoulder-owned positive envelope | 490 | 0 |
| Endpoint-owned negative envelope | 25 | 0 |
| Endpoint-owned positive envelope | 28 | 0 |
| Central transfer | 1,684 | 34 |
| **Total** | **137,252** | **34** |

All nine complete tables passed fresh independent exact replay. The
checkers reconstruct the prescribed rational roots, both children of
every midpoint split, and each strict rational leaf inequality. The
four large geometric checkers use exact fractions and outward integer
square-root bounds. The support checkers use standalone directed
dyadics; the two endpoint-owned tables also passed the separate exact
Fraction backend. All twelve fresh incomplete-tree, invalid-split,
and false-root-leaf controls were rejected.

The human-readable manuscripts specify the root boxes, subdivision
rules, leaf inequalities, local analytic complements, and the finite
dependency order. The JSON files are exact finite tables encoded as
midpoint trees; they are not sampled angles or solver verdicts.

Independent agent reviews checked the low-floor physical reductions,
the sharp support and central transfer arguments, the owner and slope
cover, the equality deduction, and the assembly against the unchanged
mask predicate. See
[A2_000_01_LOW_FLOOR_AUDIT.md](A2_000_01_LOW_FLOOR_AUDIT.md),
[A2_000_01_ASSEMBLY_AUDIT.md](A2_000_01_ASSEMBLY_AUDIT.md), and
[A2_000_01_SUPPORT_TABLE_AUDIT.md](A2_000_01_SUPPORT_TABLE_AUDIT.md).
No independent human or kernel verification is claimed. No Lean,
Lake, or CI was run or modified.

## Reproduce the accepted finite checks

Run from `research/nine/computer_assisted/`, using ordinary Python
without optimization flags (the independent checkers use assertions):

```sh
python verify_left_table_exact.py
python verify_badfloor_mainheight_exact.py
python verify_central_upper_below_p_exact.py
python verify_upper_extra_floor_exact.py
python verify_outer_scalar_family.py outer_R_linear_negative_cover.json
python verify_outer_scalar_family.py outer_R_linear_positive_cover.json
python verify_E_variable_k_linear.py E_variable_k_linear_negative_cover.json --fraction
python verify_E_variable_k_linear.py E_variable_k_linear_positive_cover.json --fraction
python verify_central_linear_transfer.py central_linear_transfer_compact.json
```

These replay scripts use the Python standard library. The optional
discovery producers are outside the accepted proof dependency and may
use numerical libraries. The exact certificate and source hashes are
recorded in `computer_assisted/mask_00001_closure_manifest.json`.

## Accounting and the next full domain

The fixed mask frontier changes from 2 closed / 30 open to **4 closed /
28 open**. The new entries are closed even at Q. The historical
positional-root counts remain **5,838 closed-Q exclusions / 2,077 open**;
no original-root manifest was rerun and no root count was inferred from
the mask closures. The same 15 roadmap IDs are retained.

The next target is the complete `000/11` domain, the remaining row
with an actual four-chain. The new proof uses the actual L--P edge in
its low-floor reductions and cannot be silently applied when both
short-chain links are weak. A.2, the unrestricted lower bound, global
equality, and the final global manuscript remain open.
