# Two complete B originals by exact quadratic center-cover proofs

November 4, 2026. This checkpoint closes exactly the unchanged original cells
`negative-0e4fa3209b6f7b12` and `negative-6ad5eef3b91c1fbd`. It advances the
fixed current-mask register from **198 CLOSED / 33 OPEN to 200 CLOSED / 31 OPEN**.
All 231 original IDs and paths are retained. The full-mask ledger remains
**8 CLOSED / 24 OPEN**; `001/00`, its reversal `100/00`, A.2, the unrestricted
bound and global equality remain OPEN.

[Source-bound packets and fresh replays](computer_assisted/a2_00100_two_b_psd_manifest.json) ·
[Fixed original register](gates/A2_00100_FIXED_FRONTIER.json) ·
[Physical caller and coverage contract](A2_COVERAGE_AND_CLOSURE_CONTRACT.md)

## 1. Complete original predicates

Both proofs start from the original registered path and the same normalized
`001/00` caller: nine independent physical unit squares, all 36 corners and
36 pairs, five marked center-cone comparisons, actual AB/BC/EF/FG and strictly
weak CD, for every `q<Q=1105/256`. They retain the accepted low-gap reduction,
the canonical original frame intervals and `x_H<=x_I`. The original paths
are reconstructed and their canonical ID hashes checked by the ancestor
replay. No owner, position or frame restriction is added without proof.

The exact parent induction proves an I-center rectangle for each original.
Each rectangle is covered by its sixteen equal closed coordinate rectangles,
four pieces per coordinate. The remaining eight centers and all nine frames
remain in their entire certified parent domains. There is no H subdivision.
Every interval endpoint and shared face belongs to the cover.

## 2. The two complete tables

| Original ID | Closed I rectangles | Affine terminals | Interval terminals | Quadratic terminals | Printed terminal rows |
|---|---:|---:|---:|---:|---:|
| `negative-0e4fa3209b6f7b12` | 16 | 8 | 7 | 1 | 1,605 |
| `negative-6ad5eef3b91c1fbd` | 16 | 7 | 4 | 5 | 6,208 |
| **Total** | **32** | **15** | **11** | **6** | **7,813** |

The complete coordinate tables, exact rational rectangle endpoints and simple
positive reserve floors are printed in the respective hand proofs:

- [B0e4 complete original-cell proof](A2_00100_B0E4_FIXED_CENTER_PSD_CLOSURE.md).
- [B6ad complete original-cell proof](A2_00100_B6AD_FIXED_CENTER_PSD_CLOSURE.md).

Their packet `COVER_TABLE.json` files are checked entry by entry against the
independent terminal outputs. The assembler requires exactly the sixteen
indices `0,...,15`, matches each to its coordinate pair, and replaces only
the explicitly listed affine remainders with their proved quadratic terminals.
Thus an incomplete child list cannot be accepted as a whole-original proof.

## 3. Why each terminal is a physical contradiction

The interval terminals repeat exact original-center propagation. They either
produce an empty interval or exclude every separation alternative for a pair
of contained original insets. Each affine terminal is an explicitly weighted
nonnegative rational sum of independently reconstructed physical rows.

The quadratic terminals use 54 original variables and their 1,485 shared
quadratic products, for 1,539 lifted coordinates. Every physical configuration
embeds in these coordinates using its actual products. Each used RLT row is
the product of a proved affine slack and a nonnegative coordinate-bound slack;
its affine premise is independently reconstructed in the same rectangle.
Each used rational square is the exact polynomial inequality

`-(q_0 + sum(q_i z_i))^2 <= 0`.

Every fixed separating-axis row is checked against the owner, axis and sign
in the unchanged original path. No newly selected separation alternative is
installed globally. The necessary frame, corner, pair and radial rows retain
their full physical hypotheses. Neither a numerical eigenvalue nor a solver
infeasibility status is a proof premise.

For the weighted sum `a·m<=b`, exact absolute bounds `|m_i|<=M_i` pay every
coefficient residual. The checker recomputes

`rho = -b - sum(M_i |a_i|) > 0`.

The same physical point would have `a·m>=-sum(M_i|a_i|)>b`, a contradiction.
The six quadratic certificates use **7,667 printed rows, 220 independently
checked RLT antecedents and 117 explicit negative rational squares**, counted
across the certificates. The 15 affine sums use a further 146 printed rows.
The original ancestors are replayed before any of these rows are admitted.

## 4. Assembly and reproducibility

Every point of either whole original cell lies in one of its sixteen closed
I rectangles. All sixteen are impossible. The complete original cell is
therefore impossible. This deduction retains physical contact and covers every
`q<Q`; it requires no fixed positive clearance in the original predicate.

Each archive is self-contained. After extracting it, run:

```sh
python -B -S verify_all.py
```

The runner checks its frozen file inventory, replays all original bound rounds,
reconstructs all used physical and polynomial rows with exact fractions, and
verifies the whole table. An audit hook rejects unbound reads from another
workspace. Both packets passed again after relocation into the root workspace.
Their fresh reports are included in the repository manifest. No numerical
producer or optimizer is imported by replay. No Lean, Lake or CI is run, and
no human or proof-kernel verification is claimed.

## 5. Fixed accounting and remaining work

This checkpoint adds **two complete original-cell exclusions**, following the
[complete D a497 proof](A2_00100_D_A497_FIXED_CENTER_PSD_CLOSURE.md). It changes
the current register from 198/33 to 200/31, with **147 complete additions after
the first 53**. The remaining families are **A5, B15, C8, D3**.

No original ID or path changes. No positional-root exclusion or roadmap-gate
closure is inferred. The same 32-mask ledger remains 8/24, and the same 7,915
positional-root IDs retain their historical 5,838 closed-Q exclusions and
2,077 OPEN entries. The other 31 current-mask originals and every other OPEN
mask still require complete proofs; internal C or A tiles earn no ledger credit.
