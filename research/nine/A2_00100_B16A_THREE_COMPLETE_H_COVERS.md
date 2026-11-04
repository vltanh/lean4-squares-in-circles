# Three complete H covers inside the original B16a cell

## Scope and immutable caller

This packet excludes the complete fixed I rectangles I12, I13 and I23 inside the unchanged original `negative-16a2fc93c8d133f0`. It does not exclude the whole original cell or a mask. The literal original path is:

```json
[["angle",3,0],["angle_cut",[0,"0"],0],["position_cut",[11,"1/2"],1],["f_side_escape",[5,7],[3]]]
```

The independently replayed common prefix has SHA256 `69ddd2dcc5383c3259187588a890ddadb4a6545e8bdcc11e653bdfb8bb6b3886`. It retains all nine original physical unit-square frames, all 36 original corners, all 36 original pairs, and the original strict C–D caller. Its five exact rounds contain 199 deductions and 582 printed rows, following 30 coordinate deductions. No new physical square or independent corner vector is introduced.

## Complete closed rectangles

Original I is divided into four equal closed intervals on each center coordinate. The three selected products are:

| Original I rectangle | I x interval | I y interval |
|---|---|---|
| I12 | [-3112321/4194304, -163627/2097152] | [0, 91/120] |
| I13 | [-3112321/4194304, -163627/2097152] | [91/120, 91/60] |
| I23 | [-163627/2097152, 2457813/4194304] | [91/120, 91/60] |

For every selected I rectangle, original H retains the common parent box

\[[-1474347/1048576,17/64]\times[-120173/655360,311927/262144].\]

For H index `(h_x,h_y)`, divide its x interval into two equal closed pieces and its y interval into four equal closed pieces. The exact product has endpoints `L+(U−L)h/m` and `L+(U−L)(h+1)/m`, with `m=2` or `4`. All eight addresses are required for each I rectangle. Every equality face remains in the adjoining pieces; the proof assumes no clearance from a boundary and no exclusion learned from an earlier sibling. All other original coordinate, scalar, angle and pair-difference facts are retained.

## Exact terminal table

The bound columns count only local induction work. A positive entry is a rational lower bound on the checked residual reserve, not a numerical solver margin. “Interval” means an independently rebuilt physical interval contradiction; no fictitious reserve is assigned. Exact endpoints, complete reserve fractions, certificate hashes and source paths are in `COVER_TABLE.json`.

| I | H | Accepted route | Local rounds | Deductions | Premise rows | Terminal rows | Positive reserve at least |
|---|---|---|---:|---:|---:|---:|---|
| I12 | H00 | direct affine | 0 | 0 | 0 | 4 | 295477/250000 |
| I12 | H01 | direct affine | 0 | 0 | 0 | 0 | Interval |
| I12 | H02 | exact bound induction | 1 | 124 | 191 | 3 | 23369/20000 |
| I12 | H03 | direct affine | 0 | 0 | 0 | 4 | 298431/250000 |
| I12 | H10 | direct affine | 0 | 0 | 0 | 4 | 293781/250000 |
| I12 | H11 | direct affine | 0 | 0 | 0 | 0 | Interval |
| I12 | H12 | direct affine | 0 | 0 | 0 | 3 | 1122541/1000000 |
| I12 | H13 | direct affine | 0 | 0 | 0 | 3 | 551487/500000 |
| I13 | H00 | direct affine | 0 | 0 | 0 | 11 | 1753/125000 |
| I13 | H01 | exact bound induction | 1 | 104 | 213 | 21 | 1367/125000 |
| I13 | H02 | exact bound induction | 1 | 119 | 184 | 5 | 1403473/1000000 |
| I13 | H03 | direct affine | 0 | 0 | 0 | 0 | Interval |
| I13 | H10 | exact bound induction | 2 | 232 | 417 | 30 | 39/250000 |
| I13 | H11 | exact bound induction | 2 | 234 | 390 | 28 | 2429/125000 |
| I13 | H12 | direct affine | 0 | 0 | 0 | 3 | 3607/125000 |
| I13 | H13 | direct affine | 0 | 0 | 0 | 0 | Interval |
| I23 | H00 | direct affine | 0 | 0 | 0 | 11 | 1753/125000 |
| I23 | H01 | exact bound induction | 1 | 90 | 175 | 16 | 2633/250000 |
| I23 | H02 | exact bound induction | 1 | 111 | 178 | 4 | 548463/500000 |
| I23 | H03 | direct affine | 0 | 0 | 0 | 4 | 298431/250000 |
| I23 | H10 | exact bound induction | 2 | 234 | 391 | 22 | 9727/1000000 |
| I23 | H11 | exact bound induction | 3 | 398 | 513 | 28 | 5909/200000 |
| I23 | H12 | exact bound induction | 2 | 258 | 376 | 10 | 3087/100000 |
| I23 | H13 | direct affine | 0 | 0 | 0 | 4 | 14419/12500 |

There are 14 direct terminals and 10 bound-induction terminals. The latter contain 1,904 exact deductions and 3,028 induction-row occurrences, followed by 167 terminal-row occurrences. Direct terminals use another 51 rows. Thus the local proof checks 3,246 row occurrences in all. The common original prefix is counted separately once.

## Why the affine certificates exclude each member

Every printed inequality is independently reconstructed from the same physical caller and the certified interval state. In a terminal, nonnegative rational weights produce `c·z ≤ d`. The checker has rational absolute bounds `|z_j| ≤ M_j`, so `c·z ≥ −Σ_j M_j|c_j|`. A strictly positive rational reserve `−d−Σ_j M_j|c_j|` is therefore a contradiction. The residual coefficients are paid exactly rather than assumed to vanish. Numerical LP solutions supply only candidate weights.

The same exact weighted-row calculation supplies each improved coordinate or pair-difference bound in an induction round. All printed premises and weights are checked before that bound is retained. Unit-frame algebra then derives the certified angle and support intervals. Each subsequent round is reconstructed from the proved preceding state; a saved producer endpoint is never itself accepted as a premise. The complete cover master compares each terminal’s original prefix hash, literal path, exact I rectangle and exact H rectangle before attaching it to the declared partition.

## Physical energy premises actually used

Three previously accepted physical inequalities occur in the printed proof. For any three original nonoverlapping unit squares, the sum of the three squared center distances is at least `7/2`. Its complete proof is freshly replayed by the master: two independent geometric evaluators, all 128 angular triangles and 1,877 exact row identities. For any four pairwise unit-separated planar centers, the sum of their six squared pair distances is at least `8`. For any selected `k` physical unit squares and rational matrix `B`, with `W=BᵀB`, the area-moment inequality gives

\[\sum_{i<j}(c_i-c_j)^T W(c_i-c_j)\ge \frac{7k^3|\det B|}{44}-\frac{k^2\operatorname{tr}(W)}{12}.\]

Each quadratic energy lower bound is converted to a necessary linear inequality by exact secant upper bounds over the current certified difference intervals. These inequalities remain valid on the full closed interval box; no unproved choice of pair-separation direction is used. The area row here uses six originals A,B,E,F,H,I and the identity matrix B.

Across the selected 24 leaves there are 25 three-square-energy occurrences, three four-center-energy occurrences and one square-area occurrence: 29 printed occurrences in total. An occurrence means one printed row in one local round or terminal, even if its label appears elsewhere. There are 10 distinct row labels and 27 distinct printed linear inequalities when coefficient and right-hand-side bytes are included. The following complete list makes the counting convention explicit:

| Printed row label | Occurrences |
|---|---:|
| `planar_four_center_sum_0_1_4_7` | 1 |
| `planar_four_center_sum_4_5_7_8` | 2 |
| `square_area_moment_secant_0-1-4-5-7-8_1_0_0_1` | 1 |
| `three_square_center_energy_0_1_4_000` | 1 |
| `three_square_center_energy_0_1_7_000` | 3 |
| `three_square_center_energy_0_4_7_000` | 7 |
| `three_square_center_energy_3_6_8_000` | 2 |
| `three_square_center_energy_4_5_8_000` | 1 |
| `three_square_center_energy_4_7_8_000` | 4 |
| `three_square_center_energy_5_7_8_000` | 7 |

The actual theorem texts and independent reviews remain in the frozen context. Their bindings are recorded below and in `PHYSICAL_PROOF_BINDINGS.json`. No energy inequality is inferred solely from a numerical report.

## Source and replay binding

- Exact full-cover master: `01b5edcc1943fa1143a581655a35d9d224d5d277e27e4cff8b04d0b710ce6886`.
- Frozen 240-input manifest: `e18f4e4a5779d82c34cbb540e1d066532143a1ec9469715d3b9c8a877dce5c57`.
- Completed exact whole-cover report: `ec8a8496b0415cb9e84a691f3601a11c442f8188c11dd7ca9d3a9884fb0f7618`.
- Independent source/24-rectangle attachment review: `c9340f42447dff6c2c9bf5ebdba4abbdca0650cd2b1a538b28d876d850aa8638`.

The complete runtime used only the portable context and independently implemented exact arithmetic. It rehashed every frozen input after all sibling proofs and audited local imports. The outputs establish three complete original-I rectangles; the original cell and mask counters remain unchanged.

## Committed portable checkpoint

[Archive parts and inventory](computer_assisted/a2_00100_b16a_three_I_complete_H_manifest.json) ·
[Accepted exact assembly](computer_assisted/a2_00100_b16a_three_I_complete_H_exact_replay.json) ·
[Exact cover table](computer_assisted/a2_00100_b16a_three_I_complete_H_table.json) ·
[Root source, hand and archive review](computer_assisted/a2_00100_b16a_three_I_root_review.json).

Concatenate the three archive parts in the declared order and extract the xz
tar. In `b16a_three_complete_H_checkpoint`, run
`python -B -S verify_b16a_three_complete_H_covers.py --report FRESH_THREE_COMPLETE_H_REPLAY.json`.
The packet preserves the accepted 240-input core, all physical proof bindings,
the complete hand/table, and both independent source and hand reviews.
All 259 regular archive entries passed an independent root hash audit against
the 258-file member inventory plus that inventory itself. PAX path extensions
preserve long historical filenames; no external links occur.

The root read the entire exact cover master and physical hand proof and
verified the archive and source bytes. The independently accepted arithmetic
is preserved; packaging and root archive review do not claim a repeated full
weighted-row replay. Its local accounting is 1,904 deductions, 3,028 premise
rows, 167 bound-terminal rows and 51 direct-terminal rows. The common original
prefix remains a separate antecedent.

The original-cell ledger remains 218 CLOSED / 13 OPEN and the mask ledger
8 CLOSED / 24 OPEN. I12, I13 and I23 are complete fixed rectangles inside
B16a; the whole original remains OPEN. No positional-root or roadmap credit
is added. No Lean, Lake or CI was run.
