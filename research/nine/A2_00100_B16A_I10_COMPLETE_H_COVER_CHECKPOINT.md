# Complete original I10 rectangle inside B16a

## Scope and original physical caller

This packet excludes the complete fixed I10 rectangle inside the unchanged original `negative-16a2fc93c8d133f0`. It awards zero original-cell or mask credit. The original path is:

```json
[["angle",3,0],["angle_cut",[0,"0"],0],["position_cut",[11,"1/2"],1],["f_side_escape",[5,7],[3]]]
```

The common original prefix is `69ddd2dcc5383c3259187588a890ddadb4a6545e8bdcc11e653bdfb8bb6b3886`. Its independent five-round replay verifies 199 deductions and 582 printed rows after 30 coordinate deductions. Every part of this proof retains the same nine physical unit-square frames, 36 original corners, 36 original pairs and strict C–D caller. Angle restrictions refer to these original frames.

## Complete position and angle covers

I10 is the original closed product `[-3112321/4194304, -163627/2097152] × [-91/60, -91/120]`. Original H retains the common parent box `[-1474347/1048576,17/64] × [-120173/655360,311927/262144]`. Its first coordinate is divided into two equal closed pieces and its second into four. The eight exact products below cover this whole box. A shared endpoint remains in both adjoining members.

| H address | H x interval | H y interval | Accepted route | Bound rounds | Deductions | Premise rows | Terminal rows |
|---|---|---|---|---:|---:|---:|---:|
| H00 | [-1474347/1048576, -1195819/2097152] | [-120173/655360, 838597/5242880] | direct affine | 0 | 0 | 0 | 5 |
| H01 | [-1474347/1048576, -1195819/2097152] | [838597/5242880, 1319289/2621440] | bound induction | 1 | 155 | 220 | 17 |
| H02 | [-1474347/1048576, -1195819/2097152] | [1319289/2621440, 4438559/5242880] | bound induction | 1 | 122 | 186 | 4 |
| H03 | [-1474347/1048576, -1195819/2097152] | [4438559/5242880, 311927/262144] | direct affine | 0 | 0 | 0 | 4 |
| H10 | [-1195819/2097152, 17/64] | [-120173/655360, 838597/5242880] | direct affine | 0 | 0 | 0 | 5 |
| H11 | [-1195819/2097152, 17/64] | [838597/5242880, 1319289/2621440] | complete I-angle4 | 9 | 1328 | 2276 | 106 |
| H12 | [-1195819/2097152, 17/64] | [1319289/2621440, 4438559/5242880] | complete I-angle4 with D-angle4 | 39 | 6478 | 10571 | 355 |
| H13 | [-1195819/2097152, 17/64] | [4438559/5242880, 311927/262144] | direct affine | 0 | 0 | 0 | 4 |

H00, H03, H10 and H13 close directly. H01 and H02 close after one local induction round. H11 and H12 first retain their independently proved six-round OPEN states. For each, the certified original-I slope interval is divided into four equal closed quarters. All four H11 quarters close. H12 quarters 0 and 3 close; its remaining quarters 1 and 2 each retain an independently proved three-round state, then divide that state’s original-D slope interval into four equal closed quarters. All eight D members close. The two hardest D members use literal same-domain 3→6→9 continuations and finish at round seven. No earlier sibling’s exclusion is a premise in a later sibling.

For an interval `[a,b]` and index `j=0,1,2,3`, the exact angle member is `[a+(b−a)j/4,a+(b−a)(j+1)/4]`. Every other certified scalar, center and pair-difference bound is retained. The master attaches each slope proof to the original H rectangle through its common six-round ancestor, checking the prefix hash, literal original path and exact I/H endpoints.

## Detailed terminal table

A reserve entry is a rational lower bound on the independently checked residual reserve. An analytic frame terminal has no assigned reserve. Complete exact intervals, full reserve fractions, source paths and hashes appear in `COVER_TABLE.json`.

| H | I quarter | D quarter | Local rounds | Deductions | Premise rows | Terminal rows | Reserve at least / terminal |
|---|---|---|---:|---:|---:|---:|---|
| H01 | — | — | 1 | 155 | 220 | 17 | 32853/500000 |
| H02 | — | — | 1 | 122 | 186 | 4 | 548463/500000 |
| H11 | 0 | — | 1 | 198 | 267 | 27 | 97/10000 |
| H11 | 1 | — | 1 | 200 | 233 | 25 | 3169/200000 |
| H11 | 2 | — | 1 | 215 | 215 | 21 | 1957/50000 |
| H11 | 3 | — | 0 | 0 | 0 | 33 | 393/250000 |
| H12 | 0 | — | 1 | 194 | 259 | 41 | 11967/1000000 |
| H12 | 1 | 0 | 2 | 366 | 471 | 45 | 11901/1000000 |
| H12 | 1 | 1 | 3 | 513 | 853 | 44 | 2889/1000000 |
| H12 | 1 | 2 | 7 | 1241 | 2017 | 26 | 4521/200000 |
| H12 | 1 | 3 | 7 | 1164 | 2081 | 34 | 641/250000 |
| H12 | 2 | 0 | 1 | 213 | 222 | 39 | 10077/500000 |
| H12 | 2 | 1 | 1 | 206 | 258 | 41 | 671/100000 |
| H12 | 2 | 2 | 2 | 444 | 468 | 0 | empty analytic frame |
| H12 | 2 | 3 | 2 | 430 | 507 | 41 | 17183/1000000 |
| H12 | 3 | — | 1 | 209 | 251 | 44 | 269/12500 |

The four direct H reserves have the following rational lower bounds:

| H | Reserve at least |
|---|---|
| H00 | 864403/500000 |
| H03 | 298431/250000 |
| H10 | 1558479/1000000 |
| H13 | 551487/500000 |

The H12/I-quarter2/D-quarter2 analytic terminal compares the same original I-frame scalar `g_I`: its proved lower bound is `227149/524288`, whereas the exact analytic upper bound from its certified slope interval is `60343715044415/140737488355328`. Their positive difference is `631130350529/140737488355328`. The checker derives both bounds from the replayed state; stale producer final fields are not used as a derived premise.

The twenty distinct bound records include sixteen terminal records and four OPEN ancestor records. The latter supply only certified necessary states and are counted once. Flattened D-continuation records already contain their earlier three and six rounds, so the saved predecessor files are retained as provenance and preflight inputs, without being counted a second time. There are 50 deduplicated local rounds, 8,083 deductions, 13,253 induction-row occurrences and 482 bound-terminal rows. The four direct terminals add 18 rows, giving 13,753 local row occurrences altogether. The common original prefix is separate and replayed once.

## Exact arithmetic and physical premises

Each printed inequality is independently reconstructed from the physical caller and current certified bounds. Nonnegative rational weights give `c·z≤d`; rational absolute bounds `|z_j|≤M_j` imply `c·z≥−ΣM_j|c_j|`. Thus a positive exact reserve `−d−ΣM_j|c_j|` proves contradiction. Every coefficient residual is paid. The analogous weighted calculation verifies each improved scalar or pair-difference bound before unit-frame algebra derives the next angle/support intervals. Numerical solvers provide candidate weights only.

The accepted three-square theorem gives center energy at least `7/2` for any three physical nonoverlapping unit squares. Its full 21-input packet is freshly replayed by the master: two geometric evaluators, 128 angular triangles and 1,877 row identities. Four pairwise unit-separated planar centers have six-pair squared-distance sum at least `8`. For any selected `k` physical unit squares and rational matrix `B`, writing `W=BᵀB`, the square-area theorem gives

\[\sum_{i<j}(c_i-c_j)^TW(c_i-c_j)\ge\frac{7k^3|\det B|}{44}-\frac{k^2\operatorname{tr}(W)}{12}.\]

Each energy lower bound is converted to a necessary affine row using exact secant upper bounds over the current certified pair-difference intervals. These rows are valid on the whole closed box without choosing an unproved separation direction. Full theorem texts and independent row reviews remain in the frozen context and are bound by `PHYSICAL_PROOF_BINDINGS.json`.

Across the selected twenty bound records and four direct certificates there are 73 printed energy occurrences: 73 three-square, 0 four-center and 0 square-area. A printed occurrence is one row in one local round or terminal. There are 5 distinct labels and 58 distinct printed linear inequalities when label, coefficients and right-hand side are included. Common ancestor records are counted once. The complete row-label accounting is:

| Printed row label | Occurrences |
|---|---:|
| `three_square_center_energy_0_1_7_000` | 1 |
| `three_square_center_energy_0_4_7_000` | 2 |
| `three_square_center_energy_1_2_8_000` | 38 |
| `three_square_center_energy_1_4_7_000` | 1 |
| `three_square_center_energy_4_5_7_000` | 31 |

## Source and acceptance binding

- Exact full-cover master: `22a512b2b4aafd10c41d79edf123dbc93ccc540b4c00ee16be8f2803ee957a94`.
- Frozen 409-input manifest: `8512984085432357c328d4ef0e1ad939c51e5f23a81ac172421f6c7580fa54fa`.
- Complete strict portable replay: `3ece1bd114c1478bac555a8685adbaa0ea690919884d4d03926eb786ceebfbaa`.
- Independent eight-address/source attachment review: `c41b6526be3ba72bbeca69be4820cdf9ae2a7de8fdeae6f3c69e205c6432d763`.

The runtime checked every frozen input after the complete sibling assembly and audited all local imports. It imported no numerical optimizer. This establishes one complete original-I rectangle and leaves original-cell and mask counts unchanged.

## Committed portable checkpoint

[Ordered archive parts and inventory](computer_assisted/a2_00100_b16a_I10_complete_H_manifest.json) ·
[Accepted complete exact replay](computer_assisted/a2_00100_b16a_I10_complete_H_replay.json) ·
[Exact cover and terminal table](computer_assisted/a2_00100_b16a_I10_complete_H_table.json) ·
[Physical proof bindings](computer_assisted/a2_00100_b16a_I10_physical_proof_bindings.json) ·
[Root source and hand review](computer_assisted/a2_00100_b16a_I10_root_review.json) ·
[Independent hand/table review](computer_assisted/a2_00100_b16a_I10_independent_hand_review.json) ·
[Root archive audit](computer_assisted/a2_00100_b16a_I10_root_archive_audit.json).

Concatenate the six declared parts in order and extract the xz tar. In
`b16a_I10_complete_H_checkpoint_v2`, a fresh independent replay is:

```bash
python -B -S -u verify_b16a_complete_H_with_slope_covers_v2.py I10_COMPLETE_H_COVER.json --report FRESH_I10_COMPLETE_H_REPLAY.json
```

The unchanged 409-input core, accepted exact report, complete physical
hand/table, source and hand reviewers, theorem inputs and portable checkers
are included. The root read the entire master and hand proof, rehashed all
409 inputs and all twelve physical bindings, independently recomputed the
eight H rectangles, and checked every one of the 430 archived files against
its source. The whole xz stream and ordered part concatenation passed.
The archive checks do not claim another weighted-arithmetic replay.

Together with the earlier complete fixed-I proofs, thirteen of B16a's sixteen
original I rectangles are now excluded. I21, I22 and I32 remain OPEN at this
checkpoint. B16a itself remains OPEN. The original-cell ledger remains
218 CLOSED / 13 OPEN, and the mask ledger remains 8 CLOSED / 24 OPEN.
No positional-root or roadmap credit is added. No Lean, Lake or CI was run.
