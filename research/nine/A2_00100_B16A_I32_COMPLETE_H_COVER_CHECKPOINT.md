# Complete original I32 rectangle inside B16a

## Original physical caller

This packet excludes the complete fixed I32 rectangle inside the unchanged original `negative-16a2fc93c8d133f0`. It awards zero original-cell and mask credit. The immutable original path is:

```json
[["angle",3,0],["angle_cut",[0,"0"],0],["position_cut",[11,"1/2"],1],["f_side_escape",[5,7],[3]]]
```

The original prefix is `69ddd2dcc5383c3259187588a890ddadb4a6545e8bdcc11e653bdfb8bb6b3886`. Its independent five-round replay proves 199 deductions and 582 printed rows after 30 coordinate deductions. All stages retain the same nine physical unit-square frames, 36 original corners, 36 original pairs and strict C–D caller. The original-I and original-D slopes belong to those frames.

## Complete closed position and angle covers

I32 is the closed product `[2457813/4194304, 5/4] × [0, 91/120]`. Original H has the parent box `[-1474347/1048576,17/64] × [-120173/655360,311927/262144]`. Its first coordinate is divided into two equal closed halves and its second into four equal closed quarters. The eight products below cover that whole box, retaining shared endpoints in both adjacent members.

| H | H x interval | H y interval | Accepted route | Rounds | Deductions | Premise rows | Terminal rows |
|---|---|---|---|---:|---:|---:|---:|
| H00 | [-1474347/1048576, -1195819/2097152] | [-120173/655360, 838597/5242880] | direct affine | 0 | 0 | 0 | 11 |
| H01 | [-1474347/1048576, -1195819/2097152] | [838597/5242880, 1319289/2621440] | bound induction | 1 | 107 | 173 | 16 |
| H02 | [-1474347/1048576, -1195819/2097152] | [1319289/2621440, 4438559/5242880] | bound induction | 1 | 126 | 159 | 4 |
| H03 | [-1474347/1048576, -1195819/2097152] | [4438559/5242880, 311927/262144] | direct affine | 0 | 0 | 0 | 3 |
| H10 | [-1195819/2097152, 17/64] | [-120173/655360, 838597/5242880] | complete I4 with D4 subcovers | 21 | 3876 | 4772 | 181 |
| H11 | [-1195819/2097152, 17/64] | [838597/5242880, 1319289/2621440] | complete I4 with D4 subcovers | 44 | 7794 | 9979 | 292 |
| H12 | [-1195819/2097152, 17/64] | [1319289/2621440, 4438559/5242880] | complete I4 with D4 subcovers | 20 | 3555 | 4336 | 192 |
| H13 | [-1195819/2097152, 17/64] | [4438559/5242880, 311927/262144] | direct affine | 0 | 0 | 0 | 3 |

H00, H03 and H13 close directly. H01 and H02 close after one local bound round. H10, H11 and H12 retain their independently proved six-round OPEN states and divide the certified original-I slope interval into four equal closed quarters. The remaining I quarters are H10/1, H11/0, H11/1, H11/3 and H12/1. Each retains its complete three-round state, then divides its certified original-D slope interval into four equal closed quarters. All twenty D members close. Seventeen use their BASE3 records, two finish at round five after a literal 3→6 continuation, and one finishes at round eight after a literal 3→6→9 continuation.

For any certified interval `[a,b]`, quarter `j` is exactly `[a+(b−a)j/4,a+(b−a)(j+1)/4]`, for `j=0,1,2,3`. Every other certified center, scalar, angle and pair-difference bound is retained. A continuation changes no domain and preserves its previous rounds literally. The complete-cover gates require every sibling, including touching faces. Each child is attached to its exact parent hash, immutable original path and original I/H rectangles. Earlier sibling exclusions are never used as assumptions for later siblings.

## Detailed bound terminal table

A displayed positive reserve is a rational lower bound on the independently checked residual reserve. Empty angle or analytic frame terminals have no invented reserve. The JSON table retains every full exact fraction, original angle interval, certificate path and hash.

| H | I quarter | D quarter | Rounds | Deductions | Premise rows | Terminal rows | Reserve at least / terminal |
|---|---|---|---:|---:|---:|---:|---|
| H01 | — | — | 1 | 107 | 173 | 16 | 2633/250000 |
| H02 | — | — | 1 | 126 | 159 | 4 | 548463/500000 |
| H10 | 0 | — | 3 | 638 | 596 | 0 | empty original angle |
| H10 | 1 | 0 | 1 | 210 | 205 | 43 | 2843/1000000 |
| H10 | 1 | 1 | 2 | 407 | 479 | 41 | 127/1000000 |
| H10 | 1 | 2 | 3 | 615 | 686 | 17 | 12469/500000 |
| H10 | 1 | 3 | 1 | 216 | 233 | 33 | 573/500000 |
| H10 | 2 | — | 1 | 205 | 250 | 18 | 2049/1000000 |
| H10 | 3 | — | 1 | 209 | 201 | 29 | 6667/500000 |
| H11 | 0 | 0 | 1 | 203 | 187 | 5 | 17373/1000000 |
| H11 | 0 | 1 | 2 | 402 | 434 | 0 | empty analytic frame |
| H11 | 0 | 2 | 5 | 954 | 1132 | 40 | 119/250000 |
| H11 | 0 | 3 | 3 | 610 | 644 | 0 | empty analytic frame |
| H11 | 1 | 0 | 1 | 196 | 205 | 22 | 171/500000 |
| H11 | 1 | 1 | 5 | 971 | 1188 | 38 | 1217/1000000 |
| H11 | 1 | 2 | 8 | 1513 | 1892 | 0 | empty analytic frame |
| H11 | 1 | 3 | 2 | 397 | 463 | 31 | 353/1000000 |
| H11 | 2 | — | 2 | 353 | 486 | 22 | 9193/500000 |
| H11 | 3 | 0 | 0 | 0 | 0 | 32 | 7719/1000000 |
| H11 | 3 | 1 | 0 | 0 | 0 | 32 | 1527/250000 |
| H11 | 3 | 2 | 0 | 0 | 0 | 34 | 4789/1000000 |
| H11 | 3 | 3 | 0 | 0 | 0 | 36 | 5971/1000000 |
| H12 | 0 | — | 3 | 590 | 661 | 35 | 13417/1000000 |
| H12 | 1 | 0 | 1 | 220 | 179 | 42 | 4443/250000 |
| H12 | 1 | 1 | 1 | 211 | 242 | 31 | 6201/1000000 |
| H12 | 1 | 2 | 1 | 212 | 229 | 33 | 4369/500000 |
| H12 | 1 | 3 | 1 | 228 | 177 | 34 | 13351/500000 |
| H12 | 2 | — | 2 | 403 | 380 | 0 | empty original angle |
| H12 | 3 | — | 2 | 407 | 393 | 17 | 19317/500000 |

The three direct certificates have these positive rational reserve floors:

| H | Reserve at least |
|---|---|
| H00 | 1753/125000 |
| H03 | 298431/250000 |
| H13 | 551487/500000 |

## Five exact angle/frame contradictions

The following intervals are derived from replayed scalar bounds and exact unit-frame algebra. The strictly positive difference between each lower and upper endpoint proves the stated interval empty. For the three analytic-frame cases, full variable index 24 is the original G-frame component `alpha_G`. Producer final fields from an early exit are never treated as newly derived bounds.

| H / I quarter / D quarter | Original quantity | Lower bound | Upper bound | Positive gap |
|---|---|---|---|---|
| H10 / 0 / — | slope_G | `198109285768863/281474976710656` | `22852470381045/140737488355328` | `152404345006773/281474976710656` |
| H11 / 0 / 1 | alpha_G | `124804882538473/140737488355328` | `906673/1048576` | `3113292439529/140737488355328` |
| H11 / 0 / 3 | alpha_G | `249079020269313/281474976710656` | `230421/262144` | `1666355441409/281474976710656` |
| H11 / 1 / 2 | alpha_G | `17132971997635/17592186044416` | `454153/524288` | `1894126041539/17592186044416` |
| H12 / 2 / — | slope_E | `-972808593825/2199023255552` | `-42879861290901/70368744177664` | `11749986288501/70368744177664` |

The two empty-angle cases also have an independently checked unit-circle contradiction. For G in H10/I-quarter0, the certified upper bound on `alpha_G²+beta_G²` is `381761133629/549755813888`, leaving deficit `167994680259/549755813888`. For E in H12/I-quarter2, the upper bound is `981749669409/1099511627776`, leaving deficit `117761958367/1099511627776`. Both deficits are strictly positive, contradicting the original unit-frame identity.

## Exact accounting and physical premises

There are 37 distinct bound records: 29 terminal records and eight OPEN ancestor records. The OPEN records provide necessary states only: three common H6 states and five common I3 states. Each is counted once. A flattened continued D record already contains its earlier rounds, so saved D3/D6 predecessors are retained for exact continuation and provenance checks without counting those rounds again. The resulting local totals are 87 rounds, 15,458 deductions, 19,419 premise-row occurrences and 685 bound-terminal rows. The direct certificates add 17 rows, giving 20,121 local row occurrences. The original prefix is separate and replayed once.

Every printed inequality is independently reconstructed from the physical caller and current certified state. Nonnegative rational weights give `c·z≤d`; rational bounds `|z_j|≤M_j` give `c·z≥−ΣM_j|c_j|`. A positive reserve `−d−ΣM_j|c_j|` is therefore contradictory. Every coefficient residual is paid. The same weighted calculation proves each scalar or pair-difference improvement before exact frame algebra produces the next angle and support intervals. Solvers only discover candidate weights.

For any three nonoverlapping physical unit squares, the accepted center-energy lower bound is `7/2`. The complete 21-input theorem packet is freshly replayed by the master, including two geometric evaluators, 128 angular triangles and 1,877 row identities. Four pairwise unit-separated planar centers have six-pair squared-distance sum at least `8`. For any selected `k` physical unit squares and rational matrix `B`, with `W=BᵀB`, the square-area theorem gives

\[\sum_{i<j}(c_i-c_j)^TW(c_i-c_j)\ge\frac{7k^3|\det B|}{44}-\frac{k^2\operatorname{tr}(W)}{12}.\]

Each energy lower bound is converted to a necessary affine inequality using exact secant upper bounds on the current certified difference intervals. This is valid on the entire closed box without assuming a separating direction. All full hand proofs and independent row-conversion reviews are retained under the 12 file hashes in `PHYSICAL_PROOF_BINDINGS.json`.

The selected records contain 199 printed energy occurrences: 199 three-square, 0 four-center and 0 square-area. An occurrence means one printed row in one round or terminal; common ancestors are counted once. There are 10 distinct row labels and 160 distinct printed linear inequalities when the label, coefficients and right side are all included. Full literals and locations are in `COVER_TABLE.json`.

| Printed energy label | Occurrences |
|---|---:|
| `three_square_center_energy_0_1_4_000` | 1 |
| `three_square_center_energy_0_1_7_000` | 2 |
| `three_square_center_energy_0_4_7_000` | 62 |
| `three_square_center_energy_1_4_7_000` | 1 |
| `three_square_center_energy_1_7_8_000` | 4 |
| `three_square_center_energy_2_3_8_000` | 7 |
| `three_square_center_energy_3_6_8_000` | 22 |
| `three_square_center_energy_4_5_7_000` | 38 |
| `three_square_center_energy_5_6_8_000` | 15 |
| `three_square_center_energy_5_7_8_000` | 47 |

## Frozen acceptance bindings

- Complete-cover master: `22a512b2b4aafd10c41d79edf123dbc93ccc540b4c00ee16be8f2803ee957a94`.
- Frozen 507-input core manifest: `33272ed096ceb3f2dab6a16570ebe080a84677a033be5690ee63bfbdbf7bfc72`.
- Strict portable full-cover replay: `69f12c27e86f13f37d02373eecce5834b0601db84f741efa6aee74a9c083a977`.
- Independent actual-input attachment review: `827ad735f6b3269f47c8a3bf9e29ee1e5be16a2e4f8582d4af86ed8a0a0ce162`.

The complete replay audited local imports and rehashed every frozen source and earlier sibling dependency at the end. It imported no numerical optimizer. This proves one complete original-I rectangle; the original-cell and mask counts remain unchanged.

## Committed portable checkpoint

[Ordered archive parts and inventory](computer_assisted/a2_00100_b16a_I32_complete_H_manifest.json) ·
[Accepted complete exact replay](computer_assisted/a2_00100_b16a_I32_complete_H_replay.json) ·
[Exact cover and terminal table](computer_assisted/a2_00100_b16a_I32_complete_H_table.json) ·
[Physical proof bindings](computer_assisted/a2_00100_b16a_I32_physical_proof_bindings.json) ·
[Root source and hand review](computer_assisted/a2_00100_b16a_I32_root_review.json) ·
[Independent hand/table review](computer_assisted/a2_00100_b16a_I32_independent_hand_review.json) ·
[Root archive audit](computer_assisted/a2_00100_b16a_I32_root_archive_audit.json).

Concatenate the seven declared parts in order and extract the xz tar. In
`b16a_I32_complete_H_checkpoint`, a fresh independent replay is:

```bash
python -B -S -u verify_b16a_complete_H_with_slope_covers_v2.py I32_COMPLETE_H_COVER.json --report FRESH_I32_COMPLETE_H_REPLAY.json
```

The unchanged 507-input core, accepted exact report, complete physical
hand/table, source and attachment reviewers, theorem inputs and portable
checkers are included. The previously reviewed master is byte-identical.
The root read the complete result hand, checked all 507 inputs and twelve
physical bindings, recomputed all eight H rectangles and five strict empty
interval gaps, and checked both unit-frame square-sum deficits.
Every one of the 526 archive paths matched its declared source; the 124
internal hardlinks point to earlier identical regular payloads. The entire
xz stream and seven-part concatenation passed. These publication checks
make no claim of another weighted-arithmetic replay.

Together with the previous complete fixed-I proofs, fourteen of B16a's
sixteen original I rectangles are excluded. I21 and I22 remain OPEN.
B16a itself remains OPEN. The original-cell ledger is 218 CLOSED / 13 OPEN,
and the mask ledger is 8 CLOSED / 24 OPEN. No positional-root or roadmap
credit is added. No Lean, Lake or CI was run.
