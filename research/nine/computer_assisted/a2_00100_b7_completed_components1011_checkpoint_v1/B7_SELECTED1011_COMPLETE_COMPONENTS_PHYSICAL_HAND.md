# B7: complete G/I branch and negative-F half

The complete retained cover of original `negative-7c60be8b07a358e9` in mask `001/00` now has 1,011 domains, 543 excluded terminal domains, and 43 OPEN terminal domains. This attachment records two completed components. The original remains OPEN and receives zero additional original-cell or mask credit.

## Original physical scope

The immutable original path is `[["angle",3,0],["angle_cut",[0,"0"],0],["position_cut",[11,"1/2"],0],["f_side_escape",[5,7],[2]]]`. Every domain retains all nine distinct original squares, all 36 corner conditions, all 36 physical pairs, the five cones, actual AB/BC/EF/FG, strictly weak CD, and the original H/I labels. The claim is for q < Q = 1105/256. No global classification at closed Q is asserted.

## Component 814: the original G-axis positive G/I branch

This component begins at the original H/I proxy [1,-1] and G/I separating-axis choice [G,0,+1]. Two closed cuts on the original F coordinate, y_F = -3/64 and y_F = 3/64, cover it by a lower complement, a central strip, and an upper complement. The lower complement 953 is excluded by its exact terminal. The central box 955 has squared center norm at most 149/2048, below (27/100)^2 by exactly 187/1280000; the accepted all-nine central-capacity theorem excludes that entire closed box.

The upper complement 956 has the complete eight-way separating-axis cover for the actual C/I pair [2,8]: either original square supplies axis 0 or 1, with both signs. All eight children 1003–1010 are excluded. Component 814 therefore has 13 domains and 10 excluded terminals, with no OPEN leaf.

## Component 993: the negative-F half under 949

Within the G/I choice [G,0,-1], the closed cut x_F = 0 at domain 949 retains both halves. The x_F <= 0 half 993 has the complete eight-way separating-axis cover for the actual F/I pair [5,8]. All eight children 994–1001 are excluded. This half has nine domains and eight excluded terminals. Its x_F >= 0 companion 1002 stays OPEN; the other old complement 952 is retained byte-for-byte and also stays OPEN. Whole component 813 remains OPEN.

## Literal terminal table

The accompanying JSON contains every literal terminal row, positive integer weight, rational residual coefficient, absolute bound, exact reserve, and terminal recipe for the following 18 leaves. These sums are reconstructed independently here; the fresh full-cover checker separately validates every printed row against the unchanged physical decoder. Numerical discovery points and producer closure flags are not premises.

| Component | Terminal | Parent | Last choice | Rounds | Deductions | Exact terminal |
|---:|---:|---:|---|---:|---:|---|
| 814 | 953 | 814 | 0 | 2 | 363 | positive_exact_reserve (reserve >= 1) |
| 814 | 955 | 954 | 0 | 0 | 0 | accepted_all_nine_original_F_center_box_exclusion_27_100 |
| 814 | 1003 | 956 | [2, 0, -1] | 0 | 0 | positive_exact_reserve (reserve >= 1/1024) |
| 814 | 1004 | 956 | [2, 0, 1] | 1 | 215 | proved_empty_analytic_frame |
| 814 | 1005 | 956 | [2, 1, -1] | 1 | 218 | positive_exact_reserve (reserve >= 1) |
| 814 | 1006 | 956 | [2, 1, 1] | 0 | 0 | positive_exact_reserve (reserve >= 1/128) |
| 814 | 1007 | 956 | [8, 0, -1] | 1 | 226 | proved_frame_contradiction |
| 814 | 1008 | 956 | [8, 0, 1] | 1 | 174 | positive_exact_reserve (reserve >= 1) |
| 814 | 1009 | 956 | [8, 1, -1] | 1 | 213 | positive_exact_reserve (reserve >= 1) |
| 814 | 1010 | 956 | [8, 1, 1] | 0 | 0 | positive_exact_reserve (reserve >= 1/256) |
| 993 | 994 | 993 | [5, 0, -1] | 0 | 0 | positive_exact_reserve (reserve >= 1/8) |
| 993 | 995 | 993 | [5, 0, 1] | 1 | 209 | positive_exact_reserve (reserve >= 1) |
| 993 | 996 | 993 | [5, 1, -1] | 1 | 207 | accepted_center_interval_terminal |
| 993 | 997 | 993 | [5, 1, 1] | 1 | 212 | positive_exact_reserve (reserve >= 1/512) |
| 993 | 998 | 993 | [8, 0, -1] | 1 | 213 | accepted_center_interval_terminal |
| 993 | 999 | 993 | [8, 0, 1] | 1 | 207 | positive_exact_reserve (reserve >= 1/512) |
| 993 | 1000 | 993 | [8, 1, -1] | 1 | 207 | positive_exact_reserve (reserve >= 1/512) |
| 993 | 1001 | 993 | [8, 1, 1] | 1 | 210 | positive_exact_reserve (reserve >= 1/512) |

## Preservation, replay, and limits

All 993 earlier domain records keep their identical initial state and complete record. Exactly 989 old payloads are byte-identical; the other four differ only in cover edges or propagated candidate status. The already completed components 4, 260, 816, 818, and 820 are retained and independently replayed. All shared closed faces remain covered.

Fresh replay checked 416 bound rounds, 67065 deductions, 246778 printed rows, 2118 relative-support chord rows, 131 all-nine central rows, and 13 original-F central-box terminal occurrences over the full retained original.

Manifest SHA-256: `bb5aaf7a3d16638b5ed6c7a70c947407c1c470e777468c4d0e0549b16ca6a449`. Fresh report SHA-256: `0f7007a02876f18701a532cf1bf82c038557c5eabfb5566a35080b7c48b862ba`. Literal table SHA-256: `500eff3ba2fe5ce420f0c57ae4295986ca28d3168e1f13e85f987ff71787ee8f`. The accepted central theorem has SHA-256 `b0b2858252d2a3bee205d40f97958da445ece0a3a4e05bd693340b2e94884257`, with source archive SHA-256 `baf3da1dbcbffdbc9d0a4723bc9ec8db4ef5fc0d62e7d29a455178ac435ce54a`.

A portable copied-input replay and independent attachment review remain publication gates. This attachment grants zero original credit. No Lean, Lake, compilation, or CI is used.
