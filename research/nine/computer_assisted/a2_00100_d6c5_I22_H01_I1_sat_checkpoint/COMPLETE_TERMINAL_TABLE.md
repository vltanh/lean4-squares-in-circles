# Complete physical terminal table for I22 / H01 / I-slope quarter 1

D quarters cover [0,1] including all shared endpoints. SAT choices use original indices A=0 through I=8.
Every positive reserve below is a proved dyadic lower bound for the exact reserve printed in the corresponding node record.
The explicit tree files contain every multiplier, original physical row and complete eight-way child union.

| D quarter | Node | Parent | Choice (owner,axis,sign) | Rounds | Deductions | Rows | Conclusion |
|---|---:|---:|---|---:|---:|---:|---|
| 0 | 0 | None | None | 0 | 0 | 0 | complete eight-way cover of pair [6, 8] |
| 0 | 1 | 0 | [6, 0, -1] | 0 | 0 | 40 | reserve >= 1/256 |
| 0 | 2 | 0 | [6, 0, 1] | 0 | 0 | 1 | reserve >= 1 |
| 0 | 3 | 0 | [6, 1, -1] | 1 | 203 | 295 | complete eight-way cover of pair [4, 7] |
| 0 | 4 | 3 | [4, 0, -1] | 0 | 0 | 1 | reserve >= 1 |
| 0 | 5 | 3 | [4, 0, 1] | 0 | 0 | 39 | reserve >= 1/128 |
| 0 | 6 | 3 | [4, 1, -1] | 1 | 215 | 275 | reserve >= 1/4096 |
| 0 | 7 | 3 | [4, 1, 1] | 0 | 0 | 1 | reserve >= 1 |
| 0 | 8 | 3 | [7, 0, -1] | 0 | 0 | 1 | reserve >= 1 |
| 0 | 9 | 3 | [7, 0, 1] | 0 | 0 | 1 | reserve >= 1/32 |
| 0 | 10 | 3 | [7, 1, -1] | 1 | 215 | 276 | reserve >= 1/4096 |
| 0 | 11 | 3 | [7, 1, 1] | 0 | 0 | 1 | reserve >= 1 |
| 0 | 12 | 0 | [6, 1, 1] | 0 | 0 | 1 | reserve >= 1/2 |
| 0 | 13 | 0 | [8, 0, -1] | 0 | 0 | 14 | reserve >= 1/64 |
| 0 | 14 | 0 | [8, 0, 1] | 0 | 0 | 1 | reserve >= 1/2 |
| 0 | 15 | 0 | [8, 1, -1] | 1 | 202 | 289 | complete eight-way cover of pair [4, 7] |
| 0 | 16 | 15 | [4, 0, -1] | 0 | 0 | 1 | reserve >= 1/2 |
| 0 | 17 | 15 | [4, 0, 1] | 0 | 0 | 41 | reserve >= 1/128 |
| 0 | 18 | 15 | [4, 1, -1] | 1 | 222 | 205 | proved_empty_original_angle_interval |
| 0 | 19 | 15 | [4, 1, 1] | 0 | 0 | 1 | reserve >= 1 |
| 0 | 20 | 15 | [7, 0, -1] | 0 | 0 | 1 | reserve >= 1 |
| 0 | 21 | 15 | [7, 0, 1] | 0 | 0 | 27 | reserve >= 1/32 |
| 0 | 22 | 15 | [7, 1, -1] | 1 | 222 | 204 | proved_empty_original_angle_interval |
| 0 | 23 | 15 | [7, 1, 1] | 0 | 0 | 1 | reserve >= 1 |
| 0 | 24 | 0 | [8, 1, 1] | 0 | 0 | 1 | reserve >= 1 |
| 1 | 0 | None | None | 0 | 0 | 0 | complete eight-way cover of pair [6, 8] |
| 1 | 1 | 0 | [6, 0, -1] | 1 | 187 | 310 | reserve >= 1/128 |
| 1 | 2 | 0 | [6, 0, 1] | 0 | 0 | 1 | reserve >= 1/2 |
| 1 | 3 | 0 | [6, 1, -1] | 0 | 0 | 45 | reserve >= 1/1024 |
| 1 | 4 | 0 | [6, 1, 1] | 0 | 0 | 1 | reserve >= 1/4 |
| 1 | 5 | 0 | [8, 0, -1] | 0 | 0 | 43 | reserve >= 1/512 |
| 1 | 6 | 0 | [8, 0, 1] | 0 | 0 | 1 | reserve >= 1/2 |
| 1 | 7 | 0 | [8, 1, -1] | 0 | 0 | 43 | reserve >= 1/4096 |
| 1 | 8 | 0 | [8, 1, 1] | 0 | 0 | 1 | reserve >= 1 |
| 2 | 0 | None | None | 0 | 0 | 0 | complete eight-way cover of pair [6, 8] |
| 2 | 1 | 0 | [6, 0, -1] | 1 | 191 | 279 | reserve >= 1/32 |
| 2 | 2 | 0 | [6, 0, 1] | 0 | 0 | 1 | reserve >= 1/2 |
| 2 | 3 | 0 | [6, 1, -1] | 0 | 0 | 43 | reserve >= 1/256 |
| 2 | 4 | 0 | [6, 1, 1] | 0 | 0 | 1 | reserve >= 1/8 |
| 2 | 5 | 0 | [8, 0, -1] | 1 | 236 | 154 | proved_empty_original_angle_interval |
| 2 | 6 | 0 | [8, 0, 1] | 0 | 0 | 1 | reserve >= 1/2 |
| 2 | 7 | 0 | [8, 1, -1] | 0 | 0 | 37 | reserve >= 1/256 |
| 2 | 8 | 0 | [8, 1, 1] | 0 | 0 | 1 | reserve >= 1 |
| 3 | 0 | None | None | 0 | 0 | 0 | complete eight-way cover of pair [6, 8] |
| 3 | 1 | 0 | [6, 0, -1] | 1 | 192 | 269 | reserve >= 1/32 |
| 3 | 2 | 0 | [6, 0, 1] | 0 | 0 | 1 | reserve >= 1/2 |
| 3 | 3 | 0 | [6, 1, -1] | 0 | 0 | 38 | reserve >= 1/512 |
| 3 | 4 | 0 | [6, 1, 1] | 0 | 0 | 1 | reserve >= 1/8 |
| 3 | 5 | 0 | [8, 0, -1] | 0 | 0 | 40 | reserve >= 1/2048 |
| 3 | 6 | 0 | [8, 0, 1] | 0 | 0 | 1 | reserve >= 1/2 |
| 3 | 7 | 0 | [8, 1, -1] | 0 | 0 | 31 | reserve >= 1/256 |
| 3 | 8 | 0 | [8, 1, 1] | 0 | 0 | 1 | reserve >= 1 |
