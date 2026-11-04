# Dc71: exact14-of16 fixed-I checkpoint

**The original remains OPEN.** Fresh exact replay excludes14 of its16 fixed-I rectangles. Only I22 and I23 remain, with exactly10 explicit H6 OPEN obligations. This packet contributes zero original-cell and zero mask closures. The unchanged denominators are231 original cells and32 masks.

Original: `positive-c71dc2feef1abb0b`. Literal caller: `[["angle",3,1],["angle_cut",[0,"0"],1],["alternate_four_escape",[1,7],[2]]]`. Whole-original prefix: `3d5c6def24cd920103c2a26b81d4f898e135cda0b125a2eea87a8880fee840fa`.

All nine original physical unit squares, all36 corners, all36 physical pairs, the marked actual comparisons, every canonical predecessor guard and the strictly weak CD bit remain in force. The full continuous coverage and physical terminal arguments are in `DC71_ORIGINAL_COVER_HAND_PROOF_V3.md`; its supplementary accounting filename is corrected below to `reviewed_tools/audit_dc71_bound_accounting_v2.py`. The replayed core is unchanged.

## Exact replay and accounting

- Complete native relocated replay: `f55d8c114ace6ab658c59959b880cc480ab43067f4d7de92306d3d26bbc485b7`, elapsed 714.74 seconds.
- All875 frozen input hashes remained unchanged. The complete 16-I/56-H domain union, all recursive slope siblings, and every closed boundary face were checked.
- 141 distinct bound records contain318 local rounds,65,008 deductions and82,465 printed-row occurrences, including2,007 terminal rows.
- The separate literal-round audit found no duplicated continuation prefix:81 retained continuation rounds,9,113 retained deductions and18,404 retained premise rows;237 newly appended local rounds,55,895 local deductions and62,054 local premise rows. The original prefix is a separately retained antecedent.

## All16 original I rectangles

| I | Exact x interval | Exact y interval | Checked conclusion |
|---|---|---|---|
| I00 | [-1472789/1048576, -3107647/4194304] | [-91/60, -91/120] | EXCLUDED; I_terminal |
| I01 | [-1472789/1048576, -3107647/4194304] | [-91/120, 0] | EXCLUDED; initial_I_difference |
| I02 | [-1472789/1048576, -3107647/4194304] | [0, 91/120] | EXCLUDED; initial_I_difference |
| I03 | [-1472789/1048576, -3107647/4194304] | [91/120, 91/60] | EXCLUDED; I_terminal |
| I10 | [-3107647/4194304, -162069/2097152] | [-91/60, -91/120] | EXCLUDED; 8/8 H members excluded |
| I11 | [-3107647/4194304, -162069/2097152] | [-91/120, 0] | EXCLUDED; 8/8 H members excluded |
| I12 | [-3107647/4194304, -162069/2097152] | [0, 91/120] | EXCLUDED; 8/8 H members excluded |
| I13 | [-3107647/4194304, -162069/2097152] | [91/120, 91/60] | EXCLUDED; 8/8 H members excluded |
| I20 | [-162069/2097152, 2459371/4194304] | [-91/60, -91/120] | EXCLUDED; I_terminal |
| I21 | [-162069/2097152, 2459371/4194304] | [-91/120, 0] | EXCLUDED; 8/8 H members excluded |
| I22 | [-162069/2097152, 2459371/4194304] | [0, 91/120] | OPEN; 3/8 H members excluded |
| I23 | [-162069/2097152, 2459371/4194304] | [91/120, 91/60] | OPEN; 3/8 H members excluded |
| I30 | [2459371/4194304, 5/4] | [-91/60, -91/120] | EXCLUDED; I_terminal |
| I31 | [2459371/4194304, 5/4] | [-91/120, 0] | EXCLUDED; I_terminal |
| I32 | [2459371/4194304, 5/4] | [0, 91/120] | EXCLUDED; I_terminal |
| I33 | [2459371/4194304, 5/4] | [91/120, 91/60] | EXCLUDED; I_terminal |

## All56 H members of the seven refined I rectangles

For each listed I parent, its independently proved H x interval is split into two equal closed halves and its H y interval into four equal closed quarters. The literal JSON table retains every exact parent interval, resulting rectangle, record hash and subtree. The six special H terminals are five independently reconstructed initial difference contradictions and the completed first-round I12H00 prefix contradiction.

| Full I/H member | Checked status | Method | Terminal or OPEN leaves |
|---|---|---|---|
| I10H00 | EXCLUDED | terminal | 1 |
| I10H01 | EXCLUDED | terminal | 1 |
| I10H02 | EXCLUDED | initial_H_difference | 1 |
| I10H03 | EXCLUDED | terminal | 1 |
| I10H10 | EXCLUDED | terminal | 1 |
| I10H11 | EXCLUDED | terminal | 1 |
| I10H12 | EXCLUDED | slope_cover | 7 |
| I10H13 | EXCLUDED | slope_cover | 16 |
| I11H00 | EXCLUDED | terminal | 1 |
| I11H01 | EXCLUDED | terminal | 1 |
| I11H02 | EXCLUDED | initial_H_difference | 1 |
| I11H03 | EXCLUDED | terminal | 1 |
| I11H10 | EXCLUDED | initial_H_difference | 1 |
| I11H11 | EXCLUDED | terminal | 1 |
| I11H12 | EXCLUDED | terminal | 1 |
| I11H13 | EXCLUDED | slope_cover | 4 |
| I12H00 | EXCLUDED | finished_H_prefix_difference | 1 |
| I12H01 | EXCLUDED | terminal | 1 |
| I12H02 | EXCLUDED | initial_H_difference | 1 |
| I12H03 | EXCLUDED | terminal | 1 |
| I12H10 | EXCLUDED | terminal | 1 |
| I12H11 | EXCLUDED | terminal | 1 |
| I12H12 | EXCLUDED | terminal | 1 |
| I12H13 | EXCLUDED | terminal | 1 |
| I13H00 | EXCLUDED | terminal | 1 |
| I13H01 | EXCLUDED | terminal | 1 |
| I13H02 | EXCLUDED | initial_H_difference | 1 |
| I13H03 | EXCLUDED | terminal | 1 |
| I13H10 | EXCLUDED | terminal | 1 |
| I13H11 | EXCLUDED | slope_cover | 4 |
| I13H12 | EXCLUDED | slope_cover | 4 |
| I13H13 | EXCLUDED | terminal | 1 |
| I21H00 | EXCLUDED | terminal | 1 |
| I21H01 | EXCLUDED | slope_cover | 4 |
| I21H02 | EXCLUDED | slope_cover | 10 |
| I21H03 | EXCLUDED | terminal | 1 |
| I21H10 | EXCLUDED | terminal | 1 |
| I21H11 | EXCLUDED | terminal | 1 |
| I21H12 | EXCLUDED | slope_cover | 16 |
| I21H13 | EXCLUDED | terminal | 1 |
| I22H00 | EXCLUDED | terminal | 1 |
| I22H01 | OPEN | open | 1 |
| I22H02 | OPEN | open | 1 |
| I22H03 | EXCLUDED | terminal | 1 |
| I22H10 | EXCLUDED | terminal | 1 |
| I22H11 | OPEN | open | 1 |
| I22H12 | OPEN | open | 1 |
| I22H13 | OPEN | open | 1 |
| I23H00 | EXCLUDED | terminal | 1 |
| I23H01 | OPEN | open | 1 |
| I23H02 | OPEN | open | 1 |
| I23H03 | EXCLUDED | terminal | 1 |
| I23H10 | EXCLUDED | terminal | 1 |
| I23H11 | OPEN | open | 1 |
| I23H12 | OPEN | open | 1 |
| I23H13 | OPEN | open | 1 |

## The107 normal-H tree leaves

This table lists the selected proof-tree leaves. It excludes the six special H primitives and nine I primitives listed above. Ancestor counts are shared and must not be recovered by summing leaf-local rows; the SHA-deduplicated accounting report supplies the totals. Each `/D4:0`-style suffix names the original frame, number of equal closed parts and child index. Full fractions and immutable SHA-256 values are in `COVER_TABLE.json`.

There are 96 ordinary exact terminals, one separately proved sharp-row terminal and ten OPEN leaves. All 77 positive affine reserves exceed `1/100000`; the smallest exact reserve is `20438044124514674055244526573343678843906311967259073141924320648164523129223825467714664079415831/327791126607224129562073927806772131177103029457708817635966189047694201493157618088537103820600115200`. Other terminals use the independently reconstructed interval/frame/separation contradictions.

| Exact domain address | Kind / terminal | Local rounds | Local deductions | Bound SHA-256 prefix |
|---|---|---:|---:|---|
| I10H00 | positive_exact_reserve | 1 | 333 | 182821df2f34e2133a92 |
| I10H01 | exact_interval_terminal | 0 | 0 | 0d80f385de7aeeed0cea |
| I10H03 | exact_interval_terminal | 0 | 0 | e106259549889fce52a5 |
| I10H10 | exact_interval_terminal | 0 | 0 | 05a5a379a65fdfd2abfc |
| I10H11 | exact_interval_terminal | 0 | 0 | d3120c95fded72ea1c1e |
| I10H12/I4:0 | positive_exact_reserve | 1 | 308 | 00b4e3a3fa7b05dca92e |
| I10H12/I4:1/I4:0 | positive_exact_reserve | 0 | 0 | cadcaf454244edfb383d |
| I10H12/I4:1/I4:1 | proved_empty_original_angle_interval | 1 | 386 | 44ec66d1d1ba2fac0aa7 |
| I10H12/I4:1/I4:2 | positive_exact_reserve | 1 | 349 | 3501f56978375b096f1f |
| I10H12/I4:1/I4:3 | positive_exact_reserve | 1 | 364 | 416ad0429029cf839c56 |
| I10H12/I4:2 | positive_exact_reserve | 3 | 889 | 2cc873c9d83ade1868c2 |
| I10H12/I4:3 | positive_exact_reserve | 1 | 331 | e5f7e1d321ac030874e7 |
| I10H13/I4:0 | positive_exact_reserve | 1 | 316 | 5a0457ff3bb7f22dd748 |
| I10H13/I4:1/I4:0 | positive_exact_reserve | 2 | 683 | 73721e08e0cdbda2945d |
| I10H13/I4:1/I4:1 | positive_exact_reserve | 3 | 969 | ac03513a5454064011bb |
| I10H13/I4:1/I4:2/D4:0 | positive_exact_reserve | 1 | 356 | 8367b8d5c8eafd90f18b |
| I10H13/I4:1/I4:2/D4:1 | positive_exact_reserve | 1 | 353 | 4caf047e7b42f1cd4b0d |
| I10H13/I4:1/I4:2/D4:2 | positive_exact_reserve | 1 | 373 | be79532be86d2c357417 |
| I10H13/I4:1/I4:2/D4:3 | positive_exact_reserve | 0 | 0 | 618bbf5f7e05f80e338c |
| I10H13/I4:1/I4:3/D4:0 | positive_exact_reserve | 1 | 377 | 11b8f05681823799b7e7 |
| I10H13/I4:1/I4:3/D4:1 | proved_empty_original_angle_interval | 1 | 380 | 9ce76ee75d4dc8e8827d |
| I10H13/I4:1/I4:3/D4:2 | positive_exact_reserve | 0 | 0 | 8a79a0cfdc5afaa537cc |
| I10H13/I4:1/I4:3/D4:3 | positive_exact_reserve | 0 | 0 | 1d0180fe58b7be70b6aa |
| I10H13/I4:2/I4:0 | positive_exact_reserve | 3 | 1023 | bbdf72403e63f35cd185 |
| I10H13/I4:2/I4:1 | positive_exact_reserve | 2 | 686 | 841afe753d72f91bec87 |
| I10H13/I4:2/I4:2 | positive_exact_reserve | 1 | 341 | 2df319c7d396235e3e37 |
| I10H13/I4:2/I4:3 | positive_exact_reserve | 1 | 369 | 9140f1e54f1b8b38dd4c |
| I10H13/I4:3 | positive_exact_reserve | 1 | 342 | e87df07be815386164a3 |
| I11H00 | positive_exact_reserve | 1 | 214 | b5d5131f5f5f7b618cd5 |
| I11H01 | positive_exact_reserve | 0 | 0 | 26d739cbb539f653717f |
| I11H03 | exact_interval_terminal | 0 | 0 | e0b67e2dbdd8021334b5 |
| I11H11 | exact_interval_terminal | 0 | 0 | b9d55699cc641d1042d5 |
| I11H12 | positive_exact_reserve | 2 | 351 | 287d6436bacb61bb7797 |
| I11H13/I4:0 | empty_physical_frame | 1 | 373 | cea37ddeed7771bf9c40 |
| I11H13/I4:1 | positive_exact_reserve | 2 | 412 | 6af4c40157684b381303 |
| I11H13/I4:2 | positive_exact_reserve | 2 | 401 | b0ffa8feefd184b4d45d |
| I11H13/I4:3 | positive_exact_reserve | 1 | 360 | 5aa353f62411ee1839e8 |
| I12H01 | positive_exact_reserve | 0 | 0 | 463d887bef962ad2a9af |
| I12H03 | exact_interval_terminal | 0 | 0 | c1ee115985aa3b2906e5 |
| I12H10 | exact_interval_terminal | 0 | 0 | 9e65e2570f816c9c8a84 |
| I12H11 | positive_exact_reserve | 2 | 332 | 6e72f6e76299bdcd0a90 |
| I12H12 | positive_exact_reserve | 0 | 0 | 3c6e3757a101618ffced |
| I12H13 | positive_exact_reserve | 5 | 749 | dd224735de7b47341ee9 |
| I13H00 | proved_empty_original_angle_interval | 2 | 572 | 618a9e984c5192eae662 |
| I13H01 | positive_exact_reserve | 0 | 0 | 7f6a36188b4d80bca693 |
| I13H03 | exact_interval_terminal | 0 | 0 | 02a6681ff17b462bcb5f |
| I13H10 | positive_exact_reserve | 0 | 0 | 34d3df3b47beead7efcf |
| I13H11/I4:0 | positive_exact_reserve | 0 | 0 | 25d054d2c833587aa740 |
| I13H11/I4:1 | positive_exact_reserve | 1 | 332 | 4a3f7fba3576928de308 |
| I13H11/I4:2 | positive_exact_reserve | 1 | 330 | 83c043ce5dc6cbbbed73 |
| I13H11/I4:3 | positive_exact_reserve | 0 | 0 | 5116a44fc06ea5ef3068 |
| I13H12/I4:0 | positive_exact_reserve | 2 | 597 | af0ff2927c411d4f838c |
| I13H12/I4:1 | positive_exact_reserve | 2 | 590 | de5c570505f018c5fee1 |
| I13H12/I4:2 | positive_exact_reserve | 2 | 576 | cc448417cfea2a7ce0b8 |
| I13H12/I4:3 | positive_exact_reserve | 2 | 592 | 6e8a37d5a34a9945a4d5 |
| I13H13 | positive_exact_reserve | 0 | 0 | 03c87762c54d3f803a5f |
| I21H00 | exact_interval_terminal | 2 | 570 | 4224e92c1c9499322410 |
| I21H01/I4:0 | positive_exact_reserve | 2 | 684 | f92a19107e697331d9f1 |
| I21H01/I4:1 | accepted_shared_sharp_boundary_terminal | 3 | 1012 | 4179dd39eda16dab9fcf |
| I21H01/I4:2 | positive_exact_reserve | 0 | 0 | 94cd838d083c3ee3e43e |
| I21H01/I4:3 | positive_exact_reserve | 0 | 0 | 1685dcf73848d1378af9 |
| I21H02/I4:0 | empty_physical_frame | 2 | 665 | a8e0e14ac9be03079016 |
| I21H02/I4:1/D4:0 | positive_exact_reserve | 3 | 1008 | d85fd0c82ba67a614bc1 |
| I21H02/I4:1/D4:1 | positive_exact_reserve | 1 | 352 | cdb1f0c2c360aec7176e |
| I21H02/I4:1/D4:2 | positive_exact_reserve | 0 | 0 | 9040a5c2831e856f4fe7 |
| I21H02/I4:1/D4:3 | positive_exact_reserve | 0 | 0 | f1dac9660ff2ebce5183 |
| I21H02/I4:2/D4:0 | positive_exact_reserve | 3 | 1001 | 9834648ce2390fa53fb3 |
| I21H02/I4:2/D4:1 | positive_exact_reserve | 1 | 337 | a825cbb7694783874a65 |
| I21H02/I4:2/D4:2 | positive_exact_reserve | 1 | 371 | 2b19bde6de33a99ab350 |
| I21H02/I4:2/D4:3 | positive_exact_reserve | 1 | 367 | ddb17979833455487950 |
| I21H02/I4:3 | positive_exact_reserve | 1 | 286 | 4004876f3cd5cd671567 |
| I21H03 | positive_exact_reserve | 2 | 502 | 32ddde46fec3a4809625 |
| I21H10 | positive_exact_reserve | 0 | 0 | f430d8e9bd4fb47c227a |
| I21H11 | positive_exact_reserve | 1 | 244 | 5056f2136e66e23b1efd |
| I21H12/I4:0 | positive_exact_reserve | 3 | 831 | a35ea0d6032cd15bd822 |
| I21H12/I4:1/D4:0/H4:0 | positive_exact_reserve | 1 | 320 | ee8e0b534bd0e95389f1 |
| I21H12/I4:1/D4:0/H4:1 | exact_interval_terminal | 3 | 965 | eaec794fad70ae36a168 |
| I21H12/I4:1/D4:0/H4:2 | positive_exact_reserve | 2 | 633 | 2ee84560ba7b6e45c5c2 |
| I21H12/I4:1/D4:0/H4:3 | positive_exact_reserve | 1 | 332 | 699de55e8d960650c585 |
| I21H12/I4:1/D4:1 | positive_exact_reserve | 2 | 638 | b7438ee0f4bb9a1c3e08 |
| I21H12/I4:1/D4:2 | positive_exact_reserve | 2 | 638 | 3bc8d61d91ac26b53e53 |
| I21H12/I4:1/D4:3 | positive_exact_reserve | 2 | 626 | c3fd6a38905e80b6e9cf |
| I21H12/I4:2/D4:0/H4:0 | positive_exact_reserve | 1 | 331 | a0917cf69c2f48a9407c |
| I21H12/I4:2/D4:0/H4:1 | positive_exact_reserve | 2 | 635 | 02ae0e04dd6c2534772e |
| I21H12/I4:2/D4:0/H4:2 | positive_exact_reserve | 2 | 626 | 457fcbf7cfe58d329740 |
| I21H12/I4:2/D4:0/H4:3 | positive_exact_reserve | 1 | 319 | 4a71726375837ea61480 |
| I21H12/I4:2/D4:1 | positive_exact_reserve | 3 | 962 | cf9990a86463a3176000 |
| I21H12/I4:2/D4:2 | positive_exact_reserve | 2 | 634 | fa08b1c8c4af3418fc58 |
| I21H12/I4:2/D4:3 | positive_exact_reserve | 3 | 956 | 658a66081a17d7cff4d7 |
| I21H12/I4:3 | positive_exact_reserve | 3 | 821 | c3b934d83226657db49f |
| I21H13 | positive_exact_reserve | 6 | 1492 | 85d493d27b6d7b74b750 |
| I22H00 | exact_interval_terminal | 2 | 467 | 940671a846dc4a7f95a2 |
| I22H01 | OPEN | 6 | 503 | 72ba90a9a750f5719eb3 |
| I22H02 | OPEN | 6 | 533 | 20eeea4f664b857f5697 |
| I22H03 | exact_interval_terminal | 3 | 774 | 3466db5cfbff6535199a |
| I22H10 | positive_exact_reserve | 0 | 0 | 3961928367989ce49c2c |
| I22H11 | OPEN | 6 | 582 | c8d9d561b782e09483b3 |
| I22H12 | OPEN | 6 | 291 | c57a6d3859b0f7041ef1 |
| I22H13 | OPEN | 6 | 218 | 721fb2fe0e764c6c3c4f |
| I23H00 | exact_interval_terminal | 2 | 472 | a039de1d848edcaa380c |
| I23H01 | OPEN | 6 | 466 | b9e98c7ed17ff0764de3 |
| I23H02 | OPEN | 6 | 424 | 9ab3b2523e41de6b141d |
| I23H03 | positive_exact_reserve | 2 | 459 | 6465c2d00f60917fca88 |
| I23H10 | positive_exact_reserve | 0 | 0 | 2c7b0eed34309ed98862 |
| I23H11 | OPEN | 6 | 422 | e5a26aa4a85843f1c24a |
| I23H12 | OPEN | 6 | 175 | c15e76760a304599aeb7 |
| I23H13 | OPEN | 6 | 1114 | ef45c32ec8238f688718 |

## The accepted sharp equality terminal

`I21H01/I4:1` binds the completed OPEN record `4179dd39eda16dab9fcfd2a9fd08dc8bf9346eaf0da42163f17d5ad3381a693f` unchanged. Fresh physical reconstruction proves the AHID row guard with all seven absolute frame components at most `1/30` and total height variation at most `43697/524288 < 11/30`. Its three horizontal-order lower bounds and both shoulder gaps are strictly positive.

The pinned full physical theorem gives squared radius at least Q. Its equality face aligns the selected seven originals and forces span3; the original actual AB/BC and cone-inset CD comparisons then force B and C aligned too, contradicting the retained strict weak CD bit. This is a separate mathematical terminal on that exact I-quarter; the underlying OPEN record is never relabeled and no sibling is discarded.

## Remaining obligations

Exactly the following ten complete H6 domains remain OPEN. Their partial discovery angle covers are preserved in the frozen core but do not receive credit or replace these obligations.

| Remaining H domain | Immutable OPEN source |
|---|---|
| I22H01 | `72ba90a9a750f5719eb3e638cc70e3de130e81e61483a496bcaedc7993996431` |
| I22H02 | `20eeea4f664b857f56973480afe4e3b067d7e46c6b9520d31b983412839be99e` |
| I22H11 | `c8d9d561b782e09483b3a709f394b8e3b38212d9a4aa03aeec7512de8849d3a2` |
| I22H12 | `c57a6d3859b0f7041ef16bfc61f82250d7c3997355c6297c448bd8db67b89fa6` |
| I22H13 | `721fb2fe0e764c6c3c4fa9f4b8ff568d963abcd0bf4d644602c58c8e831a9063` |
| I23H01 | `b9e98c7ed17ff0764de33d48517cb14e1a0a22c2b4e66c5aec42d1eeda5087cf` |
| I23H02 | `9ab3b2523e41de6b141d4c4cf2c0a1a3844eefd83be3053103f94f1ca507af63` |
| I23H11 | `e5a26aa4a85843f1c24a1239c23728a7a1e5c803c1c96bdab4b4b520dd10ace3` |
| I23H12 | `c15e76760a304599aeb700809d246740c900e095df8253e13aa370bad382cf8e` |
| I23H13 | `ef45c32ec8238f68871825d74fa2f507d76b7d433a5a39f90bc1e41d2663032d` |

Whole-original completion requires all ten listed domains to be excluded, using the same original caller and a complete cover wherever further restrictions are introduced. No geometric branch, denominator, strict face or physical original is removed by this checkpoint.

No Lean, Lake, CI, numerical optimizer or producer was imported by the exact assembly. Numerical discovery records remain untrusted until their selected physical deductions are independently replayed.

## Committed portable evidence

[Archive parts and inventory](computer_assisted/a2_00100_dc71_fourteen_I_manifest.json) ·
[Complete exact assembly report](computer_assisted/a2_00100_dc71_fourteen_I_exact_replay.json) ·
[Literal cover table](computer_assisted/a2_00100_dc71_fourteen_I_cover_table.json) ·
[Root archive audit](computer_assisted/a2_00100_dc71_fourteen_I_root_archive_check.json).

Concatenate the eight archive parts in the declared order and extract the xz tar.
From `dc71_fourteen_i_checkpoint`, run
`python -B -S verify_dc71_original_cover_v3.py`.
The archive includes 875 frozen assembly inputs and 23 supporting files.
Its 898 file entries comprise 543 regular payloads and 355 prior internal
hardlinks to identical bytes; no external links occur. All 898 entries and
their source files passed a separate root SHA-256 audit.

The root reviewed the complete cover engine, the exact sharp-guard attachment,
the physical hand proof and its result-specific tables. The complete relocated
assembly was freshly replayed by the independent worker. The root separately
replayed the new 70-record and eight-record component groups and checked
continuation accounting; no second identical full assembly run is claimed.

The ledger remains 218 CLOSED / 13 OPEN original cells and 8 CLOSED / 24 OPEN
masks. This checkpoint adds zero original cells, masks, positional roots or
roadmap gates. All ten explicitly listed H obligations remain OPEN. No Lean,
Lake or CI was run.
