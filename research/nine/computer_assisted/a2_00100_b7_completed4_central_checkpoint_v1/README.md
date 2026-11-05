# B7: complete component 4 and retained complete component 260

**B7 remains OPEN. This checkpoint grants zero original-cell and zero whole-mask credit.**
The unchanged register has **224 CLOSED / 7 OPEN**; whole masks remain **8 CLOSED / 24 OPEN**.

Native and fresh portable exact replay check the entire retained original
`negative-7c60be8b07a358e9`: **949 domains, 505 excluded terminal domains and
41 OPEN terminal domains**. The new completed component 4 has 33 domains and
20 excluded terminals. Previously completed component 260 remains intact
with 425 domains and 213 excluded terminals.

## Physical argument

Component 4 uses all eight actual E/H separating-axis alternatives. Four
previously unresolved children each receive the three closed cuts
`x_F=1/5`, `y_F=-9/50`, `y_F=9/50`. The four inner boxes have
`|c_F|² <= 181/2500 = (27/100)² - 1/2000` and are excluded by the published
all-nine central-capacity theorem. The twelve outer complements and the
four previously excluded E/H children complete the cover. All shared faces
remain present. See the [physical hand proof and terminal table](B7_COMPLETE_COMPONENT4_PHYSICAL_HAND_ATTACHMENT.md).

The exact decoder retains all nine original frames, all 36 corners and
physical pairs, the five original cones, actual AB/BC/EF/FG, strictly weak
CD, and original H/I labels. Across the full tree it checks 342 bound rounds,
57,118 rational deductions, 220,172 printed row occurrences, 1,657 relative
support chord rows, 22 central rows and six original-F central-box terminals.
No numerical point or producer status supplies a proof premise.

## Remaining original obligations

The older checkpoint had six unresolved coarse branches. Component 4 is now
complete; the other five have the following finer terminal frontier:

| Prior coarse branch | OPEN terminal domains |
|---:|---:|
| 3 | 8 |
| 142 | 6 |
| 154 | 18 |
| 156 | 4 |
| 264 | 5 |

The exact leaf IDs are in `REMAINING_OPEN_FRONTIER.json`. The count of 41
refers to this refined cover, not to 41 original register cells. Later
alternative angle covers are outside this immutable checkpoint.

## Recovery and exact replay

Concatenate the archive parts in `ARCHIVE_PARTS.json` order, checking each
part and the full SHA-256 `d083ab65ec917f3e07c99da6e42168110de1b6a502965d5e1eccbf1f1090ee10` before extraction.
The archive has 45,432,120 bytes and
1,415 independently rehashed regular members.
Its top directory is `b7_completed4_central_open_packet_v2`.

Place the extracted directory beside the published prior
`b16a_I32_complete_H_checkpoint`, identified in `PUBLISHED_PRIOR.json` by
archive SHA-256 `c6e8dfc170a3d88366a6cd6f0955302ca5f664c626790ca91387f84c42502cb6`. From their common directory:

```sh
python3 -B -S b7_completed4_central_open_packet_v2/code/replay_b7_central_position_packet.py \
  --prior b16a_I32_complete_H_checkpoint --output fresh_b7_open_replay
```

The expected receipt is `PASS_PORTABLE_B7_CENTRAL_POSITION_OPEN_COVER`,
with `complete=false`, `whole_original_proved=false`, and 41 OPEN leaves.
The checker forbids proof reads outside that dedicated replay directory,
reconstructs rational rows and complete physical covers, and rehashes all
inputs after completion. There are 1,411 frozen
packet inputs, 507 prior inputs and 751 verified
historical aliases to already frozen bytes. The unchanged mathematical
decoder and position-cover reader are bound by the source reviews.

The claim remains strict `q < 1105/256`. Neither a closed-Q global theorem
nor an equality classification is asserted. No Lean, Lake, compilation or
CI was run. Continue the remaining seven whole originals under the current
bounded-work directive.
