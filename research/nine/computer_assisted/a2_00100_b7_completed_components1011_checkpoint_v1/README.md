# B7: seven complete components in the retained 1,011-domain cover

**B7 remains OPEN. This checkpoint grants zero original-cell and zero whole-mask credit.**
The unchanged register has **224 CLOSED / 7 OPEN**; whole masks remain **8 CLOSED / 24 OPEN**.

Native and fresh isolated portable exact replay check the entire retained original
`negative-7c60be8b07a358e9`: **1,011 domains, 543 excluded terminal domains and
43 OPEN terminal domains**. The two newest complete components are the G-axis
positive G/I branch814 and the negative-F half993 under949.

## Complete components

| Component | Domains | Excluded terminal domains |
|---:|---:|---:|
| 4 | 33 | 20 |
| 260 | 425 | 213 |
| 814 | 13 | 10 |
| 816 | 7 | 4 |
| 818 | 9 | 8 |
| 820 | 7 | 4 |
| 993 | 9 | 8 |

These internal components are not additional original register cells. Every
listed component has zero OPEN terminal domains. All four positive-sign G/I
alternatives under component3 are now complete; its four negative-sign
alternatives still retain unresolved regions.

## Physical argument for the newest components

Component814 retains both closed F-position cuts `y_F=-3/64` and `y_F=3/64`.
Its lower complement is excluded by its literal exact terminal. Its central
box has `|c_F|² <=149/2048`, below `(27/100)²` by exactly`187/1280000`, so the
accepted all-nine central-capacity theorem excludes the whole closed box.
The upper complement956 has all eight actual C/I separating-axis alternatives,
and every child1003–1010 is excluded. This completes814 with13 domains/10terminals.

Under the negative G/I branch,949 is covered by the two closed halves at
`x_F=0`. Its negative half993 has all eight actual F/I separating-axis
alternatives, and every child994–1001 is excluded. The positive half1002 and
old complementary domain952 remain OPEN. Whole813 remains OPEN.

The [physical hand attachment](B7_SELECTED1011_COMPLETE_COMPONENTS_PHYSICAL_HAND.md)
and [literal terminal table](B7_SELECTED1011_COMPLETE_COMPONENTS_LITERAL_TERMINAL_TABLE.json)
retain the original labels, both closed faces of every cut, all row coefficients,
rational weights, residual bounds, exact reserves and terminal recipes. The
independent physical peer reconstructed all22 child states in five complete
unions,238 printed terminal rows and13 exact positive reserves, together with
the frame/interval and central-box terminals.

All993 previous bound records and initial states remain identical.989 old
payloads are byte-identical; the other four change only graph metadata or
propagated candidate status. All previously completed components are retained.
The full exact replay checks416 bound rounds,67,065 deductions,246,778 printed
rows,2,118 relative-support chord rows,131 all-nine central rows and13 original-F
central-box terminals. Numerical points and producer flags are not premises.

The decoder retains all nine distinct original unit squares,36 original corners,
36 physical pairs,five cones,actual AB/BC/EF/FG,strictly weak CD,and originalH/I.
The radius scope is strict`q < Q =1105/256`. No global closed-Q theorem or
equality classification is asserted.

## Remaining obligations

| Prior coarse branch | OPEN terminal domains |
|---:|---:|
| 3 | 10 |
| 142 | 6 |
| 154 | 18 |
| 156 | 4 |
| 264 | 5 |

`REMAINING_OPEN_FRONTIER.json` lists the exact43 unresolved terminal IDs.
Later numerical alternatives are outside this immutable checkpoint. The seven
original cells remain the accounting target.

## Recovery and isolated exact replay

Concatenate the parts in `ARCHIVE_PARTS.json` order, checking each part and the
full SHA-256`1bcdbbd9d2a61d3143238dba0f5b87153ce4b22f669b18c73f551b6c3a1212f6` before extraction. The archive has
51,389,580 bytes and1,527
independently rehashed regular members. Its top directory is`b7_selected1011_open_packet_v1`.

Place it beside the published prior`b16a_I32_complete_H_checkpoint`, identified
by `PUBLISHED_PRIOR.json` and archive SHA-256`c6e8dfc170a3d88366a6cd6f0955302ca5f664c626790ca91387f84c42502cb6`.
Use a dedicated directory containing only these copied input packages and the
new output directory. From their common parent:

```sh
python3 -B -S b7_selected1011_open_packet_v1/code/replay_b7_central_position_packet.py   --prior b16a_I32_complete_H_checkpoint --output fresh_b7_open_replay
```

The expected receipt is`PASS_PORTABLE_B7_CENTRAL_POSITION_OPEN_COVER`, with
`complete=false`,`whole_original_proved=false`,and43 OPEN leaves. The checker
forbids proof reads outside that dedicated directory and rehashes all copied
inputs at completion. It checks1,523 packet inputs,
507 prior inputs and752 verified historical aliases to
already frozen bytes. The12 attachments and unchanged decoder/transport sources
are independently reviewed. No old disk PASS initializes the fresh replay.

No Lean,Lake,compilation or CI was run. Continue the seven original obligations
under the fixed bounded-work directive; this checkpoint changes no ledger entry.
