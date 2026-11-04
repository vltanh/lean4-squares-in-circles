# Complete B340 original: 221 CLOSED / 10 OPEN

The unchanged original `negative-34029ea8b047982f` is completely excluded.
Its independently reconstructed initial domain is covered by a finite
403-node tree with **279 excluded leaves and zero OPEN leaves**. Native exact
replay, fresh portable exact replay, the complete hand/table review and the
full archive audit pass. The fixed 231-original register advances from
**220 CLOSED / 11 OPEN to 221 CLOSED / 10 OPEN**. Remaining families are
**A1, B5, C3, D1**. The mask ledger stays **8 CLOSED / 24 OPEN**.

## Exact physical caller

This is negative baseline frontier index 66. Its path is

```json
[["angle",3,0],["angle_cut",[0,"0"],0],
 ["position_cut",[11,"1/2"],1],["f_side_escape",[5,7],[2]]]
```

For the original frame slopes this retains `t_D,t_A in [-1,0]` and
`y_F >= 1/2`. The selected F/H escape and its earlier closed complements are

\[
x_H-x_F\le0,\qquad y_A-2y_H+y_F\le-3/5,\qquad
y_A-y_F\le3/5,\qquad y_A-2y_H+y_F\le3/5.
\]

The last inequality is redundant and remains present in the literal caller.
All nine physical unit squares A through I, their 36 original corners and
36 pair-disjointness conditions, five center cones, actual AB/BC/EF/FG and
strict weak CD remain unchanged. Every original corner lies in the closed
disk of squared radius `Q=1105/256`.

The [physical attachment](computer_assisted/a2_00100_b340_complete_original/B340_REGISTERED_ORIGINAL_PHYSICAL_ATTACHMENT.md)
defines the exact original, and the [generic hand proof](computer_assisted/a2_00100_b340_complete_original/REGISTERED_B_COMPLETE_TREE_HAND_PROOF.md)
derives the weighted-row and finite-cover rules. Insets and product variables
express necessary consequences of the same original squares.

## Complete proof

The independent checker reconstructs every weighted row from certified
original intervals, verifies nonnegative rational multipliers and pays every
coefficient residual. A positive exact contradiction reserve, or a separately
checked interval/frame contradiction, excludes its domain. Every internal
node retains its entire physical cover, including shared faces.

| Exact proof item | Count |
| --- | ---: |
| Node records | 403 |
| Complete four-way inset covers | 47 |
| Complete eight-way physical separating covers | 10 |
| Complete two-way closed slope covers | 67 |
| Excluded terminal domains | 279 |
| OPEN terminal domains | 0 |
| Bound rounds | 400 |
| Rational bound deductions | 67,336 |
| Premise-row occurrences | 199,016 |
| Terminal-row occurrences | 4,173 |

The [complete terminal table](computer_assisted/a2_00100_b340_complete_original/COMPLETE_TERMINAL_TABLE.md)
lists all 279 leaves: 181 positive exact reserves, 71 center-interval
terminals, 14 effective-angle terminals, 10 empty analytic-frame terminals
and three frame contradictions. Every coefficient and multiplier appears
in its archived literal record. No sharp or full-angle terminal is needed
in this instance. Induction over all complete covers excludes the root,
which is the entire registered original rather than a restricted descendant.

## Replay, source identity and reproducibility

The [publication manifest](computer_assisted/a2_00100_b340_complete_original_manifest.json)
binds the original definition, complete tree, hand proof, reports, terminal
table, archive parts, and exact one-cell ledger delta. The
[final root review](computer_assisted/a2_00100_b340_complete_original/ROOT_FINAL_ACCEPTANCE.md)
explains the physical attachment, arithmetic/table distinction and archive
checks. The native and cold replays both reconstruct every new bound and
cover. The cold run reads only the portable packet and its pinned published
prior, uses standard-library exact arithmetic, and imports no optimizer.
All 726 new and 507 prior input files are rehashed at completion.

The new archive is 53,274,488 bytes in seven ordered parts, SHA256
`b4b3db56da2b3ac7a006d8c8e1060d07e4ab0103070fdce88c7611c74744569f`.
Root independently verifies every part and all 730 regular archive members.
The prior is the already published
[I32 dependency manifest](computer_assisted/a2_00100_b16a_I32_complete_H_manifest.json),
archive SHA256 `c6e8dfc170a3d88366a6cd6f0955302ca5f664c626790ca91387f84c42502cb6`.
Its mathematical B16a scope is not borrowed as a B340 exclusion; its frozen
shared code and original-definition inputs are reused by the new full replay.

To reproduce, concatenate the seven new parts in `ARCHIVE_READY.json` order
and the seven prior parts in `PUBLISHED_PRIOR.json` order. Check both archive
hashes, then extract both inside one dedicated directory. Run the extracted
new packet's entry point, using a fresh output directory:

```sh
python3 -B b340_complete_original_package/code/replay_registered_b_four_lazy_packet.py \
  --prior b16a_I32_complete_H_checkpoint --output fresh_b340_replay
```

The required receipt status is
`PASS_FRESH_PORTABLE_COMPLETE_REGISTERED_B_ORIGINAL`, with `complete=true`
and `whole_original_proved=true`. The source-bound register snapshot records
the pre-acceptance OPEN status intentionally; the live fixed register carries
the subsequently accepted closure.

## Fixed accounting

Exactly B340 changes from OPEN to CLOSED. All 231 ID/sign/index/path tuples
and the other 230 entries are unchanged. The same 32 mask IDs, 7,915
positional-root IDs and 15 roadmap IDs remain fixed. No whole mask,
positional root or roadmap gate closes here. `001/00`, its reversal and the
unrestricted bound/equality obligations remain OPEN. No Lean, Lake or CI ran.
