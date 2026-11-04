# C887 I21: completed finite sharp-complement continuation

This checkpoint retains the same original `negative-887236b78100baf3`,
its exact path, all nine physical squares, all 36 corners and all 36 pairs,
the actual AB, BC, EF and FG links, and strictly weak CD. It studies only
the closed I(2,1) member of the original four-by-four position cover.

The accepted six-round ancestor has SHA-256
`caa176c72bc4eecd0c199837a334433f5bcf7570f9f6cdd14cd13d88711f18d3`.
The earlier `FOUNDATION_HAND_PROOF.md` proves the physical sharp region and
lists the complete twenty closed complementary domains. Every order face,
absolute-angle failure, signed height failure and shoulder failure remains
in that union. This continuation does not replace that cover or its caller.

## Finished exact results

| Declared failure indices | Result |
|---|---|
| 0, 2, 17, 18, 19 | Strict interval exclusions from the common parent |
| 11 | Exact positive affine contradiction after one local bound round |
| 1, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16 | Certified OPEN states after three local rounds |

Failure 11 is the closed halfspace

`-y_A + 2 y_I - y_D <= -53/100`.

Its one completed local round establishes 234 rational bounds. Its twenty
terminal rows have the exact residual-corrected positive reserve

`80497639824302736528907975196037401 / 8411520910826420758219404053336555520`.

For each selected physical affine row `a_r z <= b_r`, all printed weights
are nonnegative rationals. The independent checker reconstructs the rows
from the preceding proved state, forms their weighted sum `c z <= d`, and
uses the certified absolute bounds `|z_k| <= M_k`. A feasible state requires
`d + sum_k M_k |c_k| >= 0`. The displayed reserve is its strictly negative
opposite, so the entire selected failure domain is excluded. The bound
induction uses the same residual correction and outward rational rounding.
No numerical optimizer value is used as an accepted premise.

The common six-round state is counted once. The full continuation checks
49 completed bound rounds, 3,771 bound deductions, 11,391 premise rows and
20 terminal rows. All inherited bounds and original frame identities are
retained. The frozen three-square center-energy theorem and its 1,877 row
identities are replayed separately by the portable entry point.

Fourteen complementary domains remain OPEN. Therefore this checkpoint
closes neither I(2,1) nor an original cell nor any mask. It supplies one
additional proved conditional exclusion and preserves the finished bounded
search without treating its OPEN states as infeasibility certificates.

## Portable replay

Run `python -B -S verify_round3.py` in this packet. It verifies every frozen
input, replays the physical energy premise, repeats the entire declared
twenty-domain computation with packet-local exact code, and rehashes all
inputs before writing `ROUND3_PORTABLE_REPLAY.json`.

The older `verify_all.py`, its reviewed inventory and earlier reports are
preserved as historical foundation evidence. That older wrapper is tied to
the original foundation's inventory; `verify_round3.py` is the entry point
for this extended packet. The original foundation packet is unchanged.

No Lean, Lake, CI, human review or proof-kernel verification is claimed.

## Committed evidence

[Exact packet](computer_assisted/a2_00100_c887_sharp_three_round_checkpoint.tar.xz) ·
[Archive and source hashes](computer_assisted/a2_00100_c887_sharp_three_round_manifest.json) ·
[Root portable replay](computer_assisted/a2_00100_c887_sharp_three_round_root_replay.json).

Extract the archive and run `python -B -S verify_round3.py` from
`c887_sharp_round3_replay_package`. All 232 extracted files have been
individually hash-checked; 41 identical duplicates use safe internal
hardlinks. Every checked mathematical source byte is retained.

The unchanged current ledger is **217 CLOSED / 14 OPEN** among the same
231 original cells, and **8 CLOSED / 24 OPEN** among the same 32 masks.
The 7,915 positional roots and 15 roadmap IDs are unchanged.
