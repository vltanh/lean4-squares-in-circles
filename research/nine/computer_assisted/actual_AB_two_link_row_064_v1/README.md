# Actual-AB variation strengthened to 16/25

The complete scalar table strengthens the existing physical theorem from
3/5 to 16/25, with coefficient 641/1000 and the same equality analysis.
See [the hand proof](HAND_PROOF.md). Exact replay checks all 28 domains,
121 leaves and 15,125 rational Bernstein coefficients with zero frontier.

The D/G guards and original-label conditions are unchanged. The proof
provides a smaller remaining A-c744 complement; it does not close that
original until the complement is excluded. Current accepted counts remain
222/231 original cells and 8/32 masks closed. No Lean, Lake or CI.

Reproduce with `python -B -S check_three_angle_cover_0641.py cover_0641 fresh_replay.json`.
