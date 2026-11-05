# Universal actual-AB terminal, all frame signs

Actual AB,EF,FG and an ordered original A-B-X-D row with
`|y_X-y_B|+|y_D-y_X|<=21/100` force squared radius at least 1105/256.
There is no endpoint-sign, shoulder-height or D/G-corridor requirement.
For current `001/00`, the retained original strict CD bit excludes equality.
Use either original extra H or I as X; retain all nine originals.

[The full hand proof](HAND_PROOF.md) gives the complete scalar cover and
closed complementary domains. Exact replay checks 28 domains, 351 leaves
and 43,875 Fraction Bernstein coefficients with zero frontier.

Run `python -B -S check_universal_two_link.py cover fresh_replay.json`.
The discovery LP only proposes weights; the independent checker uses
Python standard-library exact arithmetic. This conditional result adds
zero original-cell or mask closures. No Lean, Lake or CI.
