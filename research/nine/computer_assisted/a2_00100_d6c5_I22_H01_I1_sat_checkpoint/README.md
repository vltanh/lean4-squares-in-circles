# Reproduce the exact D6c5 conditional cover

This supplement excludes I22 / H01 / original-I slope [-1/2,0], for the
complete original-D slope interval [0,1]. It adds no whole-original or mask
closure credit. Read HAND_PROOF.md and COMPLETE_TERMINAL_TABLE.md.

1. Concatenate the twelve existing `d6c5_I23_H_supplement_v3.tar.xz.part*`
   files from `research/nine/computer_assisted/a2_00100_d6c5_I23_complete_H_checkpoint`.
   The archive SHA-256 must be
   `c58aedd5dd0d5efc3dbc0422703ced905f31667e77de303387ce4b377c34993d`.
2. Extract its `d6c5_I23_H_supplement_v3/core` directory and this supplement
   beneath the same dedicated replay directory. The core manifest SHA-256
   must be `4d30e61283571ca74986957f047ae848127ea7e65fba0fadebe364d6af708b7d`.
   It contains 779 frozen inputs.
3. Run with Python assertions enabled, using only the standard library:

```sh
python -B supplement/replay_d6_sat_packet.py --core ancestor/core --output exact_output
```

Adjust the two directory names to the extraction locations. Both must be
beneath one dedicated common directory so old workspace reads can be
forbidden. Do not use Python optimization mode. No Lean, Lake or CI is needed.
The final exact result is `exact_output/COMPLETE_REPLAY.json`.

The numerical discovery sources are preserved only for provenance; this
command does not import or execute them. Discovered LP points, search order
and solver diagnostics are ignored by the proof checker.
