# Actual-AB full-angle two-link row terminal

The complete theorem is in `ACTUAL_AB_TWO_LINK_ROW_HAND_PROOF.md`.
It uses the actual AB edge and charges vertical variation only to the
two physical links B/I and I/D. Under the stated D/G sign and strict
horizontal-gap guards, it proves the sharp radius bound whenever

```
x_B <= x_I <= x_D,
|y_I-y_B|+|y_D-y_I| <= 3/5.
```

All angle magnitudes can span the full canonical range. D has the
nonnegative sign required by the oriented cap. The generic equality
case aligns A,B,I,D and gives span three; the unchanged original-nine
001/00 caller excludes that equality using its strictly weak CD bit.

The scalar proof has 28 complete domains, 103 leaves and 12,875 exact
Bernstein coefficient checks. Root and independent physical reviews pass,
as do two fresh scalar replays and the exact guard/complement controls.
`PREMISE_BINDINGS.json` pins the complete sources and inherited caps.

Run the standard-library scalar checker with assertions enabled:

```
python -B -S check_three_angle_cover.py cover_0601 fresh_scalar_report.json
```

The guard scripts check quantitative implications only. A caller must
prove the original physical and marked-link hypotheses. The included
D821 five-domain declaration does not exclude those domains by itself.
This conditional packet adds **zero original-cell and zero mask closures**.
No Lean, Lake or CI is run.
