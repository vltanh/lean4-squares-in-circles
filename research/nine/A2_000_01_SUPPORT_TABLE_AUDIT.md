# Independent review of the five complete outer and central tables

November 2, 2026. Reviewer: the separate `root_certificates` agent in the current continuation. No Lean, Lake, or CI was run.

## Result and scope

All five finite certificates used by `UNRESTRICTED_JOINT_FIVE_SQUARE_HIGH_FLOOR_CAP.md` were copied to the current writable workspace and freshly replayed. Every prescribed initial box and every midpoint split was reconstructed; no unfinished leaf was accepted. The four outer envelopes and the central transfer have complete parameter covers when joined to their stated hand regions.

This review supports the stated five-square cap with its original center bands and central whole floor. It does not independently establish the nine-square caller's routing or low-floor extraction. Those are separate components of `A2_000_01_WHOLE_DOMAIN_HAND_TABLE_PROOF.md`.

| Certificate | Fresh exact replay | Outcome |
|---|---|---|
| `outer_R_linear_negative_cover.json` | Independent directed integer intervals; 1,700 leaves | PASS; largest residual upper `-6934341744629233/18446744073709551616` |
| `outer_R_linear_positive_cover.json` | Independent directed integer intervals; 490 leaves | PASS; largest residual upper `-8221223209480849/18446744073709551616` |
| `E_variable_k_linear_negative_cover.json` | Independent exact-Fraction backend; 25 leaves | PASS; every residual upper strictly negative |
| `E_variable_k_linear_positive_cover.json` | Independent exact-Fraction backend; 28 leaves | PASS; every residual upper strictly negative |
| `central_linear_transfer_compact.json` | Independent directed integer intervals; 1,684 numerical and 34 analytic leaves | PASS; smallest numerical lower `5007949818049/1152921504606846976` |

All five input SHA-256 hashes equal the hashes printed in the joint-cap manuscript. The fresh complete reports are preserved alongside the replayed inputs in the continuation workspace. The Fraction E reports print their exact rational extrema without rounding.

## Mathematical coverage reviewed separately from execution

1. **Shoulder-owned outer envelopes.** The three complementary closed roots and the local rectangle `|w|,|z| <= 1/80` cover `[-2/3,6] × [-6,6]` after splitting the sign of `z`. The endpoint free-frame minimum contains every possible minimizing alignment and both interval endpoints. The shoulder uses the actual frame fixed by its owned normal. All box-face multipliers and edge multipliers are nonnegative. The known-frame circle-support formula, including its edge/interior transition, was checked from the quarter-disk optimization.

2. **Endpoint-owned outer envelopes.** The local interval `|z| <= 1/16` and the two closed complementary tables cover every `z ∈ [-6,6]`. Every tabulated multiplier is in `[207/16,20]`. The slope comparison is made with the actual shoulder center and frame fixed, and the table correctly retains the unboxed endpoint constant `r sqrt(46²+k²)-46-k`. A smaller boxed endpoint maximum is not substituted. The seven multiplier rows and the positive-slope derivative reserve were recomputed with exact fractions and agree with the hand proof.

3. **Central transfer.** The exact triangle support candidates retain one common physical central frame. All nonpositive sums are covered by the global `1+(9/10)|S|` triangle estimate and the original top bound; all mixed signs and the strip `|S| <= 1` are covered by the stronger `1+|S|` estimate. The remaining positive-quadrant table proves the maximum of the payment reserve and the genuine two-edge capacity reserve is positive. The second alternative contradicts a strict physical capacity bound. The omitted mixed quadrant is obtained by exchanging the two slopes. These arguments give strictness for every nonzero slope pair.

4. **Local sharp point and arithmetic.** The local R/E hand coefficients, central signed reserve, and every variable-k monotonicity row were checked independently. The local estimates retain the strict radius decrease at zero slopes. The replay arithmetic's directed products, divisions, integer-square-root bounds, active-branch derivative hulls, and centered mean-value bounds were inspected. Branch boundaries are included; the extrema recorded by the producer are not trusted by the replay.

No gap was found in these five components or their stated hand complements. The review does not claim a kernel proof or a review by an independent human mathematician.

## Minimal replay dependencies

The acceptance path for the five tables requires only:

- `verify_outer_scalar_family.py`;
- `verify_E_variable_k_linear.py`;
- `verify_central_linear_transfer.py`;
- `verify_joint_five_dyadic.py`.

The additional exact-Fraction E replay requires `verify_joint_five_fraction.py` and `interval_fraction.py`. None of these three table checkers imports a producer. No numerical optimizer or nonlinear solver is a premise of the accepted tables.
