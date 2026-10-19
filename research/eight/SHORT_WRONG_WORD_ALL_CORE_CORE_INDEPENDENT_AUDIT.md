# Independent audit: restored 0010111 core/core hand proof

Result: **PASS**, including all nineteen permitted edge/sign rows.

I independently checked the signed-marker convention and its endpoint ranges, the core side/corner angle lemma, the separate-convexity center-distance argument giving delta>27/20, and the exact role/sign enumeration. The two exceptional rows have the correct label constants and angle ranges. For edge 5 (+,-) below phi=.951, the premise b+B<=.1 bounds both signs of both primary projections and both secondary projections by 7/12+.1<1; therefore no SAT axis can separate. This proves the stated b+B>.1 implication without a missing owner case.

The fixed arithmetic checker replayed successfully with 54 comparisons. Its nineteen row bounds all exceed .898. The checker contains only fixed rational/trigonometric enclosures; no numerical contact premise enters this proof.

This audit is limited to the complete core/core component. It does not certify any remaining mixed or outer/outer row.

## Bound artifacts

- `SHORT_WRONG_WORD_ALL_CORE_CORE_HAND_PROOF.md`: `4d33cc2c40888e536308a9a457953702abe720af2d708940c9789460ccb03a98`.
- `verify_short_all_core_core_hand.js`: `c2e984ac7c026907ed33edf7a1b853c0eddd85bd446b500e8a59f9c3cf741ec7`.
- `short_all_core_core_hand_arithmetic.json`: `cbebdbfcfdc12df64e641ada7224cb1aeba6f849e8c39d2f1933571bfed9d9a3`.
