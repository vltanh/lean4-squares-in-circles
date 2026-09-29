# Normalization sharpness controls
Backend: independent exact-dyadic intervals, 96-bit units (NOT Arb).
Expected non-certification does not by itself prove a counterexample.
| test | expected | observed | boxes | unresolved | result |
|---|---|---|---:|---:|---|
| pins margin 0.049 | certified | certified | 73637 | 0 | PASS |
| pins margin 0.051 | not certified | not certified | 25239 | 3967 | PASS |
| L6 margin 0.037 | certified | certified | 4259 | 0 | PASS |
| L6 margin 0.038 | not certified | not certified | 3987 | 104 | PASS |
| L7 margin 0.10 | certified | certified | 4753 | 0 | PASS |
| L7 margin 0.11 | not certified | not certified | 7697 | 542 | PASS |
| E/CE window +/-0.2025 | certified | certified | 2155 | 0 | PASS |
| E/CE window +/-0.200 | not certified | not certified | 12999 | 2626 | PASS |
| W/OWN upper 0.6165 | not certified | not certified | 2475 | 23 | PASS |
| A1 arc (-0.995,1.22) | not certified | not certified | 15923 | 3397 | PASS |
| A1 arc (-0.99,1.23) | not certified | not certified | 8769 | 1497 | PASS |
| A2 corner arc (-0.57,1.56) | not certified | not certified | 31693 | 11099 | PASS |
| A2 near (1/2,c0), arc (-0.54,1.60) | not certified | not certified | 13951 | 1487 | PASS |
| W/D without pair disjointness | not certified | not certified | 200017 | 63150 | PASS |

OVERALL: 14/14 controls behaved as expected.
