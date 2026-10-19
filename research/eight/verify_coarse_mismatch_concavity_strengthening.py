#!/usr/bin/env python3
"""Exact rational constants for the hand concavity corollary."""
from fractions import Fraction as F
from math import factorial
from pathlib import Path
import json

gamma, beta, pi_upper = F(89727, 100000), F(99, 5000), F(710, 113)
assert 1-F(2, 5)**2/2-F(2, 5) == F(13, 25) > 0
records = []
expected = {
    F(109, 400): F(3469086670939846509033, 1036779520000000000000000000),
    F(11, 40): F(2123678636485607, 103677952000000000000),
}
for t, value in expected.items():
    s7 = sum(((-1)**j*t**(2*j+1)/factorial(2*j+1) for j in range(4)), F(0))
    c6 = sum(((-1)**j*t**(2*j)/factorial(2*j) for j in range(4)), F(0))
    p = t/2-t**2/4-t**3/12+t**4/48+t**5/240-t**6/1440-t**7/10080
    assert p == (s7+c6-1)/2
    reserve = 7*gamma+beta*p-pi_upper
    assert reserve == value > 0 and 0 < t < F(2, 5)
    records.append({"S_threshold": str(t), "width_lower_polynomial": str(p),
                    "reserve_above_710_over_113": str(reserve)})
result = {"status": "PASS_FIXED_RATIONAL_COMPARISONS",
          "scope": "Conditional hand strengthening of the already proved S<2/5 coarse cyclic budget; no extra pair inequality is assumed.",
          "gamma": str(gamma), "beta": str(beta),
          "cos_minus_sin_lower_on_0_to_2_over_5": "13/25",
          "conclusion": "S<109/400", "comparisons": records}
Path(__file__).with_name("coarse_mismatch_concavity_strengthening_arithmetic.json").write_text(
    json.dumps(result, indent=2)+"\n")
print(json.dumps(result, indent=2))
