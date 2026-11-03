#!/usr/bin/env python3
"""Exact scalar identities in THREE_ORIGINAL_SHARP_STRIP_CAPACITY_HAND_PROOF.

This checks the printed polynomial identities and rational comparisons only.
It is not a checker for the physical slice argument or for any original cell.
Python standard library only; no floating point or numerical optimization.
"""

from fractions import Fraction as F
from hashlib import sha256
from math import comb
from pathlib import Path
import json


def add(x, y):
    return x[0] + y[0], x[1] + y[1]


def mul(x, y):
    """Multiply a+b*sqrt(2) and c+d*sqrt(2)."""
    return x[0] * y[0] + 2 * x[1] * y[1], x[0] * y[1] + x[1] * y[0]


def poly_add(a, b):
    result = [(F(0), F(0)) for _ in range(max(len(a), len(b)))]
    for i, c in enumerate(a):
        result[i] = add(result[i], c)
    for i, c in enumerate(b):
        result[i] = add(result[i], c)
    return result


def poly_mul(a, b):
    result = [(F(0), F(0)) for _ in range(len(a) + len(b) - 1)]
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            result[i + j] = add(result[i + j], mul(x, y))
    return result


def main():
    zero = (F(0), F(0))
    one = (F(1), F(0))
    numerator = [(F(-2), F(1)), (F(-1, 2), F(0)), one]
    side_slope = [(F(-1), F(0)), zero, one]
    lhs = poly_add([one], poly_mul(side_slope, side_slope))
    lhs = poly_add(lhs, [mul(c, (F(-4), F(0)))
                         for c in poly_mul(numerator, numerator)])
    q = [(F(16), F(-11)), (F(-7), F(4)),
         (F(-4), F(3)), (F(3), F(0))]
    rhs = poly_mul([(F(0), F(1)), (F(-1), F(0))], q)
    assert lhs == rhs, "Sloped-side factorization fails"

    # Independently expand both sides of the printed Bernstein identity.
    b = list(map(F, ["82301/46656", "29681/7776", "253/48",
                     "139/24", "191/36", "13/3", "6"]))
    bernstein = [F(0)] * 7
    for i, bi in enumerate(b):
        for j in range(7 - i):
            bernstein[i + j] += bi * comb(6, i) * comb(6 - i, j) * (-1) ** j
    p = list(map(F, [-1, 18, -6, -16, 6, 0, 5]))
    affine = [F(0)] * 7
    for i, pi in enumerate(p):
        for j in range(i + 1):
            affine[j] += pi * comb(i, j) * 5 ** j / F(6) ** i
    assert bernstein == affine, "Bernstein identity fails"
    assert min(b) > F(6, 5)

    squares = {
        "k_at_3_20_gt_21_50": 425 ** 2 - 21 ** 2 * 409,
        "sqrt2_gt_7_5": 2 * 5 ** 2 - 7 ** 2,
        "sqrt2_lt_71_50": 71 ** 2 - 2 * 50 ** 2,
        "sqrt2_gt_141_100": 2 * 100 ** 2 - 141 ** 2,
        "k_at_1_6_gt_2_5": 625 - 592,
        "A_at_3_20_gt_101_200": 25 * 409 - 101 ** 2,
        "a_lt_829_2000": 2829 ** 2 - 2 * 2000 ** 2,
        "k_at_9_10_gt_37_1000": 500 ** 2 - 181 * 37 ** 2,
        "A_at_9_10_gt_269_400": 181 * 20 ** 2 - 269 ** 2,
        "beta_at_9_10_gt_2_3": 729 - 724,
        "a_gt_33_80": 12800 - 12769,
        "k_at_9_10_lt_3_80": 1629 - 1600,
        "sqrt2_gt_4_3": 2 * 3 ** 2 - 4 ** 2,
        "sqrt2_lt_16_11": 16 ** 2 - 2 * 11 ** 2,
        "sqrt2_gt_140_99": 2 * 99 ** 2 - 140 ** 2,
        "V_gt_24_13_when_D_ge_2": 351 * 169 - 576 * 100,
    }
    assert all(value > 0 for value in squares.values())
    assert F(9817, 40000) < F(1, 4)
    assert F(151 ** 2 + 131 ** 2, 400 ** 2) == F(39962, 160000) < F(1, 4)
    assert F(280, 99) - F(208, 75) - F(7, 150) == F(41, 4950) > 0
    assert F(3, 14) < F(13, 50) < F(5, 14)

    proof = Path(__file__).resolve().parents[1] / "THREE_ORIGINAL_SHARP_STRIP_CAPACITY_HAND_PROOF.md"
    report = {
        "schema": "n9_sharp_strip_scalar_identity_check_v1",
        "status": "PASS",
        "scope": "Printed scalar identities only; no physical, cell or mask verification claimed",
        "proof_sha256": sha256(proof.read_bytes()).hexdigest(),
        "checker_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
        "factorization": "Exact identity in Q[sqrt(2)][s]",
        "bernstein_identity": "All seven coefficients exact",
        "bernstein_positive_reserve": str(min(b) - F(6, 5)),
        "small_slope_corner_reserve": str(F(1, 4) - F(9817, 40000)),
        "nine_tenths_corner_reserve": str(F(1, 4) - F(39962, 160000)),
        "uniform_affine_improvement_at_W_7_10": str(F(41, 4950)),
        "quadratic_coefficient": "13/50",
        "positive_square_comparisons": squares,
        "lean_lake_ci_run": False,
    }
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
