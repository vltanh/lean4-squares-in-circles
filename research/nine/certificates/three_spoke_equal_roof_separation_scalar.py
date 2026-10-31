#!/usr/bin/env python3
"""Exact rational certificate for the equal-roof separation scalar.

All polynomial products, affine substitutions, and Bernstein coefficients
are computed with Python integers or fractions. No sampled parameter,
floating-point comparison, external library, or cached coefficient file
is used. The mathematical products and all row floors are printed in
THREE_SPOKE_EQUAL_ROOF_SEPARATION_SCALAR.md.
"""

from fractions import Fraction as F
from math import comb
import json


def constant(value):
    return {(0, 0): value}


def add(*polynomials):
    result = {}
    for polynomial in polynomials:
        for exponent, value in polynomial.items():
            result[exponent] = result.get(exponent, 0) + value
    return {exponent: value for exponent, value in result.items() if value}


def scale(polynomial, scalar):
    return {
        exponent: value * scalar
        for exponent, value in polynomial.items()
        if value * scalar
    }


def multiply(left, right):
    result = {}
    for (i, j), x in left.items():
        for (k, ell), y in right.items():
            exponent = (i + k, j + ell)
            result[exponent] = result.get(exponent, 0) + x * y
    return {exponent: value for exponent, value in result.items() if value}


def power(polynomial, exponent):
    result = constant(1)
    while exponent:
        if exponent % 2:
            result = multiply(result, polynomial)
        polynomial = multiply(polynomial, polynomial)
        exponent //= 2
    return result


def product(*polynomials):
    result = constant(1)
    for polynomial in polynomials:
        result = multiply(result, polynomial)
    return result


def certificate_polynomial(row):
    one = constant(1)
    z = {(1, 0): 1}
    w = {(0, 1): 1}
    A = add(one, scale(power(z, 2), -1))
    B = scale(z, 2)
    D = add(one, power(z, 2))
    M = add(A, B)
    L = add(A, scale(B, -1))

    if row == "lower":
        N0, K0 = B, A
    elif row == "upper":
        N0, K0 = add(one, scale(z, -1)), add(one, z)
    else:
        raise ValueError(row)

    K = product(M, K0)
    N = add(product(L, K0), product(w, add(product(N0, M), scale(product(L, K0), -1))))
    H = add(product(B, K), product(A, N))
    T = add(product(D, K), scale(H, -1))
    Delta = add(scale(product(L, K), -1), product(M, N))
    J = add(product(A, add(K, scale(N, -1)), D, K), product(T, Delta))
    V = add(product(D, power(K, 2)), scale(product(N, H), -1))

    inner = add(
        scale(product(power(V, 3), add(J, product(power(A, 2), add(power(K, 2), power(N, 2))))), 2),
        product(D, power(K, 2), J, add(scale(power(V, 2), 2), scale(product(power(T, 2), power(K, 2)), -1))),
    )
    return add(
        scale(product(add(scale(power(K, 2), 2), scale(power(N, 2), -1)), add(K, scale(N, -1)), inner), 5),
        scale(product(power(K, 3), J, power(V, 3)), -42),
    )


def bernstein_coefficients(polynomial, left, right):
    """Tensor Bernstein coefficients after z=left+(right-left)Z, w=W."""
    n = max(i for i, j in polynomial)
    m = max(j for i, j in polynomial)
    affine = {}
    for (i, j), value in polynomial.items():
        for k in range(i + 1):
            exponent = (k, j)
            affine[exponent] = affine.get(exponent, F(0)) + (
                value * comb(i, k) * left ** (i - k) * (right - left) ** k
            )

    first = {}
    for i in range(n + 1):
        for j in range(m + 1):
            first[i, j] = sum(
                (affine.get((k, j), F(0)) * F(comb(i, k), comb(n, k)) for k in range(i + 1)),
                F(0),
            )

    result = []
    for i in range(n + 1):
        result.append([
            sum((first[i, ell] * F(comb(j, ell), comb(m, ell)) for ell in range(j + 1)), F(0))
            for j in range(m + 1)
        ])
    return result


EXPECTED = {
    "lower": {
        "interval": (F(19, 100), F(27, 100)),
        "degree": (54, 11),
        "terms": 647,
        "floors": [87, 93, 99, 105, 112, 119, 126, 120, 114, 108, 102, 96, 91, 85, 80, 75, 70, 66, 61, 57, 53, 49, 45, 42, 39, 35, 33, 30, 27, 25, 23, 21, 19, 17, 16, 15, 14, 13, 12, 11, 10, 10, 10, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10, 11, 11],
    },
    "upper": {
        "interval": (F(1, 4), F(5, 12)),
        "degree": (43, 11),
        "terms": 434,
        "floors": [115, 151, 190, 232, 282, 340, 407, 485, 575, 679, 798, 935, 1092, 1272, 1476, 1709, 1973, 2272, 2611, 2993, 3425, 3911, 4458, 5071, 5759, 6529, 7390, 8351, 9422, 10614, 11940, 13412, 15045, 16853, 18854, 21064, 23504, 26193, 29154, 32410, 35986, 39910, 44211, 48919],
    },
}


def main():
    summaries = []
    for row, expected in EXPECTED.items():
        polynomial = certificate_polynomial(row)
        degree = (max(i for i, j in polynomial), max(j for i, j in polynomial))
        assert degree == expected["degree"]
        assert len(polynomial) == expected["terms"]
        coefficients = bernstein_coefficients(polynomial, *expected["interval"])
        assert all(value > 0 for line in coefficients for value in line)
        floors = [min(line).numerator * 10 // min(line).denominator for line in coefficients]
        assert floors == expected["floors"]
        summaries.append({
            "row": row,
            "degree": degree,
            "nonzero_monomials": len(polynomial),
            "positive_coefficients": sum(len(line) for line in coefficients),
            "minimum_row_floor_tenths": min(floors),
            "row_floors_tenths": floors,
        })

    z = F(19, 100)
    checks = {
        "p0_minus_q1_at_19_over_100": (1 - z*z - 2*z)/(1 - z*z + 2*z) - 2*z/(1 - z*z),
        "sqrt3_above_173_over_100": F(3) - F(173, 100)**2,
        "sqrt3_below_7_over_4": F(7, 4)**2 - F(3),
        "sqrt2_below_17_over_12": F(17, 12)**2 - F(2),
        "radius_reserve": F(21, 10) - F(25, 12),
    }
    assert all(value > 0 for value in checks.values())
    print(json.dumps({"rows": summaries, "positive_comparisons": {key: str(value) for key, value in checks.items()}}, indent=2))


if __name__ == "__main__":
    main()
