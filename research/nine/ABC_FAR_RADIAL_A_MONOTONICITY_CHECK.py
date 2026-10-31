#!/usr/bin/env python3
"""Reconstruct the complete 52-coefficient far-radial monotonicity certificate.

Standard library only. This is the independent reviewer's reconstruction
of ABC_FAR_RADIAL_A_MONOTONICITY_WORKING_2026_10_25.md, equations (4)--(12).
It first checks the derivative-numerator expansion modulo p^2=1-t^2,
then constructs the cleared two-variable polynomial directly, computes
all rational Bernstein coefficients, checks the sole zero and every
strict sign, and reconstructs every ordinary coefficient in the inverse
identity. No numerical pose or floating-point sign is used.

Run with --write-certificate-dir DIR to save the exact coefficient data.
The geometric domain and derivative derivation remain in the manuscript;
this checker verifies their explicitly displayed polynomial arithmetic.
"""

from argparse import ArgumentParser
from fractions import Fraction as F
from math import comb
from pathlib import Path
import json


def add(*polynomials):
    result = {}
    for polynomial in polynomials:
        for exponent, coefficient in polynomial.items():
            result[exponent] = result.get(exponent, F(0)) + coefficient
    return {e: c for e, c in result.items() if c}


def scale(polynomial, coefficient):
    return {e: c * F(coefficient) for e, c in polynomial.items()
            if c * F(coefficient)}


def mul(*polynomials):
    dimension = len(next(iter(polynomials[0])))
    result = {(0,) * dimension: F(1)}
    for polynomial in polynomials:
        product = {}
        for e, c in result.items():
            for f, d in polynomial.items():
                exponent = tuple(x + y for x, y in zip(e, f))
                product[exponent] = product.get(exponent, F(0)) + c * d
        result = {e: c for e, c in product.items() if c}
    return result


def power(polynomial, exponent):
    dimension = len(next(iter(polynomial)))
    return (mul(*([polynomial] * exponent)) if exponent
            else {(0,) * dimension: F(1)})


def constant(value, dimension):
    return {(0,) * dimension: F(value)} if value else {}


def variable(index, dimension):
    return {tuple(int(index == j) for j in range(dimension)): F(1)}


def reduce_unit_circle(polynomial):
    """Reduce p^2=1-t^2 in a polynomial whose variables are (M,t,p)."""
    result = {}
    for (i, j, k), coefficient in polynomial.items():
        for ell in range(k // 2 + 1):
            exponent = (i, j + 2 * ell, k % 2)
            result[exponent] = (result.get(exponent, F(0))
                                + coefficient * comb(k // 2, ell)
                                * (-1) ** ell)
    return {e: c for e, c in result.items() if c}


def derivative_expansion():
    """Independently check the manuscript's equation (4) equals (5)."""
    M, t, p = [variable(i, 3) for i in range(3)]
    one = constant(1, 3)
    H = add(mul(M, p), scale(t, -F(1, 2)))
    beta = add(one, scale(p, F(1, 2)), mul(M, t))
    Z = add(M, t)
    raw = add(mul(H, t, add(scale(M, 2), t), Z), mul(beta, H, t),
              mul(beta, M, p, Z), scale(power(Z, 3), -1))
    reduced_formula = add(
        mul(power(M, 3), add(scale(mul(t, p), 3), constant(-1, 3))),
        mul(power(M, 2), add(constant(F(1, 2), 3), p, scale(t, -3),
                            scale(power(t, 2), -F(3, 2)),
                            scale(mul(p, power(t, 2)), 5))),
        mul(M, add(t, scale(mul(p, t), 2), scale(power(t, 2), -3),
                   scale(power(t, 3), -3), mul(p, power(t, 3)))),
        scale(power(t, 2), -F(1, 2)),
        scale(mul(p, power(t, 2)), -F(1, 4)),
        scale(power(t, 3), -1), scale(power(t, 4), -F(1, 2)))
    assert reduce_unit_circle(raw) == reduce_unit_circle(reduced_formula)


def cleared_polynomial():
    """Directly clear 8(1-z)^3(1+z^2)^5 in equation (10)."""
    lam, z = variable(0, 2), variable(1, 2)
    one = constant(1, 2)
    z2 = power(z, 2)
    U = add(one, z2)
    one_minus_z = add(one, scale(z, -1))
    p_numerator = add(one, scale(z2, -1))
    t_numerator = scale(z, 2)
    M_numerator = add(
        mul(add(one, z), U),
        scale(mul(lam, add(one, scale(z, -2), scale(z2, -1))), 2))

    # These are the four M-degree coefficients of equation (5), after
    # respectively clearing U^2, U^3, U^4, and U^4.
    c3 = add(scale(mul(t_numerator, p_numerator), 3),
             scale(power(U, 2), -1))
    c2 = add(scale(power(U, 3), F(1, 2)),
             mul(p_numerator, power(U, 2)),
             scale(mul(t_numerator, power(U, 2)), -3),
             scale(mul(power(t_numerator, 2), U), -F(3, 2)),
             scale(mul(p_numerator, power(t_numerator, 2)), 5))
    c1 = add(mul(t_numerator, power(U, 3)),
             scale(mul(p_numerator, t_numerator, power(U, 2)), 2),
             scale(mul(power(t_numerator, 2), power(U, 2)), -3),
             scale(mul(power(t_numerator, 3), U), -3),
             mul(p_numerator, power(t_numerator, 3)))
    c0 = add(scale(mul(power(t_numerator, 2), power(U, 2)), -F(1, 2)),
             scale(mul(p_numerator, power(t_numerator, 2), U), -F(1, 4)),
             scale(mul(power(t_numerator, 3), U), -1),
             scale(power(t_numerator, 4), -F(1, 2)))
    return add(
        mul(power(M_numerator, 3), c3),
        scale(mul(power(M_numerator, 2), one_minus_z, c2), 2),
        scale(mul(M_numerator, power(one_minus_z, 2), c1), 4),
        scale(mul(power(one_minus_z, 3), U, c0), 8))


def certify():
    derivative_expansion()
    G = cleared_polynomial()
    assert tuple(max(e[i] for e in G) for i in range(2)) == (3, 12)
    ordinary = {(r, s): c * F(31, 91) ** s for (r, s), c in G.items()}
    bernstein = [
        [sum(ordinary.get((r, s), 0)
             * F(comb(i, r), comb(3, r))
             * F(comb(j, s), comb(12, s))
             for r in range(i + 1) for s in range(j + 1))
         for j in range(13)]
        for i in range(4)
    ]
    floors = [[c.numerator // c.denominator for c in row]
              for row in bernstein]
    expected_floors = [
        [2, 2, 2, 3, 3, 3, 3, 3, 3, 2, 2, 1, 1],
        [4, 4, 5, 5, 5, 5, 5, 5, 5, 4, 3, 2, 1],
        [6, 6, 7, 7, 8, 8, 8, 8, 7, 6, 5, 4, 2],
        [0, 3, 6, 9, 10, 11, 12, 12, 11, 9, 8, 6, 3],
    ]
    assert floors == expected_floors
    assert bernstein[3][0] == 0
    assert all(bernstein[i][j] > 0 for i in range(4) for j in range(13)
               if (i, j) != (3, 0))

    # Expand the Bernstein basis back into ordinary powers. This checks
    # every one of the 52 coefficient positions, including zero entries.
    inverse = {}
    for i in range(4):
        for j in range(13):
            for r in range(4 - i):
                for s in range(13 - j):
                    exponent = (i + r, j + s)
                    inverse[exponent] = (
                        inverse.get(exponent, F(0)) + bernstein[i][j]
                        * comb(3, i) * comb(12, j)
                        * comb(3 - i, r) * comb(12 - j, s)
                        * (-1) ** (r + s))
    inverse = {e: c for e, c in inverse.items() if c}
    assert inverse == ordinary
    return {
        'packet': 'FAR_RADIAL_A_MONOTONICITY',
        'degrees': [3, 12],
        'z_scale': '31/91',
        'zero_bernstein_positions': [[3, 0]],
        'coefficient_floors': floors,
        'bernstein_coefficients': [[str(c) for c in row] for row in bernstein],
        'unscaled_power_coefficients': [
            [r, s, str(c)] for (r, s), c in sorted(G.items())],
        'scaled_power_coefficients': [
            [r, s, str(c)] for (r, s), c in sorted(ordinary.items())],
    }


def main():
    if not __debug__:
        raise RuntimeError('Run this exact checker without Python optimization.')
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--write-certificate-dir', type=Path)
    options = parser.parse_args()
    record = certify()
    if options.write_certificate_dir:
        options.write_certificate_dir.mkdir(parents=True, exist_ok=True)
        path = options.write_certificate_dir / (
            'ABC_FAR_RADIAL_A_MONOTONICITY_CERTIFICATE.json')
        path.write_text(json.dumps(record, indent=2) + '\n', encoding='utf-8')
    print('PASS: original derivative numerator expansion; all 52 exact '
          'Bernstein coefficients, sole zero b[3,0], and full inverse identity.')


if __name__ == '__main__':
    main()
