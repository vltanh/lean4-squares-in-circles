#!/usr/bin/env python3
"""Exact nine-coefficient certificate for the whole adjacent-C side exit.

Standard library only; no sampled signs or external algebra packages.
Reconstructs the formula-defined polynomial, every Bernstein coefficient,
the complete inverse identity, the discriminant, and rational reserves.
"""
from fractions import Fraction as F
from math import comb


def add(a, b):
    result = a.copy()
    for exponent, coefficient in b.items():
        result[exponent] = result.get(exponent, F(0))+coefficient
    return {e: c for e, c in result.items() if c}


def scale(a, coefficient):
    return {e: coefficient*c for e, c in a.items() if coefficient*c}


def mul(a, b):
    result = {}
    for (i, j), x in a.items():
        for (k, ell), y in b.items():
            exponent = i+k, j+ell
            result[exponent] = result.get(exponent, F(0))+x*y
    return {e: c for e, c in result.items() if c}


def main():
    one = {(0, 0): F(1)}
    tau = {(1, 0): F(1)}
    w = {(0, 1): F(1)}
    w2, tau2 = mul(w, w), mul(tau, tau)

    # J from the actual chord comparison, before collecting coefficients.
    j = add(scale(one, F(7, 8)), scale(w, -F(1, 2)))
    j = add(j, mul(tau, add(scale(one, -F(3, 4)),
                            scale(add(w2, scale(w, -F(1))), F(2, 3)))))
    j = add(j, mul(tau2, add(scale(w, F(2, 3)), scale(w2, -F(2, 9)))))
    expected = {(0, 0): F(7, 8), (0, 1): -F(1, 2),
                (1, 0): -F(3, 4), (1, 2): F(2, 3),
                (1, 1): -F(2, 3), (2, 1): F(2, 3),
                (2, 2): -F(2, 9)}
    assert j == expected

    # tau=lambda/2 and W=(23/16)*zeta, both on the entire unit square.
    power = {(r, s): coefficient*F(1, 2)**r*F(23, 16)**s
             for (r, s), coefficient in j.items()}
    bernstein = [
        [sum(coefficient*F(comb(i, r), comb(2, r))
             * F(comb(k, s), comb(2, s))
             for (r, s), coefficient in power.items() if r <= i and s <= k)
         for k in range(3)] for i in range(3)]
    expected_bernstein = [[F(7, 8), F(33, 64), F(5, 32)],
                          [F(11, 16), F(5, 24), F(113, 1536)],
                          [F(1, 2), F(1, 48), F(533, 4608)]]
    assert bernstein == expected_bernstein
    assert all(value > 0 for row in bernstein for value in row)

    # Rebuild every ordinary monomial coefficient from the full tensor basis.
    for r in range(3):
        for s in range(3):
            inverse = sum(bernstein[i][k]*comb(2, i)*comb(2-i, r-i)
                          * (-1)**(r-i)*comb(2, k)*comb(2-k, s-k)
                          * (-1)**(s-k)
                          for i in range(r+1) for k in range(s+1))
            assert inverse == power.get((r, s), F(0)), (r, s)

    # Exact W-quadratic discriminant in beta, using first variable as beta.
    beta = tau
    beta2 = mul(beta, beta)
    leading = add(scale(beta, F(4)), scale(one, -F(1)))
    linear = scale(mul(beta, add(scale(beta, F(2)), scale(one, -F(1)))), -F(4))
    constant = scale(mul(beta2, add(beta, scale(one, -F(1)))), F(8))
    discriminant = add(mul(linear, linear), scale(mul(leading, constant), -F(4)))
    expected_discriminant = scale(mul(beta2,
        add(add(scale(beta2, -F(4)), scale(beta, F(6))), scale(one, -F(1)))), F(16))
    assert discriminant == expected_discriminant
    assert -4*F(3, 2)**2+6*F(3, 2)-1 == -1
    assert -8*F(3, 2)+6 < 0

    assert F(1105, 256)-F(9, 4) == F(23, 16)**2
    derivative_reserve = 1-F(23, 72)*F(39, 16)
    assert derivative_reserve == F(85, 384) > 0
    assert 3 > F(3, 2)**2
    assert F(3, 2)**2 > 2
    assert (F(6241, 1600)-F(15, 4))/2 == F(241, 3200) > 0

    print('PASS: all nine positive Bernstein coefficients and every inverse coefficient.')
    for row in bernstein:
        print('  ', ', '.join(str(value) for value in row))
    print('PASS: circle discriminant, beta derivative, and all rational reserves.')


if __name__ == '__main__':
    main()
