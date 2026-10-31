#!/usr/bin/env python3
"""Exact five-coefficient certificate and reserves for the far-return proof.

Standard library only. Rebuilds the actual comparison polynomial, all
five Bernstein coefficients, the complete inverse polynomial identity,
and the displayed rational endpoint reserves. No sampled sign is used.
"""
from fractions import Fraction as F
from itertools import zip_longest
from math import comb


def add(a, b):
    return [x+y for x, y in zip_longest(a, b, fillvalue=F(0))]


def mul(a, b):
    result = [F(0)]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            result[i+j] += x*y
    return result


def scale(a, c):
    return [c*x for x in a]


def evaluate(a, x):
    return sum(c*x**i for i, c in enumerate(a))


def main():
    q0, qmax = F(6241, 1600), F(1105, 256)
    lower, upper = F(1, 4), F(27, 50)
    width = upper-lower

    # Formula-defined actual comparison polynomial (9).
    tau_lower = [F(1), -F(5, 4), F(9, 20)]
    denominator = [F(1), F(49, 30), -F(1)]
    numerator = [F(1), -F(21, 25), -F(35, 18)]
    one_minus_tau = [F(0), F(5, 4), -F(9, 20)]
    polynomial = add(scale(mul(tau_lower, denominator), F(6, 25)),
                     scale(mul(one_minus_tau, numerator), -F(1)))
    expected_power = [F(6, 25), -F(579, 500), F(439, 500),
                      F(113803, 45000), -F(983, 1000)]
    assert polynomial == expected_power
    degree = 4

    # Exact affine substitution s=1/4+(29/100)t.
    assert width == F(29, 100)
    transformed = [sum(polynomial[i]*comb(i, j)*lower**(i-j)*width**j
                       for i in range(j, degree+1))
                   for j in range(degree+1)]
    bernstein = [sum(transformed[j]*F(comb(i, j), comb(degree, j))
                     for j in range(i+1)) for i in range(degree+1)]
    expected_bernstein = [F(472897, 11520000), F(5427751, 288000000),
                          F(2277601, 75000000), F(425205657, 5000000000),
                          F(1158370107, 6250000000)]
    assert bernstein == expected_bernstein
    assert all(value > 0 for value in bernstein)

    # Complete inverse identity in ordinary t powers, not evaluations.
    reconstructed = [sum(bernstein[i]*comb(degree, i)
                         * comb(degree-i, j-i)*(-1)**(j-i)
                         for i in range(j+1))
                     for j in range(degree+1)]
    assert reconstructed == transformed

    h_upper = [F(1, 4), F(9, 10), F(33, 80)]
    beta_lower = [F(19, 10), -F(1, 4)]
    root_reserve = add([q0], scale(add(mul(h_upper, h_upper),
                                     mul(beta_lower, beta_lower)), -F(1)))
    assert evaluate(root_reserve, lower) == F(447999, 1638400)
    assert evaluate(root_reserve, upper) == F(2087039951, 40000000000)
    assert evaluate(root_reserve, lower) > 0
    assert evaluate(root_reserve, upper) > 0
    assert evaluate(tau_lower, lower) == F(229, 320)
    assert evaluate(tau_lower, upper) == F(22811, 50000)
    assert 0 < evaluate(tau_lower, upper) < evaluate(tau_lower, lower) < 1

    reserves = {
        'a_lower': q0-F(81, 100)-F(49, 16),
        'a_upper_two': 4-(qmax-F(9, 25)),
        'angle_lower_sqrt': 15-F(58, 15)**2,
        'angle_upper': F(35, 18)*upper**2+upper*F(21, 25)-1,
        'cosine_lower': 1-upper**2-F(21, 25)**2,
        'cosine_quadratic': F(11, 20)-F(25, 46),
        'radius_upper': F(25, 12)**2-qmax,
        'endpoint_a_upper': F(81, 25)-(q0-F(81, 100)),
        'rho_comparison': 1-F(3, 5)-F(3, 5)**2,
        'N_comparison': 7**2-34,
        'P_a_upper': F(225, 64)-(qmax-F(81, 100)),
        'P_b_upper': F(59, 40)**2-qmax/2,
        'P_norm': 1-(F(7, 8)**2+F(19, 40)**2),
        'sqrt_two_upper': F(99, 70)**2-2,
        'P_distance': F(157, 280)**2-F(5, 16),
        'pressure_sqrt_two': F(3, 2)**2-2,
        'positive_U_vertex': F(39, 40)**2-F(13, 16),
    }
    assert all(value > 0 for value in reserves.values())
    assert reserves['a_lower'] == F(9, 320)
    assert reserves['angle_upper'] == F(103, 5000)
    assert reserves['P_a_upper'] == F(59, 6400)
    assert reserves['P_b_upper'] == F(223, 12800)
    assert F(7, 8)**2+F(19, 40)**2 == F(793, 800)
    assert F(79, 40)-F(99, 70) == F(157, 280)
    assert reserves['P_distance'] == F(149, 78400)
    assert reserves['positive_U_vertex'] == F(221, 1600)

    # The two one-variable identities used in the pressure/radius step.
    n = [F(0), F(1)]
    b0_squared = [F(5, 16), F(0), -F(1)]
    chord = [F(3, 4), -F(1)]
    circle_difference = add(b0_squared, scale(mul(chord, chord), -F(1)))
    factored_difference = scale(mul([-F(1, 4), F(1)],
                                   [F(1, 2), -F(1)]), F(2))
    assert circle_difference == factored_difference
    assert mul(chord, [F(3, 4), F(1)]) == [F(9, 16), F(0), -F(1)]

    print('PASS: all five positive Bernstein coefficients and every inverse coefficient.')
    print('Bernstein:', ', '.join(str(value) for value in bernstein))
    print('PASS: root endpoints, angle/radius reserves, and pressure identities.')


if __name__ == '__main__':
    main()
