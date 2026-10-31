#!/usr/bin/env python3
"""Exact 18-coefficient checker for the whole positive-C comparison.

Both scalar polynomials are rebuilt from the defining squared comparisons,
not loaded from a certificate. Every monomial coefficient, every positive
Bernstein coefficient, and both full inverse identities are checked using
only Python's standard Fraction arithmetic. No sampled substitution is used.
"""
from fractions import Fraction as F
from math import comb


def add(a, b):
    out = [F(0)] * max(len(a), len(b))
    for i, value in enumerate(a):
        out[i] += value
    for i, value in enumerate(b):
        out[i] += value
    return out


def scale(a, scalar):
    return [value * scalar for value in a]


def sub(a, b):
    return add(a, scale(b, -1))


def mul(a, b):
    out = [F(0)] * (len(a) + len(b) - 1)
    for i, value in enumerate(a):
        for j, other in enumerate(b):
            out[i + j] += value * other
    return out


def power(a, exponent):
    out = [F(1)]
    for _ in range(exponent):
        out = mul(out, a)
    return out


def affine_substitute(a, left, right):
    out = [F(0)]
    for i, value in enumerate(a):
        out = add(out, scale(power([left, right - left], i), value))
    return out


def certify(poly, left, right, expected):
    transformed = affine_substitute(poly, left, right)
    degree = 8
    coefficients = [
        sum(transformed[k] * F(comb(i, k), comb(degree, k))
            for k in range(min(i, len(transformed) - 1) + 1))
        for i in range(degree + 1)
    ]
    assert coefficients == expected
    assert all(value > 0 for value in coefficients)
    for k in range(degree + 1):
        actual = sum(
            coefficients[i] * comb(degree, i) * comb(degree - i, k - i)
            * (-1) ** (k - i)
            for i in range(k + 1)
        )
        target = transformed[k] if k < len(transformed) else F(0)
        assert actual == target, ("inverse", k, actual, target)
    return min(coefficients)


p = [F(0), F(1)]
p2 = power(p, 2)
p3 = power(p, 3)
w0 = F(79, 200)
p1 = F(213, 250)

b_a = sub([F(1)], scale(mul(p2, sub(p, [w0])), F(12, 25)))
r_a = sub([w0 + F(2, 3)], p3)
poly_a = sub(power(r_a, 2), mul(power(b_a, 2), sub([F(1)], p2)))
assert poly_a == [
    F(45769, 360000), F(0), F(388, 625), -F(349, 300),
    F(536331, 1562500), -F(12156, 15625), F(1258669, 1562500),
    -F(2844, 15625), F(144, 625),
]
coefficients_a = [
    F(89912784779689, 576000000000000),
    F(1785245130798353, 11520000000000000),
    F(93939915415177316534149, 630000000000000000000000),
    F(107915943776010466959509, 787500000000000000000000),
    F(57924571143055171227923, 492187500000000000000000),
    F(11186766812587710327377, 123046875000000000000000),
    F(17954976906921774981407, 307617187500000000000000),
    F(6897382627777033352129, 274658203125000000000000),
    F(229014543407232478021, 85830688476562500000000),
]
minimum_a = certify(poly_a, w0, p1, coefficients_a)

a_l = sub([F(25, 12)], scale(mul(p, sub(p, [w0])), F(12, 25)))
b_l = add(sub([F(15, 7)], scale(p2, 2)), scale(p, w0))
poly_l = sub(power(b_l, 2), mul(power(a_l, 2), sub([F(1)], p2)))
assert poly_l == [
    F(1775, 7056), F(158, 175), -F(3324941477, 1575000000),
    -F(37999, 62500), F(2821169, 1562500), -F(2844, 15625),
    F(144, 625),
]
coefficients_l = [
    F(1775, 7056),
    F(7667077, 22050000),
    F(1072560605129987, 2756250000000000),
    F(5086900407304249, 13781250000000000),
    F(31710842451161494793, 107666015625000000000),
    F(19851849882388389923, 107666015625000000000),
    F(76990933744858166597, 1076660156250000000000),
    F(7958878428337209899, 1076660156250000000000),
    F(18884302876900644689, 269165039062500000000),
]
minimum_l = certify(poly_l, F(0), p1, coefficients_l)

reserves = {
    "w lower": F(6241, 3200) - (1 + w0) ** 2,
    "w upper": F(19, 10) ** 2 + F(9, 10) ** 2 - F(1105, 256),
    "p upper": p1 - F(35800, 42041),
    "Z lower": F(6241, 1600) - F(9, 10) ** 2 - F(7, 4) ** 2,
    "Z upper": F(25, 12) ** 2 - F(1105, 256),
    "M greater than p": F(3, 8) ** 2 - F(1, 8),
    "final circle reserve": F(6241, 1600) - F(2287, 588),
}
assert all(value > 0 for value in reserves.values())
assert reserves["final circle reserve"] == F(2627, 235200)
assert F(64, 49) + F(1, 4) + 1 + F(4, 3) == F(2287, 588)
print("PASS: both defining squared polynomials, all 18 positive Bernstein")
print("coefficients, both full inverse identities (including elevated zeros),")
print("and all exact scalar domain/final reserves.")
print("A-coordinate packet minimum:", minimum_a)
print("L-coordinate packet minimum:", minimum_l)
