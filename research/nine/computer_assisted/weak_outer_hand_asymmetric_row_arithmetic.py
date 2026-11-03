#!/usr/bin/env python3
"""Exact scalar arithmetic for the asymmetric original replacement row.

This checks the finite coefficients and positive-root comparisons in the
hand argument. It does not substitute a numerical grid for that argument.
"""
from fractions import Fraction as F
from pathlib import Path
import json


def add(p, q):
    n = max(len(p), len(q))
    return tuple((p[i] if i < len(p) else F(0)) +
                 (q[i] if i < len(q) else F(0)) for i in range(n))


def mul(p, q):
    r = [F(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            r[i + j] += a * b
    return tuple(r)


def scale(p, c):
    return tuple(F(c) * v for v in p)


def deriv(p):
    return tuple(i * p[i] for i in range(1, len(p)))


def same(p, q):
    return not any(add(p, scale(q, -1)))


def evaluate(p, x):
    return sum(c * x**i for i, c in enumerate(p))


def main():
    U, delta = F(1, 3), F(1, 16)
    checks = []

    def positive(name, reserve):
        assert reserve > 0, (name, reserve)
        checks.append({'name': name, 'positive_reserve': str(reserve)})

    positive('upward pair shallow coefficient squared', F(1, 8)-U*U)
    positive('upward pair steep comparison squared', F(2)-(1+U)**2)
    positive('first deficit upper bound squared', F(2)-F(45, 32)**2)
    positive('sqrt2 exceeds7/5 squared', F(2)-F(7, 5)**2)
    positive('shallow X owner slope reserve', F(1, 2)-U-delta)
    positive('steep second owner surplus', F(7, 5)-1-delta-F(1, 16))
    positive('middle endpoint coefficient of z', (2*F(7, 5)-1)/6-delta)
    positive('middle endpoint surplus', (4*F(7, 5)-5)/3-F(1, 8))
    positive('diagonal endpoint surplus', 5*F(7, 5)/3-2-F(1, 8)-delta)
    positive('positive D total variation reserve', F(1, 2)-U-delta)
    assert checks[4]['positive_reserve'] == '5/48'
    assert checks[5]['positive_reserve'] == '11/40'
    assert checks[7]['positive_reserve'] == '3/40'
    assert checks[8]['positive_reserve'] == '7/48'

    t = (F(0), F(1))
    r2 = (F(1), F(0), F(1))
    one_t3 = (F(1), F(0), F(0), F(1))
    # Derivative numerator of (1+t^3)/(1+t^2)^(3/2).
    n = add(mul(deriv(one_t3), r2), scale(mul(t, one_t3), -3))
    assert same(n, (F(0), F(-3), F(3)))
    # Numerator for (A+r)' minus a sufficient upper bound for r^3.
    n = add((F(1), F(2), F(0), F(3)),
            scale(mul((F(1), F(1)), r2), -1))
    assert same(n, (F(0), F(1), F(-1), F(2)))
    # Exact concavity numerator; affine z dependence is checked at0,1.
    concavity = []
    for z in (F(0), F(1)):
        first_n = (1-z/2, -z/2, F(0), F(1))
        second_n = add(mul(deriv(first_n), r2),
                       scale(mul(t, first_n), -3))
        expected = (-z/2, -3+3*z/2, 3+z)
        assert same(second_n, expected)
        concavity.append([str(c) for c in expected])
    # At z=1 the convex quadratic is negative at both endpoints0,1/2.
    assert evaluate((F(-1,2), F(-3,2), F(4)), F(0)) == F(-1,2)
    assert evaluate((F(-1,2), F(-3,2), F(4)), F(1,2)) == F(-1,4)
    # The t=0 radical comparison has squared difference2z^3.
    left = mul(mul((F(2), F(1)), (F(2), F(1))), r2)
    right = mul((F(2), F(1), F(1)), (F(2), F(1), F(1)))
    assert same(add(left, scale(right, -1)), (F(0), F(0), F(0), F(2)))
    # k=1/sqrt8<1/2, and all old/new last-gap allowances are included.
    assert F(1, 8) < F(1, 4)
    assert delta < F(1, 8)
    assert F(1, 8)-delta == F(1, 16)
    assert U+delta == F(19, 48) < F(1, 2)
    # Equality-caller arithmetic remains inside the original C/D cone.
    assert F(1, 16) < F(2, 3)
    assert F(3, 2)-F(2, 3)-F(1, 2) == F(1, 3)
    report = {
        'status': 'PASS',
        'claim': 'complete asymmetric physical row; continuous owner and equality arguments in hand manuscript',
        'first_vertical_interval': ['0', str(U)],
        'last_vertical_absolute_bound': str(delta),
        'total_variation_upper': str(U+delta),
        'polynomial_identities': 5,
        'concavity_endpoint_numerators': concavity,
        'positive_checks': checks,
        'whole_mask_closed': False,
    }
    target = Path(__file__).with_name('weak_outer_hand_asymmetric_row_arithmetic.json')
    target.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
