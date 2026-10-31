#!/usr/bin/env python3
"""Exact 49-sign residual circle-slope proof for the double-shared C6.

The companion source proves the whole torque-slope inequality analytically.
This self-contained checker reconstructs one degree-(6,6) Q(sqrt(2))
polynomial, all signs, its exact division, and the full Bernstein inverse.
It imports neither the older 209-sign proof nor any stored certificate.
"""
from fractions import Fraction as F
from math import comb
import argparse
import json
from pathlib import Path

ZERO = (F(0), F(0))
ONE = (F(1), F(0))
ROOT_HALF = (F(0), F(1, 2))


def qa(a, b):
    return (a[0] + b[0], a[1] + b[1])


def qm(a, b):
    return (a[0]*b[0] + 2*a[1]*b[1], a[0]*b[1] + a[1]*b[0])


def qi(a):
    denominator = a[0]*a[0] - 2*a[1]*a[1]
    return (a[0]/denominator, -a[1]/denominator)


def sign(a):
    x, y = a
    if x == 0:
        return (y > 0) - (y < 0)
    if y == 0:
        return (x > 0) - (x < 0)
    if x > 0 and y > 0:
        return 1
    if x < 0 and y < 0:
        return -1
    difference = x*x - 2*y*y
    return ((difference > 0) - (difference < 0)) * (1 if x > 0 else -1)


def cn(a):
    return {(0, 0): a} if a != ZERO else {}


def add(a, b):
    out = a.copy()
    for ij, value in b.items():
        out[ij] = qa(out.get(ij, ZERO), value)
        if out[ij] == ZERO:
            del out[ij]
    return out


def scale(a, value):
    return {ij: qm(q, value) for ij, q in a.items() if qm(q, value) != ZERO}


def rs(a, value):
    return scale(a, (F(value), F(0)))


def sub(a, b):
    return add(a, rs(b, -1))


def mul(a, b):
    out = {}
    for (i, j), v in a.items():
        for (k, ell), w in b.items():
            ij = (i+k, j+ell)
            out[ij] = qa(out.get(ij, ZERO), qm(v, w))
    return {ij: v for ij, v in out.items() if v != ZERO}


def product(*args):
    out = cn(ONE)
    for a in args:
        out = mul(out, a)
    return out


def sq(a):
    return mul(a, a)


def divide(a, b):
    remainder = a.copy()
    quotient = {}
    leftover = {}
    lead = max(b)
    while remainder:
        ij = max(remainder)
        value = remainder[ij]
        if ij[0] >= lead[0] and ij[1] >= lead[1]:
            exponent = (ij[0]-lead[0], ij[1]-lead[1])
            coeff = qm(value, qi(b[lead]))
            quotient[exponent] = qa(quotient.get(exponent, ZERO), coeff)
            remainder = sub(remainder, mul({exponent: coeff}, b))
        else:
            leftover[ij] = value
            del remainder[ij]
    return quotient, leftover


def build():
    one = cn(ONE)
    x = {(1, 0): ONE}
    y = {(0, 1): ONE}
    k = cn((-F(1), F(1)))
    a = rs(x, F(3, 20))
    b = mul(k, y)
    ds = add(one, sq(a))
    dw = add(one, sq(b))
    sn = scale(add(sub(one, sq(a)), rs(a, 2)), ROOT_HALF)
    cc = scale(add(sub(sq(a), one), rs(a, 2)), ROOT_HALF)
    uu = scale(sub(sub(one, sq(b)), rs(b, 2)), ROOT_HALF)
    vv = scale(add(sub(one, sq(b)), rs(b, 2)), ROOT_HALF)
    assert add(sq(sn), sq(cc)) == sq(ds)
    assert add(sq(uu), sq(vv)) == sq(dw)
    en = sub(sub(mul(ds, dw), add(mul(cc, uu), mul(sn, vv))), mul(ds, uu))
    base = product(ds, dw, vv)
    pp = add(add(base, product(ds, vv, add(uu, vv))), product(vv, dw, sn))
    qq = sub(add(base, product(ds, vv, sub(vv, uu))), product(vv, dw, cc))
    rr = sub(add(base, product(ds, vv, sub(uu, vv))), mul(dw, en))
    ss = add(rs(base, 2), product(ds, vv, add(uu, vv)))
    ab = add(sq(pp), sq(qq))
    cd = add(sq(rr), sq(ss))
    an = sub(mul(ss, ab), mul(qq, cd))
    bn = sub(mul(pp, cd), mul(rr, ab))
    raw = sub(rs(bn, 14), rs(an, 15))
    factor = product(dw, dw, vv)
    result, remainder = divide(raw, factor)
    assert not remainder
    assert mul(factor, result) == raw
    assert (max(i for i, j in result), max(j for i, j in result)) == (6, 6)
    return result


def bernstein(poly):
    result = {}
    for i in range(7):
        for j in range(7):
            value = ZERO
            for (a, b), q in poly.items():
                if a <= i and b <= j:
                    factor = F(comb(i, a), comb(6, a))*F(comb(j, b), comb(6, b))
                    value = qa(value, qm(q, (factor, F(0))))
            result[i, j] = value
    return result


def inverse(bs):
    result = {}
    for a in range(7):
        for b in range(7):
            value = ZERO
            for i in range(a+1):
                for j in range(b+1):
                    factor = (comb(6, i)*comb(6-i, a-i)*comb(6, j)*
                              comb(6-j, b-j)*(-1)**(a+b-i-j))
                    value = qa(value, qm(bs[i, j], (F(factor), F(0))))
            if value != ZERO:
                result[a, b] = value
    return result


def encode(poly):
    return [[i, j, str(q[0]), str(q[1])] for (i, j), q in sorted(poly.items())]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--json', type=Path)
    args = parser.parse_args()
    poly = build()
    bs = bernstein(poly)
    assert len(bs) == 49
    assert all(sign(qa(value, (-F(7), F(0)))) > 0 for value in bs.values())
    assert inverse(bs) == poly
    # Elementary domain and analytic torque-slope reserves.
    assert 13**2 > 2*8**2
    assert 2*23452**2-33153**2 == 871199 > 0
    assert 409**2-2*289**2 == 239 > 0
    assert 2*F(3, 20)/(1+F(3, 20)**2) == F(120, 409)
    if args.json:
        record = {'arithmetic': 'Q(sqrt(2))', 'degree': [6, 6],
                  'coefficient_count': 49, 'strict_lower_bound': '7',
                  'ordinary': encode(poly), 'bernstein': encode(bs)}
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps(record, indent=2)+'\n')
    print('PASS: degree (6,6), all 49 coefficients >7; full division and Bernstein inverse.')


if __name__ == '__main__':
    main()
