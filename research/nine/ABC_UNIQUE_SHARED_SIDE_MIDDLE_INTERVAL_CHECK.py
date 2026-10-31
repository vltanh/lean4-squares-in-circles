#!/usr/bin/env python3
"""Exact one-rectangle certificate for the shared unique-C side proof.

Reconstructs the defining polynomial, all 36 exact Bernstein coefficients,
their complete inverse identity, and the formula-to-scalar normalization.
Only standard-library rational/integer arithmetic is used.
"""
from argparse import ArgumentParser
from fractions import Fraction
from math import comb, gcd
from functools import reduce
from pathlib import Path
import json


def clean(p):
    return {e: c for e, c in p.items() if c}


def const(c):
    return {(0, 0): c} if c else {}


def add(*ps):
    out = {}
    for p in ps:
        for e, c in p.items():
            out[e] = out.get(e, 0) + c
    return clean(out)


def scale(c, p):
    return clean({e: c*v for e, v in p.items()})


def mul(p, q):
    out = {}
    for (i, j), a in p.items():
        for (k, ell), b in q.items():
            e = (i+k, j+ell)
            out[e] = out.get(e, 0) + a*b
    return clean(out)


def evaluate(p, lam, z):
    return sum(c*lam**i*z**j for (i, j), c in p.items())


def polynomial():
    lam, z = {(1, 0): 1}, {(0, 1): 1}
    B = add(const(750), scale(90, z))
    H = add(const(315), scale(-81, z),
            mul(lam, add(const(85), scale(81, z))))
    B2, H2 = mul(B, B), mul(H, H)
    D = add(B2, H2)
    raw = add(
        mul(add(scale(4, B), scale(-2, H), const(-4200)), mul(D, D)),
        scale(4, mul(mul(mul(B, H), add(H, const(1200))), D)),
        scale(-2400, mul(B2, H2)))
    common = reduce(gcd, map(abs, raw.values()))
    assert common == 2
    p = {e: c//common for e, c in raw.items()}
    assert max(i for i, j in p) == max(j for i, j in p) == 5
    assert len(p) == 36
    return raw, p


def certify():
    raw, p = polynomial()
    rows = [[sum(Fraction(c)*Fraction(comb(i, r), comb(5, r))
                  * Fraction(comb(j, s), comb(5, s))
                  for (r, s), c in p.items() if r <= i and s <= j)
             for j in range(6)] for i in range(6)]
    assert all(c > 0 for row in rows for c in row)
    assert all(3*c > 2*rows[0][0] for row in rows for c in row)
    for r in range(6):
        for s in range(6):
            reconstructed = sum(
                rows[i][j]*comb(5, i)*comb(5-i, r-i)*(-1)**(r-i)
                * comb(5, j)*comb(5-j, s-j)*(-1)**(s-j)
                for i in range(r+1) for j in range(s+1))
            assert reconstructed == p.get((r, s), 0), (r, s)
    floors = [[int(100*c//rows[0][0]) for c in row] for row in rows]
    assert [min(row) for row in floors] == [68,280,464,654,849,1051]

    # Rebuild the rational scalar polynomial independently and compare
    # every ordinary coefficient of the clearing identity. No sampled
    # substitution is used in this or the sign certificate.
    lam, z = {(1, 0): 1}, {(0, 1): 1}
    beta = add(const(Fraction(5, 4)), scale(Fraction(3, 20), z))
    low = add(const(Fraction(33, 20)), scale(Fraction(-9, 10), beta))
    h = add(low, mul(lam, add(const(Fraction(2, 3)), scale(-1, low))))
    beta2, h2 = mul(beta, beta), mul(h, h)
    d = add(beta2, h2)
    scalar = add(
        mul(add(scale(4, beta), scale(-2, h), const(-7)), mul(d, d)),
        scale(4, mul(mul(mul(beta, h), add(h, const(2))), d)),
        scale(-4, mul(beta2, h2)))
    assert scale(600**5, scalar) == raw
    return {
        'degrees':[5,5], 'primitive_gcd':2,
        'normalized_floor_100':floors,
        'power':[[i,j,str(c)] for (i,j),c in sorted(p.items())],
        'bernstein':[[str(c) for c in row] for row in rows],
        'normalization':'raw=600^5*P(beta,h); primitive=raw/2',
    }


def main():
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('--write-certificate',type=Path)
    args=parser.parse_args()
    result=certify()
    if args.write_certificate:
        args.write_certificate.write_text(json.dumps(result,indent=2)+'\n')
    print('PASS: all 36 exact coefficients positive, all normalized above 2/3,')
    print('      all 36 inverse identities, and the scalar normalization.')
    print('Normalized floor table:',result['normalized_floor_100'])


if __name__=='__main__':
    main()
