#!/usr/bin/env python3
"""Exact arithmetic certificate for the full-angle R0 torque correction.

Python standard library only. Builds the defining polynomials, certifies
all 1559 Bernstein coefficients by rational arithmetic, and reconstructs
all ordinary coefficients from the inverse Bernstein identities. No
sampling, numerical optimization, Lean compilation or CI is used.

Run normally to check. --json PATH additionally writes the complete exact
coefficient record; that output is optional and is not an input to checking.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
from math import comb
import json
from pathlib import Path

Poly = dict[tuple[int, int], F]
Matrix = list[list[F]]


def constant(c: F | int) -> Poly:
    return {(0, 0): F(c)} if c else {}


def add(a: Poly, b: Poly) -> Poly:
    c = a.copy()
    for k, v in b.items():
        c[k] = c.get(k, F(0)) + v
        if not c[k]:
            del c[k]
    return c


def scale(a: Poly, c: F | int) -> Poly:
    return {k: v * c for k, v in a.items() if v * c}


def sub(a: Poly, b: Poly) -> Poly:
    return add(a, scale(b, -1))


def mul(a: Poly, b: Poly) -> Poly:
    c: Poly = {}
    for (i, j), u in a.items():
        for (k, ell), v in b.items():
            key = (i + k, j + ell)
            c[key] = c.get(key, F(0)) + u * v
    return {k: v for k, v in c.items() if v}


def power(a: Poly, n: int) -> Poly:
    out = constant(1)
    for _ in range(n):
        out = mul(out, a)
    return out


def product(*polys: Poly) -> Poly:
    out = constant(1)
    for p in polys:
        out = mul(out, p)
    return out


def matrix(p: Poly) -> Matrix:
    n = max(i for i, _ in p)
    m = max(j for _, j in p)
    return [[p.get((i, j), F(0)) for j in range(m + 1)]
            for i in range(n + 1)]


def affine(coeffs: list[F], lo: F, hi: F) -> list[F]:
    n = len(coeffs) - 1
    return [sum((coeffs[i] * comb(i, j) * lo ** (i - j)
                 * (hi - lo) ** j for i in range(j, n + 1)), F(0))
            for j in range(n + 1)]


def rectangle_power(p: Matrix, xlo: F, xhi: F,
                    zlo: F, zhi: F) -> Matrix:
    n, m = len(p) - 1, len(p[0]) - 1
    first = [affine(row, zlo, zhi) for row in p]
    cols = [affine([first[i][j] for i in range(n + 1)], xlo, xhi)
            for j in range(m + 1)]
    return [[cols[j][i] for j in range(m + 1)] for i in range(n + 1)]


def bernstein(p: Matrix) -> Matrix:
    n, m = len(p) - 1, len(p[0]) - 1
    return [[sum((p[k][ell] * F(comb(i, k), comb(n, k))
                  * F(comb(j, ell), comb(m, ell))
                  for k in range(i + 1) for ell in range(j + 1)), F(0))
             for j in range(m + 1)] for i in range(n + 1)]


def inverse(b: Matrix) -> Matrix:
    n, m = len(b) - 1, len(b[0]) - 1
    return [[sum((b[i][j] * comb(n, i) * comb(n - i, k - i)
                  * comb(m, j) * comb(m - j, ell - j)
                  * (-1) ** (k + ell - i - j)
                  for i in range(k + 1) for j in range(ell + 1)), F(0))
             for ell in range(m + 1)] for k in range(n + 1)]


def reciprocal(p: Matrix) -> Matrix:
    """Exactly expand (1-u)^n p(1/(1-u),z), with n=degree_x p."""
    n, m = len(p) - 1, len(p[0]) - 1
    out = [[F(0) for _ in range(m + 1)] for _ in range(n + 1)]
    for i in range(n + 1):
        for j in range(m + 1):
            for k in range(n - i + 1):
                out[k][j] += p[i][j] * comb(n - i, k) * (-1) ** k
    # Check the whole reverse substitution, not selected evaluations:
    # x^n * q(1-1/x,z) must recover p(x,z).
    recovered = [[F(0) for _ in range(m + 1)] for _ in range(n + 1)]
    for k in range(n + 1):
        for j in range(m + 1):
            for ell in range(k + 1):
                recovered[n - ell][j] += out[k][j] * comb(k, ell) * (-1) ** ell
    assert recovered == p, 'Reciprocal inverse polynomial identity failed'
    return out


def build() -> tuple[Poly, Poly, Poly]:
    one = constant(1)
    x: Poly = {(1, 0): F(1)}
    z: Poly = {(0, 1): F(1)}
    den = add(one, power(z, 2))
    en = sub(one, power(z, 2))
    dn = scale(z, 2)
    assert add(power(en, 2), power(dn, 2)) == power(den, 2)
    aa = sub(mul(den, add(power(x, 2), one)), scale(mul(dn, x), 2))
    bb = add(mul(den, add(scale(power(x, 2), 2), one)),
             scale(mul(x, sub(en, dn)), 2))
    pp = sub(mul(den, add(power(x, 2), one)), scale(mul(dn, x), F(3, 2)))
    qq = add(mul(en, bb), scale(product(dn, x, add(en, dn)), F(1, 2)))
    tt = sub(scale(mul(x, den), F(1, 2)),
             add(scale(den, F(8, 25)), scale(dn, F(16, 25))))
    # a=aa/den, b=bb/den, p=pp/den, q=qq/(den*en), t=tt/den.
    # Hnum=den^4*en^2*(K^2*p^2*b-q^2*a-t^2*a*b).
    hh = sub(sub(scale(product(power(pp, 2), bb, den, power(en, 2)), F(79, 40)**2),
                 product(power(qq, 2), aa, den)),
             product(power(tt, 2), aa, bb, power(en, 2)))
    # Pnum=den^8*en^4*(H^2-4*q^2*t^2*a^2*b).
    pp_final = sub(power(hh, 2),
                   scale(product(power(qq, 2), power(tt, 2), power(aa, 2),
                                 bb, den, power(en, 2)), 4))
    # Znum=den^3*en^2*(K^2*p^2*b-q^2*a).
    zz = sub(scale(product(power(pp, 2), bb, power(en, 2)), F(79, 40)**2),
             product(power(qq, 2), aa))
    return hh, pp_final, zz


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--json', type=Path)
    args = parser.parse_args()
    hh, pp, zz = build()
    hm, pm, zm = map(matrix, (hh, pp, zz))
    assert (len(hm)-1, len(hm[0])-1) == (6, 12)
    assert (len(pm)-1, len(pm[0])-1) == (12, 24)
    assert (len(zm)-1, len(zm[0])-1) == (6, 10)
    hr, pr = reciprocal(hm), reciprocal(pm)
    domains = [
        ('H_small', hm, (F(0), F(1), -F(5, 12), F(1, 4)), F(2)),
        ('P_small', pm, (F(0), F(1), -F(5, 12), F(1, 4)), F(2)),
        ('Z_small', zm, (F(0), F(1), F(1, 4), F(5, 12)), F(1)),
        ('H_large', hr, (F(0), F(1), -F(5, 12), F(5, 12)), F(7, 10)),
        ('P_large_1', pr, (F(0), F(1, 2), -F(5, 12), F(5, 12)), F(1, 2)),
        ('P_large_2', pr, (F(1, 2), F(3, 4), -F(5, 12), F(5, 12)), F(9, 100)),
        ('P_large_3', pr, (F(3, 4), F(1), -F(5, 12), F(5, 12)), F(9, 100)),
    ]
    record = {'arithmetic': 'exact rational', 'domains': []}
    count = 0
    for name, source, box, lower in domains:
        transformed = rectangle_power(source, *box)
        coeffs = bernstein(transformed)
        assert inverse(coeffs) == transformed, name + ': inverse identity failed'
        assert all(c > lower for row in coeffs for c in row), name + ': strict sign failed'
        n, m = len(coeffs)-1, len(coeffs[0])-1
        count += (n+1)*(m+1)
        print(f'PASS {name}: degree ({n},{m}), {(n+1)*(m+1)} coefficients > {lower}; full inverse.')
        record['domains'].append({
            'name': name, 'box': [str(t) for t in box],
            'degree': [n, m], 'strict_lower_bound': str(lower),
            'power': [[str(t) for t in row] for row in transformed],
            'bernstein': [[str(t) for t in row] for row in coeffs],
        })
    assert count == 1559
    assert F(17, 12)**2 - 2 == F(1, 144) > 0
    assert F(8, 25) + F(16, 25)*F(8, 17) - F(1, 2) == F(103, 850) > 0
    assert 2*F(33, 25)**2 + F(16, 25)**2 == F(2434, 625)
    assert F(79, 40)**2 - F(2434, 625) == F(249, 40000) > 0
    record['coefficient_count'] = count
    record['verification'] = ['all exact strict signs', 'all full Bernstein inverse identities',
                              'both reciprocal inverse polynomial identities', 'unit half-angle identity',
                              'all endpoint and final Cauchy reserves']
    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps(record, indent=2) + '\n')
        print('Wrote complete coefficient record:', args.json)
    print('PASS: all 1559 exact signs, all inverse identities, and every rational reserve.')


if __name__ == '__main__':
    main()
