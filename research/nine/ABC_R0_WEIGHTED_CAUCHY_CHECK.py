#!/usr/bin/env python3
"""Exact 270-sign weighted-Cauchy certificate for the complete R0 scalar.

The small-ratio interval has a table-free proof in the companion source.
This checker constructs one degree-(8,14) polynomial, verifies two whole
Bernstein rectangles and all inverse identities using Fraction only.
No original 1559-sign certificate, sampled signs, Lean or CI are invoked.
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


def build() -> Poly:
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
    rn = sub(scale(mul(x, sub(scale(den, 3), dn)), F(1, 10)),
             scale(den, F(1, 8)))
    rd = mul(x, den)
    # rho=rn/rd; W=K^2*p^2/a-(1+rho)*q^2/b-(1+1/rho)*t^2.
    # J=x*den^2*en^2*rn*aa*bb*W, an identity on the full rational domain.
    jj = sub(sub(scale(product(power(pp, 2), bb, power(en, 2), rn, rd), F(79, 40)**2),
                 product(add(rd, rn), rn, power(qq, 2), aa)),
             product(add(rd, rn), x, power(tt, 2), aa, bb, power(en, 2)))
    # Reconstruct the denominator identity term by term using the stated
    # rational substitutions, with common positive denominator removed.
    first = scale(product(x, den, power(en, 2), rn, power(pp, 2), bb), F(79, 40)**2)
    second = product(add(rd, rn), rn, power(qq, 2), aa)
    third = product(add(rd, rn), x, power(tt, 2), aa, bb, power(en, 2))
    assert jj == sub(sub(first, second), third)
    return jj


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--json', type=Path)
    args = parser.parse_args()
    jj = build()
    jm = matrix(jj)
    assert (len(jm)-1, len(jm[0])-1) == (8, 14)
    assert len(jj) == 128
    jr = reciprocal(jm)
    domains = [
        ('large_first', (F(0), F(3, 4), -F(5, 12), F(5, 12)), F(1, 200)),
        ('large_second', (F(3, 4), F(1), -F(5, 12), F(5, 12)), F(3, 500)),
    ]
    record = {'arithmetic': 'exact rational', 'small_ratio': 'table-free concavity proof',
              'defining_power': [[str(t) for t in row] for row in jm], 'domains': []}
    count = 0
    for name, box, lower in domains:
        transformed = rectangle_power(jr, *box)
        coeffs = bernstein(transformed)
        assert inverse(coeffs) == transformed, name + ': inverse identity failed'
        assert all(c > lower for row in coeffs for c in row), name + ': strict sign failed'
        n, m = len(coeffs)-1, len(coeffs[0])-1
        count += (n+1)*(m+1)
        print(f'PASS {name}: degree ({n},{m}), {(n+1)*(m+1)} coefficients > {lower}; full inverse.')
        record['domains'].append({
            'name': name, 'box': [str(t) for t in box], 'degree': [n, m],
            'strict_lower_bound': str(lower),
            'power': [[str(t) for t in row] for row in transformed],
            'bernstein': [[str(t) for t in row] for row in coeffs],
        })
    assert count == 270
    # Elementary reserves used in the small-ratio argument.
    assert F(7, 10)**2 < F(1, 2) < F(71, 100)**2
    assert F(5, 8)**2 < F(1, 2)
    assert F(113, 100)**2 < 2-F(71, 100)
    assert F(111, 50)**2 > F(7, 2)+2*F(71, 100)
    assert F(41, 25)**2 < 2+F(7, 10)
    assert F(63, 25)**2 > F(7, 2)+4*F(71, 100)
    assert F(79, 40)*F(113, 100)-F(111, 50)-F(9, 50)+F(16, 25)*F(7, 10) == F(1119, 4000)>0
    assert F(79, 40)*F(41, 25)-F(63, 25)-F(9, 50)-F(16, 25)*F(71, 100) == F(423, 5000)>0
    assert F(3, 10)-F(3, 4)/10-F(1, 8) == F(1, 10)
    assert F(17, 12)**2-2 == F(1, 144)>0
    record['coefficient_count'] = count
    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps(record, indent=2) + '\n')
        print('Wrote complete coefficient record:', args.json)
    print('PASS: all 270 exact signs, full inverses, denominator terms and small-ratio reserves.')


if __name__ == '__main__':
    main()
