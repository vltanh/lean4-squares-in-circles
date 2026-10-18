#!/usr/bin/env python3
"""Emit the polynomial rows of the central band (CENTRAL_BAND_COMMON_POINT_LEMMAS.md).

Each row is a polynomial on a closed interval with its exact Bernstein coefficients there;
`BernsteinRow.check` verifies it in the kernel and gives its positivity on the interval. The
rows are written to SquaresInCircles/Eight/Generated/WholePairPolynomialsNNN.lean (24 a module),
with the umbrella WholePairPolynomials.lean and polynomial_generation_index.json.
"""
from __future__ import annotations
from fractions import Fraction as Q
from math import comb
from pathlib import Path
import argparse
import json


def rat(x):
    return Q(str(x))


def leanq(x):
    x = rat(x)
    return str(x.numerator) if x.denominator == 1 else f"({x.numerator}/{x.denominator})"


def bernstein(p, lo, hi, n):
    p = list(map(rat, p)) + [Q(0)] * (n + 1 - len(p))
    lo, hi = rat(lo), rat(hi)
    translated = [sum((p[j] * comb(j, k) * lo ** (j - k) * (hi - lo) ** k for j in range(k, n + 1)),
                      Q(0)) for k in range(n + 1)]
    return [sum((translated[j] * Q(comb(k, j), comb(n, j)) for j in range(k + 1)), Q(0))
            for k in range(n + 1)]


def padd(a, b):
    return [(a[i] if i < len(a) else Q(0)) + (b[i] if i < len(b) else Q(0))
            for i in range(max(len(a), len(b)))]


def pmul(a, b):
    out = [Q(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def pscale(c, a):
    return [rat(c) * x for x in a]


def central_band_rows():
    z = [Q(1), Q(0), Q(1)]
    c = [Q(1), Q(0), Q(-1)]
    s = [Q(0), Q(2)]
    specs = [('segment', Q(1, 2), Q(11, 12), Q(11, 12), Q(7, 20), ['0', '1/4', '1/2', '1'],
              ['0', '3/14', '3/7']),
             ('bandA', Q(5007, 10000), Q(10007, 10000) * Q(9308368, 10 ** 7),
              Q(10007, 10000) * Q(9308369, 10 ** 7), Q(10007, 10000) * Q(365435, 10 ** 6),
              ['0', '1/4', '3/8', '7/16', '1/2', '1'], ['0', '3/14', '9/28', '3/7']),
             ('bandB', Q(107, 200), Q(41, 40) * Q(9286, 10000), Q(41, 40) * Q(9287, 10000),
              Q(41, 40) * Q(371, 1000), ['0', '1/2', '1'], ['0', '3/14', '15/56', '9/28', '3/7'])]
    out = []
    for name, A, Cm, Cp, D, pcuts, vcuts in specs:
        H = padd(padd(pscale(Q(1, 2), z), pscale(Cm, c)), pscale(-D, s))
        P = padd(padd(pmul(pmul(H, H), z), pmul(pmul(H, c), padd(c, s))),
                 pscale(Q(1, 2) - Q(9789, 2500), pmul(pmul(c, c), z)))
        V = padd(padd(pscale(Q(1, 2), pmul(c, z)), pscale(A, pmul(s, z))),
                 padd(pscale(-Cp, pmul(s, c)), pscale(-D, pmul(c, c))))
        for letter, poly, cuts in [('P', P, pcuts), ('V', V, vcuts)]:
            for i, (lo, hi) in enumerate(zip(cuts, cuts[1:])):
                out.append((f'central_{name}_{letter}{i}', 'CENTRAL_BAND_COMMON_POINT_LEMMAS.md',
                            f'{name} {letter}, row {i}', poly, [lo, hi], len(poly) - 1))
    return out


HEADER = ['module', '', 'public import SquaresInCircles.Eight.Arithmetic.BernsteinCheck', '',
          '/-! Polynomial rows of schema eight-polynomial-v1: a polynomial, an interval, and '
          'Bernstein',
          'coefficients on that interval. `BernsteinRow.check` verifies a row in the kernel. -/', '',
          '@[expose] public section', 'noncomputable section', 'open scoped BigOperators',
          'namespace SquaresInCircles.Eight.Generated', '']


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[2])
    args = ap.parse_args()
    output = args.root / 'SquaresInCircles/Eight/Generated'
    output.mkdir(parents=True, exist_ok=True)
    entries = central_band_rows()
    chunks = []
    for group in range((len(entries) + 23) // 24):
        rows = entries[24 * group:24 * (group + 1)]
        module = f'WholePairPolynomials{group:03d}'
        text = list(HEADER)
        for full, source, name, p, bounds, n in rows:
            lo, hi = map(rat, bounds)
            p = list(map(rat, p))
            b = bernstein(p, lo, hi, n)
            margin = min(b) / 2
            text += [f'/-- Source: {source}, polynomial {name}. -/',
                     f'def {full} : Arithmetic.BernsteinRow :=',
                     f'  {{ interval := ⟨{leanq(lo)},{leanq(hi)}⟩',
                     '    polynomial := [' + ', '.join(map(leanq, p)) + ']',
                     f'    degree := {n}',
                     '    coefficients := [' + ', '.join(map(leanq, b)) + '] }', '',
                     f'theorem {full}_valid : {full}.Valid {leanq(margin)} :=',
                     '  Arithmetic.BernsteinRow.valid_of_check (by decide +kernel)',
                     f'theorem {full}_positive {{x : ℝ}} (hx : ({leanq(lo)} : ℝ) ≤ x ∧ x ≤ '
                     f'{leanq(hi)}) :',
                     f'    0 < {full}.polynomial.eval x :=',
                     f'  {full}_valid.positive_of_eq (by norm_num) rfl (by push_cast; exact hx)']
        text += ['end SquaresInCircles.Eight.Generated', '']
        (output / f'{module}.lean').write_text('\n'.join(text))
        chunks.append(module)
    (output / 'WholePairPolynomials.lean').write_text(
        'module\n\n' + '\n'.join(f'public import SquaresInCircles.Eight.Generated.{x}'
                                 for x in chunks) + '\n')
    (output / 'polynomial_generation_index.json').write_text(json.dumps(
        {'schema': 'eight-polynomial-v1', 'rows': len(entries), 'chunks': chunks,
         'sources': [{'declaration': x[0], 'source': x[1], 'polynomial': x[2]} for x in entries]},
        indent=2) + '\n')
    print(json.dumps({'polynomial_rows': len(entries), 'chunks': len(chunks)}))


if __name__ == '__main__':
    main()
