#!/usr/bin/env python3
"""Write the polynomial rows of the central band.

    python3 -I scripts/eight/generate_polynomial_rows.py [--root ROOT]

In SquaresInCircles/Eight/CentralCore.lean (namespace `CentralBand`) the positivity of the
polynomials `centralBandP C D` on [0, 1] of
SquaresInCircles/Eight/Arithmetic/CentralBandPolynomials.lean, in the half-angle tangent u,
gives the bound `primary_upper`. Together with `secondary_upper`, it gives the side inequalities
of a square in `transverse_segment_sides`, `bandA_sides` and `bandB_sides`, each for its own
parameters. The polynomials `centralBandV A C D` used by `secondary_upper` are proved positive
by completing a square in Lean and need no rows. The script expands each of the P polynomials
in powers of u, cuts its interval
into pieces, and computes on each piece the exact Bernstein coefficients of the expansion, with
the margin half the least of them. It writes the rows to
SquaresInCircles/Eight/Generated/WholePairPolynomialsNNN.lean, 24 to a module, each with a theorem
`_valid`, which the kernel checks by `BernsteinRow.check`, and a theorem `_positive`; the module
WholePairPolynomials.lean, which imports them; and polynomial_generation_index.json, which lists
the declarations. ROOT is the root of the repository, by default the one holding this script.
"""
from __future__ import annotations
from fractions import Fraction as Q
from math import comb
from pathlib import Path
import argparse
import json


def rat(x):
    """A rational from a numeral or a string such as '3/14'."""
    return Q(str(x))


def leanq(x):
    """A rational as a Lean numeral."""
    x = rat(x)
    return str(x.numerator) if x.denominator == 1 else f"({x.numerator}/{x.denominator})"


def bernstein(p, lo, hi, n):
    """The Bernstein coefficients of degree n on [lo, hi] of the polynomial p, given by its
    coefficients in increasing degree: p(lo + (hi - lo) t) is expanded in powers of t and then
    written in the Bernstein basis of degree n."""
    p = list(map(rat, p)) + [Q(0)] * (n + 1 - len(p))
    lo, hi = rat(lo), rat(hi)
    translated = [sum((p[j] * comb(j, k) * lo ** (j - k) * (hi - lo) ** k for j in range(k, n + 1)),
                      Q(0)) for k in range(n + 1)]
    return [sum((translated[j] * Q(comb(k, j), comb(n, j)) for j in range(k + 1)), Q(0))
            for k in range(n + 1)]


# the sum, the product and a scalar multiple of polynomials given by their coefficient lists
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


# the Lean names of the three polynomials (Arithmetic/CentralBandPolynomials.lean) and the theorems
# of CentralCore.lean that use them
LEAN_NAMES = {'segment': 'centralBandP (11/12) (7/20)',
              'bandA': 'centralBandP bandA_Cminus bandA_D',
              'bandB': 'centralBandP bandB_Cminus bandB_D'}
USED_BY = {'segment': 'transverse_segment_sides', 'bandA': 'bandA_sides', 'bandB': 'bandB_sides'}


def central_band_rows():
    """The rows: for each set of parameters the polynomial P = `centralBandP C₋ D`
    in u, with z = 1 + u², c = 1 - u², s = 2u, on the pieces of a cut of [0, 1].
    Each row is (declaration, docstring, label, polynomial,
    piece, degree)."""
    z = [Q(1), Q(0), Q(1)]
    c = [Q(1), Q(0), Q(-1)]
    s = [Q(0), Q(2)]
    # (name, C₋, D, cuts of [0, 1] for P)
    specs = [('segment', Q(11, 12), Q(7, 20), ['0', '1/4', '1/2', '1']),
             ('bandA', Q(10007, 10000) * Q(9308368, 10 ** 7),
              Q(10007, 10000) * Q(365435, 10 ** 6),
              ['0', '1/4', '3/8', '7/16', '1/2', '1']),
             ('bandB', Q(41, 40) * Q(9286, 10000),
              Q(41, 40) * Q(371, 1000), ['0', '1/2', '1'])]
    out = []
    for name, Cm, D, pcuts in specs:
        H = padd(padd(pscale(Q(1, 2), z), pscale(Cm, c)), pscale(-D, s))
        P = padd(padd(pmul(pmul(H, H), z), pmul(pmul(H, c), padd(c, s))),
                 pscale(Q(1, 2) - Q(9789, 2500), pmul(pmul(c, c), z)))
        for i, (lo, hi) in enumerate(zip(pcuts, pcuts[1:])):
            out.append((f'central_{name}_P{i}',
                        f'The polynomial `{LEAN_NAMES[name]}` for `{USED_BY[name]}`,\n'
                        f'expanded in powers of `u`, on `[{lo}, {hi}]`.',
                        f'{name} P, row {i}', P, [lo, hi], len(P) - 1))
    return out


HEADER = ['module', '', 'public import SquaresInCircles.Eight.Arithmetic.BernsteinCheck', '',
          '/-!',
          '# Eight squares: the polynomial rows of the central band',
          '',
          'The polynomials `centralBandP` of',
          '`Arithmetic/CentralBandPolynomials.lean` for `transverse_segment_sides`, `bandA_sides`',
          'and `bandB_sides` of `CentralCore.lean`, expanded in powers of the half-angle tangent',
          '`u`, each on the pieces of a cut of `[0, 1]`.',
          'A row (`Arithmetic.BernsteinRow`) holds the expansion,',
          'the piece and the exact Bernstein coefficients there. The kernel checks each row by',
          '`BernsteinRow.check` (`_valid`), and its positive coefficients make the polynomial',
          'positive on the piece (`_positive`). `Arithmetic/CentralBandPolynomials.lean`',
          'identifies each expansion with its polynomial and joins the pieces.',
          'The polynomials `centralBandV` instead use a quadratic lower bound and a completed square.',
          'Written by',
          '`scripts/eight/generate_polynomial_rows.py`.',
          '-/', '',
          '@[expose] public section', 'noncomputable section', 'open scoped BigOperators',
          'namespace SquaresInCircles.Eight.Generated', '']


def main():
    """Write the row modules, the module that imports them, and the index."""
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
        for full, doc, name, p, bounds, n in rows:
            lo, hi = map(rat, bounds)
            p = list(map(rat, p))
            b = bernstein(p, lo, hi, n)
            if min(b) <= 0:
                raise SystemExit(f'{full}: a Bernstein coefficient on [{lo}, {hi}] is not positive')
            margin = min(b) / 2
            text += [f'/-- {doc} -/',
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
                                 for x in chunks) + '\n'
        + '\n/-!\n# Eight squares: the polynomial rows of the central band\n\n'
          'The polynomial rows of the central band, gathered from their modules;\n'
          '`Arithmetic/CentralBandPolynomials.lean` identifies them with the polynomials\n'
          '`centralBandP`. Written by\n'
          '`scripts/eight/generate_polynomial_rows.py`.\n'
          '-/\n')
    (output / 'polynomial_generation_index.json').write_text(json.dumps(
        {'schema': 'eight-polynomial-v1', 'rows': len(entries), 'chunks': chunks,
         'sources': [{'declaration': x[0], 'polynomial': x[2]} for x in entries]},
        indent=2) + '\n')
    print(json.dumps({'polynomial_rows': len(entries), 'chunks': len(chunks)}))


if __name__ == '__main__':
    main()
