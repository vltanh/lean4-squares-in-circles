#!/usr/bin/env python3
"""Independent exact coefficient checker of a proper row-profile certificate.

Standard library. Imports neither emitter nor certificate producer nor SymPy.
The original nine-square geometric-to-row-root implication is proved in the
companion manuscript. This checker verifies its exact polynomial identity.
"""
from fractions import Fraction as F
from pathlib import Path
import copy
import hashlib
import json
import sys


def need(ok, text):
    if not ok:
        raise ValueError(text)


# Polynomial = {sorted monomial variable tuple: rational coefficient}.
def const(q):
    return {(): F(q)} if q else {}


def var(name):
    return {(name,): F(1)}


def add(*ps):
    out = {}
    for p in ps:
        for m, c in p.items():
            out[m] = out.get(m, F(0)) + c
    return {m: c for m, c in out.items() if c}


def scale(c, p):
    return {m: F(c)*q for m, q in p.items() if F(c)*q}


def mul(a, b):
    out = {}
    for m, c in a.items():
        for n, d in b.items():
            k = tuple(sorted(m+n))
            out[k] = out.get(k, F(0)) + c*d
    return {m: c for m, c in out.items() if c}


def square(p):
    return mul(p, p)


def hypotheses():
    """Fixed physical root; it is NOT supplied by untrusted certificate data."""
    x = [var(f'x_{i}') for i in range(7)]
    A, B, q = var('ya'), var('yb'), var('q')
    def corner(xp, yp):
        return add(q, scale(-1, square(xp)), scale(-1, square(yp)))
    h = {
        'corner_0_1': corner(add(x[0], const(-F(1, 2))), add(A, const(F(1, 2)))),
        'corner_3_3': corner(add(x[3], const(F(1, 2))), add(A, const(F(1, 2)))),
        'corner_4_0': corner(add(x[4], const(-F(1, 2))), add(B, const(-F(1, 2)))),
        'corner_6_2': corner(add(x[6], const(F(1, 2))), add(B, const(-F(1, 2)))),
        'row_gap': add(A, scale(-1, B), const(-1)),
    }
    for i, j in ((0, 1), (1, 2), (2, 3), (4, 5), (5, 6)):
        h[f'gap_{i}_{j}'] = add(x[j], scale(-1, x[i]), const(-1))
    return h


def verify(certificate):
    need(certificate.get('schema') == 'row43-quadratic-v1', 'unknown certificate schema')
    need(F(certificate['target']) == F(1105, 256), 'wrong target')
    h = hypotheses()
    weights = certificate['weighted_hypotheses']
    need(set(weights) == set(h), 'missing/extra original hypothesis')
    total = {}
    for name, raw in weights.items():
        w = F(raw)
        need(w >= 0, 'negative hypothesis weight')
        total = add(total, scale(w, h[name]))
    allowed = {f'x_{i}' for i in range(7)} | {'ya', 'yb', 'q', 'ONE'}
    need(len(certificate['squares']) == 6, 'six squared affine terms required')
    for item in certificate['squares']:
        w = F(item['weight'])
        need(w >= 0, 'negative square weight')
        p = {}
        for name, raw in item['affine'].items():
            need(name in allowed, 'unknown variable')
            p = add(p, scale(F(raw), const(1) if name == 'ONE' else var(name)))
        total = add(total, scale(w, square(p)))
    residual = add(var('q'), const(-F(1105, 256)), scale(-1, total))
    need(not residual, f'nonzero coefficient residual: {residual}')
    return {'identity': 'q-1105/256=sum(nonnegative hypotheses and squares)',
            'weighted_physical_hypotheses': len(h), 'nonnegative_squares': 6,
            'residual_monomials': len(residual)}


def main():
    path = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).with_name('row43_certificate.json')
    raw = path.read_bytes()
    c = json.loads(raw)
    result = verify(c)
    # The checker must reject a changed coefficient and a stronger fake target.
    corrupt = copy.deepcopy(c)
    corrupt['weighted_hypotheses']['corner_0_1'] = '1'
    for bad in (corrupt, dict(c, target='5')):
        try:
            verify(bad)
        except ValueError:
            continue
        raise AssertionError('corrupted certificate accepted')
    result.update({'result': 'PASS', 'certificate_sha256': hashlib.sha256(raw).hexdigest(),
                   'arithmetic': 'exact rational coefficient expansion',
                   'counterexample_mutations_rejected': 2,
                   'proper_row_family_lower_bound_proved': True,
                   'arbitrary_packing_lower_bound_proved': False,
                   'separate_human_review_performed': False})
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
