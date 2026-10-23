"""Exact interval exclusion for a unit square missing its block-side marker.

Research certificate for the centered 2-by-2 block subcase only. No claim
about unrestricted eleven-square global sharpness is made by this script.
"""
from fractions import Fraction as F
from pathlib import Path
import json

U = F(4999, 1000)


def add(x, y):
    return x[0] + y[0], x[1] + y[1]


def neg(x):
    return -x[1], -x[0]


def sub(x, y):
    return add(x, neg(y))


def mul(x, y):
    vals = [a * b for a in x for b in y]
    return min(vals), max(vals)


def scalar(x, s):
    return mul(x, (s, s))


def sq_abs_min(x):
    if x[0] <= 0 <= x[1]:
        return F(0)
    return min(abs(x[0]), abs(x[1]))


def frames(t):
    lo, hi = t
    c = ((1-hi*hi)/(1+hi*hi), (1-lo*lo)/(1+lo*lo))
    s = (2*lo/(1+lo*lo), 2*hi/(1+hi*hi))
    return c, s


def exclusion(box, kind, axis, sign):
    a, b, t = box
    if t[0]*t[0]+2*t[0] > 1:
        return 'frame-chart'
    am, bm = sq_abs_min(a), sq_abs_min(b)
    if am*am+bm*bm+am+bm+F(1, 2) > U:
        return 'corner-radius'
    c, s = frames(t)
    if kind == 'own':
        sep = sub(sub(a, add(c, s)), (F(1, 2), F(1, 2)))
    else:
        sep = sub(sub(mul(c, a), mul(s, b)),
                  add((F(1), F(1)), scalar(add(c, s), F(1, 2))))
    if sep[1] < 0:
        return 'block-separator'
    delta = sub(a, scalar(c, F(3, 2))) if axis == 0 else add(b, scalar(s, F(3, 2)))
    if scalar(delta, F(sign))[1] < F(1, 2):
        return 'marker-outside'
    return None


def make_tree(kind, axis, sign):
    stats = {'nodes': 0, 'leaves': 0, 'max_depth': 0}
    def visit(box, depth):
        stats['nodes'] += 1
        stats['max_depth'] = max(stats['max_depth'], depth)
        why = exclusion(box, kind, axis, sign)
        if why:
            stats['leaves'] += 1
            return {'excluded': why}
        if depth >= 60:
            raise RuntimeError(('unresolved', kind, axis, sign, box))
        # Equalize normalized widths of the initial three parameter intervals.
        scales = [F(7, 2), F(7, 2), F(5, 12)]
        k = max(range(3), key=lambda k: (box[k][1]-box[k][0])/scales[k])
        lo, hi = box[k]
        mid = (lo+hi)/2
        left = list(box); left[k] = (lo, mid)
        right = list(box); right[k] = (mid, hi)
        return {'split': k, 'left': visit(left, depth+1), 'right': visit(right, depth+1)}
    initial = [(F(-7, 4), F(7, 4)), (F(-7, 4), F(7, 4)), (F(0), F(5, 12))]
    tree = visit(initial, 0)
    return {'kind': kind, 'axis': axis, 'sign': sign, 'stats': stats, 'tree': tree}


def main():
    if not __debug__:
        raise RuntimeError('Assertions must remain enabled')
    branches = []
    for kind in ('own', 'core'):
        for axis in (0, 1):
            for sign in (-1, 1):
                cert = make_tree(kind, axis, sign)
                branches.append(cert)
                print('CLOSED', kind, axis, sign, cert['stats'], flush=True)
    out = {'schema': 'centered-block-marker-v1', 'q': str(U), 'branches': branches}
    path = Path(__file__).with_name('BLOCK_MARKER_COVER.json')
    path.write_text(json.dumps(out, sort_keys=True, separators=(',', ':'))+'\n')
    print(path)


if __name__ == '__main__':
    main()
