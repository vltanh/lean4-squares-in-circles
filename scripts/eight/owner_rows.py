#!/usr/bin/env python3
"""Convert the owner and tilt rows of eight squares into natural-number data files.

The script reads the rows from the Lean structure literals of
`SquaresInCircles/Eight/Generated/Owner/*.lean` at commit 65e4060 (option `--commit`) and
writes one file per table to `data/eight/owner/`, one row per line of 55 natural numbers,
read by `Line.ofNats` (`Candidate/DualCheck.lean`):

    positive a⁺ a⁻ b⁺ b⁻ d lambda[7] cone[35] mu[7]

The interval of the row is `[a / d, b / d]` with `a = a⁺ - a⁻`, `b = b⁺ - b⁻` and `d`
the least common denominator, and every multiplier is written in units of `10⁻⁸`
(all of them are integer multiples of `10⁻⁸`). The mode and the owners are those of
the table; the alternative is `.zero` in an owner table, and the row of a tilt bundle
with number `k` is the row of `Alternative.ofIndex k`.

The quartic, its Bernstein coefficients and the reserve are not stored: Lean computes
them. As a check of the data the script

* prints every stored row back in the source syntax and compares it with the source,
  together with the mode, owners and alternative given by its table;
* recomputes the quartic and its Bernstein coefficients exactly, with the formulas of
  `Row.quartic`, and compares them with the source literals, and the source reserve
  with their minimum;
* repeats the natural-number computation of `Line.quarticN` and `bernsteinN` and checks
  that it gives `M` times the quartic and `12 d⁴ M` times the Bernstein coefficients,
  all of them positive.

    python3 -I scripts/eight/owner_rows.py [--commit 65e4060] [--lean]

With `--lean` it also writes the two Lean modules of the tables: the owner tables of the
mixed mode, and the tilt bundles.
"""
from fractions import Fraction as Q
from pathlib import Path
import argparse
import hashlib
import json
import math
import re
import subprocess
import sys
import textwrap

ROOT = Path(__file__).resolve().parents[2]
SOURCE = 'SquaresInCircles/Eight/Generated/Owner'
DATA = ROOT / 'data/eight/owner'
LEAN = ROOT / SOURCE
MODES = ['quarter', 'mixed', 'tilt']

# --- exact mirror of `Row.quartic` (Candidate/Dual.lean) -----------------

ZERO, OTHER, MIXED = {0, 2, 4}, {3, 5}, {1, 6}
G, T, E = 1, 4, 6
SIGNS = [1, -1, 1, -1, 1, -1, -1]
ALIGNED = [0, 2, 3, 4, 5]
LOWER_RATIO = [Q(1, 2), Q(1, 20), Q(0), Q(0), Q(1, 20), Q(1, 2), Q(0)]
UPPER_RATIO = [Q(1), Q(4, 5), Q(1), Q(1), Q(4, 5), Q(1), Q(1)]
D, C, S = [Q(1), Q(0), Q(1)], [Q(1), Q(0), Q(-1)], [Q(0), Q(2)]


def add(*ps):
    r = [Q(0)] * max([len(p) for p in ps] + [0])
    for p in ps:
        for i, x in enumerate(p):
            r[i] += x
    return r


def scale(c, p):
    return [c * x for x in p]


def mul(p, q):
    if not p or not q:
        return []
    r = [Q(0)] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            r[i + j] += x * y
    return r


def nxt(i):
    return (i + 1) % 7


def sin_num(i):
    return [] if i in ZERO else D if i in OTHER else C


def cos_num(i):
    return D if i in ZERO else [] if i in OTHER else S if i == G else scale(-1, S)


def coef(j, r, p):
    return p if j == r else []


def nominal_a(i, o, r):
    return [coef(nxt(i), r, sin_num(i)),
            add(scale(-1, coef(i, r, cos_num(i))), coef(nxt(i), r, D)),
            coef(i, r, sin_num(i)),
            add(coef(i, r, D), scale(-1, coef(nxt(i), r, cos_num(i))))][o]


def nominal_b(i, o, r):
    si, sj = SIGNS[i], SIGNS[nxt(i)]
    return [add(coef(i, r, scale(si, D)), scale(-1, coef(nxt(i), r, scale(sj, cos_num(i))))),
            coef(i, r, scale(si, sin_num(i))),
            add(coef(i, r, scale(si, cos_num(i))), scale(-1, coef(nxt(i), r, scale(sj, D)))),
            scale(-1, coef(nxt(i), r, scale(sj, sin_num(i))))][o]


def derivative_a(i, o, r):
    return [coef(nxt(i), r, cos_num(i)), coef(i, r, sin_num(i)),
            coef(i, r, cos_num(i)), coef(nxt(i), r, sin_num(i))][o]


def derivative_b(i, o, r):
    si, sj = SIGNS[i], SIGNS[nxt(i)]
    return [coef(nxt(i), r, scale(sj, sin_num(i))), coef(i, r, scale(si, cos_num(i))),
            scale(-1, coef(i, r, scale(si, sin_num(i)))),
            scale(-1, coef(nxt(i), r, scale(sj, cos_num(i))))][o]


def sign_value(positive):
    return Q(1) if positive else Q(-1)


def width_numerator(positive):
    return scale(Q(1, 2), add(D, C, scale(sign_value(positive), S)))


def last_width_derivative(positive):
    return scale(Q(1, 2), add(C, scale(-1, S))) if positive else scale(Q(-1, 2), add(C, S))


def edge_width(positive, i):
    return width_numerator(positive) if i in MIXED else D


def alternative_owner(j, second):
    if second:
        return 3 if j in (2, 4) else 2
    return 2 if j in (2, 4) else 0


def primary(i):
    return (Q(7, 12), Q(349, 250)) if i in (G, T) else (Q(447, 800), Q(283, 200))


def quartic(row):
    mode, positive = row['mode'], row['positive']
    lam, cone, mu, alt = row['lambda'], row['cone'], row['mu'], row['alternative']
    owners = row['owners']
    assert mode in (1, 2), 'only the mixed and tilt modes are used'
    q = Q(1957767069, 500000000) if mode == 2 else Q(9789, 2500)
    eps = Q(1, 1000)
    max_lambda = max(lam[i] for i in ALIGNED)
    if mode == 1:
        loss = eps * (Q(1001, 1000) * max_lambda + 2 * lam[E])
    else:
        loss = eps ** 2 * (Q(1001, 1000) * max_lambda + Q(9, 8) * lam[E])

    def error(derivative, i):
        if alt is None:
            return []
        j, second, pos = alt
        e = ALIGNED[j]
        return scale(sign_value(pos) * eps,
                     add(scale(lam[e], derivative(e, alternative_owner(j, second), i)),
                         scale(-lam[E], derivative(E, 1, i))))

    def cone_sum(f):
        return sum(cone[5 * k + m] * f(k, m) for k in range(7) for m in range(5))

    def cone_a(j):
        return cone_sum(lambda k, m: ([1, -1, -LOWER_RATIO[j], UPPER_RATIO[j], 0][m]
                                      if k == j else 0))

    def cone_b(j):
        return cone_sum(lambda k, m: [0, 0, 1, -1, -1][m] if k == j else 0)

    fa = [add(*[scale(lam[i], nominal_a(i, owners[i], j)) for i in range(7)],
              scale(cone_a(j), D), error(derivative_a, j)) for j in range(7)]
    fb = [add(*[scale(lam[i], nominal_b(i, owners[i], j)) for i in range(7)],
              scale(cone_b(j), D), error(derivative_b, j)) for j in range(7)]
    rhs_cone = cone_sum(lambda k, m: [primary(k)[0], -primary(k)[1], 0, 0, Q(-9, 10)][m])
    if alt is None:
        error_rhs = []
    else:
        j, _, pos = alt
        error_rhs = add(scale(-(sign_value(pos) * eps * lam[E]), last_width_derivative(positive)),
                        scale(eps * lam[ALIGNED[j]] / 2, D))
    rhs = add(*[scale(lam[i], edge_width(positive, i)) for i in range(7)],
              scale(rhs_cone - loss, D), error_rhs)
    L = add(rhs, scale(Q(1, 2), add(*[add(fa[i], fb[i]) for i in range(7)])))
    p = add(mul(D, L), scale(-(q * sum(mu)), mul(D, D)),
            *[scale(-1 / (4 * mu[i]), add(mul(fa[i], fa[i]), mul(fb[i], fb[i])))
              for i in range(7)])
    return p + [Q(0)] * (5 - len(p))


def bernstein(p, lo, hi):
    """Bernstein coefficients of degree 4 of `t ↦ p (lo + (hi - lo) t)` on [0, 1]."""
    w = hi - lo
    a = [p[0] + lo * (p[1] + lo * (p[2] + lo * (p[3] + lo * p[4]))),
         p[1] + lo * (2 * p[2] + lo * (3 * p[3] + lo * 4 * p[4])),
         p[2] + lo * (3 * p[3] + lo * 6 * p[4]),
         p[3] + lo * 4 * p[4],
         p[4]]
    c = [a[k] * w ** k for k in range(5)]
    return [c[0], c[0] + c[1] / 4, c[0] + c[1] / 2 + c[2] / 6,
            c[0] + 3 * c[1] / 4 + c[2] / 2 + c[3] / 4, c[0] + c[1] + c[2] + c[3] + c[4]]


# --- parsing the source rows ---------------------------------------------

RAT = r'\(?(-?\d+)(?:/(\d+))?\)?'


def rat(s):
    m = re.fullmatch(RAT, s.strip())
    if not m:
        raise ValueError(f'not a rational literal: {s!r}')
    return Q(int(m.group(1)), int(m.group(2) or 1))


def show(x):
    x = Q(x)
    return str(x.numerator) if x.denominator == 1 else f'({x.numerator}/{x.denominator})'


def vec(xs):
    return '![' + ', '.join(map(show, xs)) + ']'


def lst(xs):
    return '[' + ', '.join(map(show, xs)) + ']'


def items(s):
    return [x for x in re.split(r',\s*', s.strip()) if x]


ROW = re.compile(
    r'def (\w+) : Row :=\n'
    r'  \{ mode := \.(\w+)\n'
    r'    positive := (true|false)\n'
    r'    interval := ⟨([^,]+), ([^⟩]+)⟩\n'
    r'    owners := !\[([^\]]*)\]\n'
    r'    lambda := !\[([^\]]*)\]\n'
    r'    cone := fun i => \(!\[(.*)\] i\.1\) i\.2\n'
    r'    mu := !\[([^\]]*)\]\n'
    r'    alternative := (\.zero|\(\.spike (\d) (true|false) (true|false)\))\n'
    r'    polynomial := \[([^\]]*)\]\n'
    r'    bernstein := \[([^\]]*)\]\n'
    r'    reserve := (\S+) \}\n')


def parse_row(m):
    cone_text = m.group(8)
    cone_rows = re.findall(r'!\[([^\]]*)\]', cone_text)
    if len(cone_rows) != 7:
        raise ValueError(f'{m.group(1)}: cone has {len(cone_rows)} rows')
    cone = [rat(x) for r in cone_rows for x in items(r)]
    alt = None if m.group(10) == '.zero' else (
        int(m.group(11)), m.group(12) == 'true', m.group(13) == 'true')
    row = {
        'name': m.group(1), 'mode': MODES.index(m.group(2)),
        'positive': m.group(3) == 'true',
        'lo': rat(m.group(4)), 'hi': rat(m.group(5)),
        'owners': [int(x) for x in items(m.group(6))],
        'lambda': [rat(x) for x in items(m.group(7))], 'cone': cone,
        'mu': [rat(x) for x in items(m.group(9))], 'alternative': alt,
        'polynomial': [rat(x) for x in items(m.group(14))],
        'bernstein': [rat(x) for x in items(m.group(15))],
        'reserve': rat(m.group(16)), 'text': m.group(0)}
    sizes = [len(row['owners']), len(row['lambda']), len(row['cone']), len(row['mu'])]
    if sizes != [7, 7, 35, 7]:
        raise ValueError(f'{row["name"]}: field sizes {sizes}')
    return row


def alternative_index(alt):
    if alt is None:
        return 0
    j, second, positive = alt
    return 1 + 4 * j + 2 * second + positive


def alternative_text(alt):
    if alt is None:
        return '.zero'
    j, second, positive = alt
    return f'(.spike {j} {str(second).lower()} {str(positive).lower()})'


SIGMA = 10 ** 8


def interval_ints(lo, hi):
    d = lo.denominator * hi.denominator // math.gcd(lo.denominator, hi.denominator)
    return int(lo * d), int(hi * d), d


def units(x):
    n = x * SIGMA
    if n.denominator != 1 or n < 0:
        raise ValueError(f'not a nonnegative multiple of 10^-8: {x}')
    return int(n)


def encode(row):
    a, b, d = interval_ints(row['lo'], row['hi'])
    return ([int(row['positive']), max(a, 0), max(-a, 0), max(b, 0), max(-b, 0), d] +
            [units(x) for x in row['lambda'] + row['cone'] + row['mu']])


def decode(ints):
    """The fields of `Line.row`, as `Line.ofNats` reads a line."""
    assert len(ints) == 55 and min(ints) >= 0, ints
    a, b, d = ints[1] - ints[2], ints[3] - ints[4], ints[5]
    return {'positive': ints[0] == 1, 'lo': Q(a, d), 'hi': Q(b, d),
            'lambda': [Q(n, SIGMA) for n in ints[6:13]],
            'cone': [Q(n, SIGMA) for n in ints[13:48]],
            'mu': [Q(n, SIGMA) for n in ints[48:55]]}


def reprint(name, row, polynomial, coefficients, reserve):
    """The source syntax of a row, from its fields and the given derived ones."""
    cones = '![' + ', '.join(vec(row['cone'][5 * i:5 * i + 5]) for i in range(7)) + ']'
    return (f'def {name} : Row :=\n'
            f'  {{ mode := .{MODES[row["mode"]]}\n'
            f'    positive := {str(row["positive"]).lower()}\n'
            f'    interval := ⟨{show(row["lo"])}, {show(row["hi"])}⟩\n'
            f'    owners := {vec(row["owners"])}\n'
            f'    lambda := {vec(row["lambda"])}\n'
            f'    cone := fun i => ({cones} i.1) i.2\n'
            f'    mu := {vec(row["mu"])}\n'
            f'    alternative := {alternative_text(row["alternative"])}\n'
            f'    polynomial := {lst(polynomial)}\n'
            f'    bernstein := {lst(coefficients)}\n'
            f'    reserve := {show(reserve)} }}\n')


# --- the natural-number computation of `Line.quarticN` and `bernsteinN` -----

D_INT, C_INT, S_INT = [1, 0, 1], [1, 0, -1], [0, 2]


def to_int(p):
    assert all(x.denominator == 1 for x in p), p
    return [int(x) for x in p]


def quartic_n(row, ints):
    """`Line.quarticN`, with integers in place of differences of natural numbers."""
    mode, owners, alt, positive = row['mode'], row['owners'], row['alternative'], ints[0] == 1
    lam, K, U = ints[6:13], ints[13:48], ints[48:55]
    eps = 20
    half = 12000000
    QN = 1879456386240000000 if mode == 2 else 1879488000000000000
    lower = [10000, 1000, 0, 0, 1000, 10000, 0]
    upper = [20000, 16000, 20000, 20000, 16000, 20000, 20000]
    lp = [14000000000 if i in (G, T) else 13410000000 for i in range(7)]
    up = [33504000000 if i in (G, T) else 33960000000 for i in range(7)]

    def error(derivative, i):
        if alt is None:
            return []
        j, second, pos = alt
        e = ALIGNED[j]
        t = add(scale(eps * lam[e], to_int(derivative(e, alternative_owner(j, second), i))),
                scale(-eps * lam[E], to_int(derivative(E, 1, i))))
        return t if pos else scale(-1, t)

    fa = [add(*[scale(20000 * lam[i], to_int(nominal_a(i, owners[i], j))) for i in range(7)],
              scale(20000 * K[5*j] + upper[j] * K[5*j+3] - 20000 * K[5*j+1] - lower[j] * K[5*j+2],
                    D_INT), error(derivative_a, j)) for j in range(7)]
    fb = [add(*[scale(20000 * lam[i], to_int(nominal_b(i, owners[i], j))) for i in range(7)],
              scale(20000 * K[5*j+2] - 20000 * K[5*j+3] - 20000 * K[5*j+4], D_INT),
              error(derivative_b, j)) for j in range(7)]
    cone_rhs = sum(lp[i] * K[5*i] - up[i] * K[5*i+1] - 21600000000 * K[5*i+4] for i in range(7))
    max_lambda = max(lam[i] for i in ALIGNED)
    loss = (24024000 * max_lambda + 48000000 * lam[E] if mode == 1 else
            24024 * max_lambda + 27000 * lam[E])
    width = add(D_INT, C_INT, S_INT if positive else scale(-1, S_INT))
    rhs = add(*[scale(12000000000 * lam[i], width) if i in MIXED else
                scale(24000000000 * lam[i], D_INT) for i in range(7)],
              scale(cone_rhs - loss, D_INT))
    if alt is not None:
        j, _, pos = alt
        last = add(C_INT, scale(-1, S_INT)) if positive else scale(-1, add(C_INT, S_INT))
        w = scale(lam[E], last)
        rhs = add(rhs, scale(half, add(scale(lam[ALIGNED[j]], D_INT), scale(-1, w) if pos else w)))
    ell = add(rhs, scale(600000, add(*[add(fa[i], fb[i]) for i in range(7)])))
    prod = math.prod(U)
    p = add(scale(20000000 * prod, mul(D_INT, ell)), scale(-QN * sum(U) * prod, mul(D_INT, D_INT)),
            *[scale(-300000000 * (prod // U[i]), add(mul(fa[i], fa[i]), mul(fb[i], fb[i])))
              for i in range(7)])
    return to_int(p) + [0] * (5 - len(p)), 48 * 10 ** 24 * prod


def bernstein_n(p, a, b, d):
    """`bernsteinN`: `12 d⁴` times the Bernstein coefficients of `p` on `[a / d, b / d]`."""
    e = b - a
    c0 = p[0]*d**4 + a*(p[1]*d**3 + a*(p[2]*d**2 + a*(p[3]*d + a*p[4])))
    c1 = e*(p[1]*d**3 + a*(2*p[2]*d**2 + a*(3*p[3]*d + a*4*p[4])))
    c2 = e*e*(p[2]*d**2 + a*(3*p[3]*d + a*6*p[4]))
    c3 = e*e*e*(p[3]*d + a*4*p[4])
    c4 = e*e*e*e*p[4]
    return [12*c0, 12*c0 + 3*c1, 12*c0 + 6*c1 + 2*c2, 12*c0 + 9*c1 + 6*c2 + 3*c3,
            12*(c0 + c1 + c2 + c3 + c4)]


TABLE = re.compile(r'def (\w+) : OwnerTable where\n  mode := \.(\w+)\n  owners := !\[([^\]]*)\]\n'
                   r'  rows := \[([^\]]*)\]\n')
BUNDLE = re.compile(r'def (\w+) : TiltBundle where\n  interval := ⟨([^,]+), ([^⟩]+)⟩\n'
                    r'  lambda := !\[([^\]]*)\]\n  row := (\w+)\n')
SELECT = re.compile(r'  \| (\.zero|\(\.spike \d (?:true|false) (?:true|false)\)) => (\w+)\n')


def source_text(commit, module):
    return subprocess.run(['git', '-C', str(ROOT), 'show', f'{commit}:{SOURCE}/{module}.lean'],
                          check=True, capture_output=True, text=True).stdout


def modules(commit):
    out = subprocess.run(['git', '-C', str(ROOT), 'ls-tree', '--name-only', f'{commit}:{SOURCE}'],
                         check=True, capture_output=True, text=True).stdout.split()
    return sorted(n[:-5] for n in out if n.endswith('.lean'))


def convert(commit):
    tables = []
    for module in modules(commit):
        text = source_text(commit, module)
        rows = [parse_row(m) for m in ROW.finditer(text)]
        if len(rows) != text.count(': Row :='):
            raise ValueError(f'{module}: parsed {len(rows)} of {text.count(": Row :=")} rows')
        names = [r['name'] for r in rows]
        info = {'module': module, 'rows': rows}
        if module.startswith('Tilt'):
            b = BUNDLE.search(text)
            selector = dict((n, a) for a, n in SELECT.findall(text))
            if [selector[n] for n in names] != [alternative_text(r['alternative']) for r in rows]:
                raise ValueError(f'{module}: selector differs from the row alternatives')
            if [alternative_index(r['alternative']) for r in rows] != list(range(21)):
                raise ValueError(f'{module}: rows are not in alternative order')
            info.update(kind='bundle', name=b.group(1), lo=rat(b.group(2)), hi=rat(b.group(3)),
                        lam=[rat(x) for x in items(b.group(4))],
                        interval_text=(b.group(2), b.group(3)), lambda_text=b.group(4))
        else:
            t = TABLE.search(text)
            if items(t.group(4)) != names:
                raise ValueError(f'{module}: table rows differ from the module rows')
            info.update(kind='table', name=t.group(1), mode=t.group(2),
                        owners=[int(x) for x in items(t.group(3))], owners_text=t.group(3))
        tables.append(info)
    return tables


def needed(info):
    """Whether the proof uses the table. The nonpositive half-angles are excluded geometrically
    (`negative_tilt_excluded`), and so are all quarter patterns (`quarter_owners`) and the mixed
    patterns with the `E` axis `2` or `3` (`mixed_E_owners`)."""
    if info['kind'] == 'bundle':
        return info['hi'] > 0
    return info['mode'] == 'mixed' and info['owners'][6] < 2


def check(tables):
    """Exactness of the data files and agreement of the derived fields."""
    count, bits = 0, 0
    for info in tables:
        first = encode(info['rows'][0])
        if info['kind'] == 'bundle':
            head = decode(first)
            if (head['lo'], head['hi'], head['lambda']) != (info['lo'], info['hi'], info['lam']):
                raise ValueError(f'{info["name"]}: interval or weights differ from the first row')
        for k, row in enumerate(info['rows']):
            ints = encode(row)
            back = decode([int(x) for x in ' '.join(map(str, ints)).split()])
            if info['kind'] == 'table':
                back.update(mode=MODES.index(info['mode']), owners=info['owners'], alternative=None)
            else:
                if ints[:13] != first[:13]:
                    raise ValueError(f'{row["name"]}: sign, interval or weights differ '
                                     'in the bundle')
                j = k - 1
                back.update(mode=2, owners=[0, 0, 0, 2, 0, 2, 1], alternative=None if k == 0 else
                            (j // 4, bool(j // 2 % 2), bool(j % 2)))
            p = quartic(back)
            b = bernstein(p, back['lo'], back['hi'])
            if p != row['polynomial']:
                raise ValueError(f'{row["name"]}: quartic differs from the source')
            if b != row['bernstein']:
                raise ValueError(f'{row["name"]}: Bernstein coefficients differ from the source')
            if not (0 < row['reserve'] <= min(b)):
                raise ValueError(f'{row["name"]}: source reserve is not below the coefficients')
            if reprint(row['name'], back, p, b, row['reserve']) != row['text']:
                raise ValueError(f'{row["name"]}: printed row differs from the source text')
            pn, M = quartic_n(back, ints)
            if [Q(x) for x in pn] != [M * x for x in p]:
                raise ValueError(f'{row["name"]}: natural-number quartic differs')
            a, bb, d = ints[1] - ints[2], ints[3] - ints[4], ints[5]
            bn = bernstein_n(pn, a, bb, d)
            if [Q(x) for x in bn] != [12 * d ** 4 * M * x for x in b] or min(bn) <= 0:
                raise ValueError(f'{row["name"]}: natural-number Bernstein coefficients differ')
            bits = max(bits, max(abs(x).bit_length() for x in bn))
            count += 1
    return count, bits


def write_data(tables):
    DATA.mkdir(parents=True, exist_ok=True)
    total = 0
    for info in tables:
        text = ''.join(' '.join(map(str, encode(r))) + '\n' for r in info['rows'])
        path = DATA / (info['module'].lower() + '.txt')
        path.write_text(text)
        total += len(text.encode())
    return total


HEADER = '''module

public import SquaresInCircles.Eight.Candidate.DualCheck
meta import SquaresInCircles.Eight.IntRows

'''

OPEN = '''@[expose] public section
noncomputable section
open SquaresInCircles.Eight.Candidate
open SquaresInCircles.Eight.Candidate.Dual
namespace SquaresInCircles.Eight.Generated.Owner

'''


def wrap(text):
    return '\n'.join(textwrap.wrap(text, 100, break_on_hyphens=False, break_long_words=False))


def lines_def(info, what):
    """The definition reading the rows of a table or bundle from its data file, read once."""
    stem = info['module'][0].lower() + info['module'][1:]
    return stem, f'''set_option maxRecDepth 100000 in
/-- The rows of `{info['name']}`{what}. -/
noncomputable def {stem}Lines : List Line :=
  nat_rows% "../../../../data/eight/owner/{info['module'].lower()}.txt" ↦ Line.ofNats

'''


def lean_tables(tables):
    """The module of the owner tables."""
    out = HEADER + '/-!\n# Eight squares: the owner tables\n\n' + wrap(
        f'The {len(tables)} owner tables of the mixed mode, with '
        f'{sum(len(i["rows"]) for i in tables)} rows, read from `data/eight/owner/mixed*.txt`, one '
        f'file per table. For each table the kernel evaluates that every row passes `Line.check` '
        f'and that the intervals cover the half-angle chart (`coverCheck`).') + '\n-/\n\n' + OPEN
    for info in tables:
        stem, text = lines_def(info, '')
        mode, owners = info['mode'], f'![{info["owners_text"]}]'
        test = f'Line.check .{mode} {owners} .zero'
        out += text + f'''theorem {stem}_rows :
    {stem}Lines.all ({test}) = true := by
  decide +kernel

theorem {stem}_cover : coverCheck {stem}Lines = true := by decide +kernel

def {info['name']} : OwnerTable :=
  .ofLines .{mode} {owners} {stem}Lines {stem}_rows {stem}_cover

'''
    return out + 'end SquaresInCircles.Eight.Generated.Owner\n'


def lean_bundles(tables):
    """The module of the tilt bundles of the two tails of the positive half-angle chart."""
    split = Q(1001, 20000)
    left = [info for info in tables if info['hi'] <= split]
    right = [info for info in tables if info['lo'] > split]
    if len(left) + len(right) != len(tables):
        raise ValueError('a tilt bundle meets the window (1001/20000, 2/25)')
    rows = sum(len(info['rows']) for info in tables)
    out = HEADER + '/-!\n# Eight squares: the tilt bundles\n\n' + wrap(
        f'The tilt bundles of the two tails `[0, 1001/20000]` and `[2/25, 3/8]` of the positive '
        f'half-angle chart, {len(left)} and {len(right)} of them, with {rows} rows, read from '
        f'`data/eight/owner/tilt*.txt`, one file per bundle with one row for each error '
        f'alternative. For each bundle the kernel evaluates `bundleCheck`: every row passes '
        f'`Line.check`.') + '\n-/\n\n' + OPEN
    for info in left + right:
        a, b = show(info['lo']).strip('()'), show(info['hi']).strip('()')
        stem, text = lines_def(info, f' on `[{a}, {b}]`, in the order of `Alternative.index`')
        out += text + f'''theorem {stem}_check : bundleCheck {stem}Lines = true := by decide +kernel

def {info['name']} : TiltBundle := .ofLines {stem}Lines {stem}_check

'''
    return out + 'end SquaresInCircles.Eight.Generated.Owner\n'


def lean_modules(tables):
    """The two modules of the tables, by file name."""
    return {'Tables': lean_tables([i for i in tables if i['kind'] == 'table']),
            'Bundles': lean_bundles([i for i in tables if i['kind'] == 'bundle'])}


def write_index(commit, tables):
    """The provenance of the data files and their hashes: Lake does not track them."""
    old = json.loads(subprocess.run(
        ['git', '-C', str(ROOT), 'show', f'{commit}:{SOURCE}/generation_index.json'],
        check=True, capture_output=True, text=True).stdout)
    data = []
    for info in tables:
        path = DATA / (info['module'].lower() + '.txt')
        data.append({'file': str(path.relative_to(ROOT)), 'table': info['name'],
                     'rows': len(info['rows']),
                     'sha256': hashlib.sha256(path.read_bytes()).hexdigest()})
    index = {'schema': 'eight-owner-lines-v1',
             'source': f'the rows of {SOURCE} at commit {commit}, converted by '
                       'scripts/eight/owner_rows.py',
             'inputs': old['inputs'], 'data': data}
    (LEAN / 'generation_index.json').write_text(json.dumps(index, indent=2) + '\n')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--commit', default='65e4060')
    ap.add_argument('--lean', action='store_true')
    args = ap.parse_args()
    tables = [info for info in convert(args.commit) if needed(info)]
    count, bits = check(tables)
    size = write_data(tables)
    if args.lean:
        modules = lean_modules(tables)
        if sum(m.count('Lines : List Line') for m in modules.values()) != len(tables):
            raise ValueError('a table is in no module')
        for name, text in modules.items():
            (LEAN / (name + '.lean')).write_text(text)
        write_index(args.commit, tables)
    print(f'{len(tables)} tables, {count} rows checked, {size} bytes of data, '
          f'Bernstein numbers below 2^{bits}')


if __name__ == '__main__':
    sys.exit(main())
