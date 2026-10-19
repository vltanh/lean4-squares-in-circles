#!/usr/bin/env python3
"""Extract a compact, exact record from the completed fixed middle replay.

This only reads supplied coefficient lower bounds; it derives no new
polynomial and is not a substitute for the frozen kernel.  Exclusive
creation prevents alteration of an already-published compact record.
"""
from fractions import Fraction as F
from hashlib import sha256
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
DATA = HERE/'MISMATCH_026_TO_01_AFFINE_HAND_DATA.json'
KERNEL = HERE/'verify_mismatch_026_to_01_affine_hand.js'
FULL = HERE/'MISMATCH_026_TO_01_AFFINE_HAND_ARITHMETIC.json'
OUT = HERE/'MISMATCH_026_TO_01_AFFINE_HAND_COMPACT_REPORT.json'
expected = {
    DATA: '3230d71cdb3f1aa513aa74de04dc49429bb6ff2759a115cd55d98b160e1fedf4',
    KERNEL: '6af3d41fe7d404da7dd286c46644160f5444edd3028d864701266e9a4cd18697',
    FULL: '13a7dc18a78aaa4bbdeef9dc0d83b8f0098ba6c0e6e68ba55401d41849ef0f24',
}


def digest(p):
    return sha256(p.read_bytes()).hexdigest()


assert all(digest(p) == h for p, h in expected.items())
d, a = json.loads(DATA.read_text()), json.loads(FULL.read_text())
assert a['status'] == a['cover']['status'] == 'PASS'
assert not a['failures'] and not a['cover']['errors']
assert a['rows'] == a['passed'] == len(a['results']) == len(d['rows']) == 131255
assert len(d['arcs']) == 401
assert a['cover']['angle_chains'] == len(a['cover']['chains']) == 123168
records = []
polynomials = coefficients = 0
least = None
for index, result in enumerate(a['results']):
    assert result['index'] == index and result['cost']
    row = []
    for kind in ('premises', 'cost'):
        group = []
        for p in result[kind]:
            values = list(map(F, p['coefficient_lower']))
            assert len(values) == p['degree']+1
            lower = min(values)
            assert lower == F(p['reserve'])
            assert lower > 0 if kind == 'cost' else lower >= 0
            group.append([p['degree'], str(lower)])
            polynomials += 1
            coefficients += len(values)
            if kind == 'cost':
                least = lower if least is None else min(least, lower)
        row.append(group)
    records.append(row)
assert polynomials == 354398 and coefficients == 2903573
assert least == F(76173, 20000000000000)
assert sum(map(F, d['gamma']), F(0)) == F(3141537, 500000)
compact = {
    'status': 'PASS',
    'scope': a['scope'],
    'hypotheses': a['hypotheses'],
    'rows': a['rows'],
    'passed': a['passed'],
    'failures': [],
    'cover': {'status': 'PASS', 'angle_chains': a['cover']['angle_chains']},
    'arcs': len(d['arcs']),
    'polynomials': polynomials,
    'coefficients': coefficients,
    'minimum_cost_coefficient': str(least),
    'gamma_sum': '3141537/500000',
    'sha256': {p.name: h for p, h in expected.items()},
    'row_records': records,
}
assert all(digest(p) == h for p, h in expected.items())
if OUT.exists():
    assert json.loads(OUT.read_text()) == compact
    print('Existing compact record is mathematically identical; no file changed.')
else:
    with OUT.open('x') as f:
        json.dump(compact, f, indent=2)
        f.write('\n')
    print('Created '+OUT.name)
print(json.dumps({
    'status': 'PASS_EXACT_COMPACT_EXTRACTION',
    'polynomials': polynomials,
    'coefficients': coefficients,
    'least_strict_cost_coefficient': str(least),
    'compact_sha256': digest(OUT),
}, indent=2))
