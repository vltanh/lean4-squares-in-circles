"""Fixed rational comparisons and interface binding for the ceiling transfer.

The continuous proof is independently reviewed in the companion audit.
This script checks only its printed rational constants, the radius order,
the common frame clusters and all zero-error allowed-normal identities.
The already proved stationary-root bracket is an explicit input lemma.
"""
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
DEPENDENCIES = [
    'HAND_FIXED_CEILING_TRANSFER_WITH_AUTOMATIC_TERMINAL.md',
    'HUMAN_SHARP_CEILING_BRACKET.md',
    'HUMAN_BROAD_TERMINAL_ARITHMETIC.md',
    'CYCLIC_RADIAL_BOUNDARY_REDUCTION.md',
    'HAND_CANDIDATE_CAPTURE_AT_ONE_THOUSANDTH.md',
    'HAND_TERMINAL_WITH_AUTOMATIC_SLIDERS.md',
    'EQUALITY_PULLBACK_TO_ORIGINAL_SQUARES.md',
    'COMPLETE_EQUALITY_PARAMETER_DOMAIN.md',
]


def locate(name):
    candidates = [HERE/name, ROOT/'proof_reference'/name]
    return next(p for p in candidates if p.is_file())


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


checks = []


def check(label, lhs, relation, rhs):
    lhs, rhs = F(lhs), F(rhs)
    assert {'>': lhs > rhs, '<': lhs < rhs, '=': lhs == rhs}[relation], label
    checks.append({'label': label, 'left': str(lhs), 'relation': relation,
                   'right': str(rhs), 'difference': str(lhs-rhs)})


def rotate_quarters(v, k):
    x, y = v
    for _ in range(k % 4):
        x, y = -y, x
    return x, y


def main():
    inputs = {name: locate(name) for name in DEPENDENCIES}
    before = {name: digest(path) for name, path in inputs.items()}
    assert before[DEPENDENCIES[0]] == '09c574dbcad7353057ef247341424e2f6bc158c2ed1329bd7a125223ab062265'
    q_floor, q_ceiling, q_coarse = F(7831, 2000), F(1957767069, 500000000), F(9789, 2500)
    q_test = F('3.91553413751747532652')
    bracket_low, bracket_high = q_test-F(2, 10**16), q_test+F(1, 10**16)
    check('working floor exceeds monotonicity floor', q_floor, '>', F(5, 2))
    check('certified lower bracket exceeds working floor', bracket_low, '>', q_floor)
    check('certified bracket width', bracket_high-bracket_low, '=', F(3, 10**16))
    check('fixed ceiling exceeds certified upper bracket', q_ceiling, '>', bracket_high)
    check('fixed ceiling below coarse hand ceiling', q_coarse, '>', q_ceiling)
    check('coarse ceiling below four', 4, '>', q_coarse)
    check('sqrt two less than three halves', F(3, 2)**2, '>', 2)
    check('outer lower-radius polynomial upper bound', F(4, 5)**2+F(3, 2)*F(4, 5)+F(1, 2), '=', F(117, 50))
    check('outer lower-radius bound holds at q=5/2', F(5, 2), '>', F(117, 50))
    check('outer upper-radius polynomial lower bound', F(3, 2)**2+F(3, 2)+F(1, 2), '=', F(17, 4))
    check('outer upper-radius bound holds at q=4', F(17, 4), '>', 4)
    check('derivative squared-denominator minimum', 1+4*F(5, 2)-2, '=', 9)
    check('derivative squared-denominator maximum', 2+4*4-2, '=', 16)
    check('sqrt two less than ten sevenths', F(10, 7)**2, '>', 2)
    check('rounded-square core radius below four fifths', F(4, 5)-(F(5, 7)+F(1, 12)), '=', F(1, 420))
    check('positive outer pair derivative bound', F(2, 3)/4, '=', F(1, 6))
    check('mixed-sign outer derivative coefficient', F(8, 15)/4-F(1, 3), '=', -F(1, 5))
    check('mixed-sign outer pair derivative floor', F(1, 6)-F(5, 8)/5, '=', F(1, 24))
    check('core outer positive projection reserve', 1-F(4, 5), '=', F(1, 5))
    check('core outer positive coefficient floor', F(1, 5)/F(3, 2), '=', F(2, 15))
    check('core outer derivative floor', F(2, 15)/4, '=', F(1, 30))
    check('boundary-reduction radius upper reserve', F(71, 50)**2+F(71, 50)+F(1, 2)-q_coarse, '=', F(13, 625))
    check('radial span below one', 1, '>', F(71, 50)-F(7, 12))
    check('boundary-reduction cosine corner bound', F(41, 50), '>', F(17443, 21300))
    check('cosine lower Taylor endpoint', 1-F(3, 5)**2/2, '=', F(41, 50))
    check('six other gaps exclude a pi gap', F(18, 5), '>', F(355, 113))
    check('automatic mismatch threshold', F(1, 500), '>', F(1, 1000))
    reserve = F(56793, 5000000)-F(93, 10)*F(1, 1000)
    check('automatic terminal angular reserve', reserve, '=', F(10293, 5000000))
    check('automatic terminal reserve positive', reserve, '>', 0)

    offsets = [-1, -1, 0, 0, 1, 1, 2]
    word = [offsets[i+1]-offsets[i] for i in range(6)]+[offsets[0]+4-offsets[6]]
    assert word == [0, 1, 0, 1, 0, 1, 1] and sum(word) == 4
    aligned = [0, 2, 3, 4, 5]
    owner_sets = [[1, 3], [1], [1, 3], [3, 4], [1, 3], [3, 4], [2]]
    assignments = list(product(*owner_sets))
    assert len(assignments) == 32
    # At zero error, normals 1/3 agree at zero quarter and normals 3/4
    # agree at one quarter.  These are vector identities before applying
    # the common actual source-frame rotation.
    identities = []
    for i in aligned:
        normals = []
        for owner in owner_sets[i]:
            normal = ((0, 1) if owner == 1 else
                      rotate_quarters((0, 1), word[i]) if owner == 3 else (-1, 0))
            normals.append(normal)
        assert normals[0] == normals[1]
        identities.append({'edge': i, 'owners': owner_sets[i], 'relative_normal': list(normals[0])})
    components = [{i} for i in range(7)]
    for i in aligned:
        j = (i+1) % 7
        united = next(s for s in components if i in s) | next(s for s in components if j in s)
        components = [s for s in components if not (s & united)]+[united]
    assert {frozenset(s) for s in components} == {frozenset([0, 1]), frozenset([2, 3, 4, 5, 6])}
    assert before == {name: digest(path) for name, path in inputs.items()}
    result = {
        'status': 'PASS_FIXED_CEILING_TRANSFER_ARITHMETIC_AND_INTERFACES',
        'scope': 'Continuous transfer independently reviewed; unrestricted conclusion remains conditional on complete fixed-ceiling hand capture at total mismatch at most1/1000.',
        'working_radius_floor': str(q_floor), 'fixed_radius_ceiling': str(q_ceiling),
        'external_certified_sharp_bracket': [str(bracket_low), str(bracket_high)],
        'rational_comparisons': len(checks), 'checks': checks,
        'word': word, 'quarter_offsets': offsets, 'owner_assignments': len(assignments),
        'zero_error_owner_normal_identities': identities,
        'zero_error_frame_clusters': [sorted(s) for s in sorted(components, key=min)],
        'sha256': before, 'checker_sha256': digest(Path(__file__)), 'unchanged_inputs': True,
    }
    (HERE/'fixed_ceiling_transfer_independent_audit.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('checks', 'sha256')}, indent=2))


if __name__ == '__main__':
    main()
