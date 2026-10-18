"""Bind the independently reviewed conditional capture package.

This is an interface and integrity check, not a replacement for the three
standalone polynomial proofs or their independent reconstructions. It
checks their exact inputs, review bindings, complete pattern/vertex unions,
and the radius/mismatch/owner/quarter-offset route into the sharp terminal.
No discovery program is imported or executed.
"""
from fractions import Fraction as R
from hashlib import sha256
from itertools import product
from pathlib import Path
import json

BASE = Path(__file__).resolve().parent
ROOT = BASE.parent
LOOKUP = (BASE, ROOT / 'global_attack' / 'hand_conversion',
          ROOT / 'm5_agent' / 'hand_conversion', ROOT / 'proof_reference')
OUTPUT = BASE / 'CANDIDATE_CAPTURE_AT_ONE_THOUSANDTH_HAND_MANIFEST.json'


def locate(name):
    found = [p / name for p in LOOKUP if (p / name).is_file()]
    assert found, ('missing required file', name)
    raw = found[0].read_bytes()
    assert all(p.read_bytes() == raw for p in found), ('conflicting copies', name)
    return found[0]


def digest(name):
    return sha256(locate(name).read_bytes()).hexdigest()


def load(name):
    return json.loads(locate(name).read_text())


STAGES = [
    dict(name='quarter_owners', Q='9789/2500', epsilon='3/200',
         manuscript='HAND_CANDIDATE_MIXED_OWNERS_AND_TILT.md',
         checker='verify_candidate_mixed_owner_and_tilt_duals.py',
         data='candidate_quarter_owner_large_mismatch_dual_data.json',
         arithmetic='candidate_quarter_owner_large_mismatch_dual_arithmetic.json',
         review='CANDIDATE_QUARTER_LARGE_MISMATCH_INDEPENDENT_AUDIT.md',
         independent_checker='audit_candidate_quarter_large_mismatch_independently.py',
         independent_arithmetic='candidate_quarter_owner_large_mismatch_independent_audit.json',
         quartics=1545, coefficients=7725, patterns=48,
         minimum='2539981/1000000000000'),
    dict(name='mixed_owners', Q='9789/2500', epsilon='1/1000',
         manuscript='HAND_CANDIDATE_MIXED_OWNERS_WITH_TOTAL_MISMATCH.md',
         checker='verify_candidate_shared_mismatch_owner_duals.py',
         data='candidate_mixed_owner_shared_mismatch_hand_data.json',
         arithmetic='candidate_mixed_owner_shared_mismatch_hand_arithmetic.json',
         review='HAND_CANDIDATE_SHARED_MISMATCH_OWNERS_INDEPENDENT_AUDIT.md',
         independent_checker='audit_candidate_shared_mismatch_owners_independently.py',
         independent_arithmetic='candidate_shared_mismatch_owners_independent_audit.json',
         quartics=729, coefficients=3645, patterns=15,
         minimum='231527/1000000000000'),
    dict(name='common_tilt', Q='1957767069/500000000', epsilon='1/1000',
         manuscript='HAND_CANDIDATE_TILT_FROM_SIGNED_ERROR_VERTICES.md',
         checker='verify_candidate_signed_error_tilt_duals.py',
         data='candidate_tilt_signed_error_hand_data.json',
         arithmetic='candidate_tilt_signed_error_hand_arithmetic.json',
         review='CANDIDATE_SIGNED_ERROR_TILT_INDEPENDENT_AUDIT.md',
         independent_checker='audit_candidate_signed_error_tilt_independently.py',
         independent_arithmetic='candidate_signed_error_tilt_independent_audit.json',
         quartics=1239, coefficients=6195, cells=59, vertices=21,
         minimum='40703/500000000000'),
]

FILE_FIELDS = ('manuscript', 'checker', 'data', 'arithmetic', 'review',
               'independent_checker', 'independent_arithmetic')


def closed_chain(intervals, left, right):
    end = R(left)
    for lo, hi in sorted(intervals):
        assert lo == end and lo < hi <= R(right)
        assert hi <= 0 or lo >= 0
        end = hi
    assert end == R(right)


def check_domain(data, stage):
    assert data['unresolved'] == []
    assert R(data['Q']) == R(stage['Q'])
    assert R(data['epsilon']) == R(stage['epsilon'])
    assert data['denominator'] == 10**8
    assert data['bernstein_denominator'] == 10**12
    if stage['name'] == 'quarter_owners':
        expected = {(1, g, 1, b, 1, d, h)
                    for g, b, d, h in product(range(1, 5), (1, 3),
                                               (1, 3), range(1, 5))
                    if (b, d) != (3, 3)}
    elif stage['name'] == 'mixed_owners':
        expected = {(1, g, 1, 3, 1, 3, h)
                    for g, h in product(range(1, 5), repeat=2)
                    if (g, h) != (1, 2)}
        assert data['shared_total_error'] is True
        assert R(data['aligned_loss']) == R(1001, 1000)
    else:
        derivatives = ((0, 1, 1), (0, 3, 0), (2, 1, 3), (2, 3, 2),
                       (3, 3, 10), (3, 4, 4), (4, 1, 5), (4, 3, 4),
                       (5, 3, 12), (5, 4, 6))
        expected = {(-1, 0, 0, -1)} | {
            (i, owner, sign, coordinate)
            for i, owner, coordinate in derivatives for sign in (-1, 1)}
        assert len(expected) == stage['vertices'] == 21
        intervals = []
        for bundle in data['bundles']:
            assert len(bundle['lambda']) == 7
            assert all(isinstance(n, int) and n >= 0 for n in bundle['lambda'])
            vertices = [tuple(row['vertex']) for row in bundle['vertices']]
            assert len(vertices) == len(set(vertices)) == 21
            assert set(vertices) == expected
            assert all('lambda' not in row for row in bundle['vertices'])
            intervals.append((R(bundle['lo']), R(bundle['hi'])))
        assert len(intervals) == len(set(intervals)) == stage['cells']
        left = [p for p in intervals if p[0] < R(1001, 20000)]
        right = [p for p in intervals if p[0] >= R(2, 25)]
        assert len(left) + len(right) == len(intervals)
        closed_chain(left, '-3/8', '1001/20000')
        closed_chain(right, '2/25', '3/8')
        assert len(intervals) * 21 == stage['quartics']
        return
    assert len(expected) == stage['patterns']
    cover = {p: [] for p in expected}
    for row in data['rows']:
        p = tuple(row['owners'])
        assert p in expected
        cover[p].append((R(row['lo']), R(row['hi'])))
    assert len(data['rows']) == stage['quartics']
    for intervals in cover.values():
        assert len(intervals) == len(set(intervals))
        closed_chain(intervals, '-3/8', '3/8')


def main():
    all_files = {'HAND_CANDIDATE_CAPTURE_AT_ONE_THOUSANDTH.md',
                 Path(__file__).name}
    checked = []
    for stage in STAGES:
        all_files.update(stage[field] for field in FILE_FIELDS)
        data = load(stage['data'])
        author = load(stage['arithmetic'])
        independent = load(stage['independent_arithmetic'])
        assert author['status'].startswith('PASS')
        assert independent['status'].startswith('PASS')
        assert author['input_sha256'] == digest(stage['data'])
        assert author['checker_sha256'] == digest(stage['checker'])
        assert R(author['Q']) == R(stage['Q'])
        assert R(author['epsilon']) == R(stage['epsilon'])
        assert author.get('quartics', author.get('polynomials')) == stage['quartics']
        assert author['bernstein_coefficients'] == stage['coefficients']
        assert R(author['minimum_printed_coefficient']) == R(stage['minimum']) > 0
        assert independent['quartics'] == stage['quartics']
        if stage['name'] == 'mixed_owners':
            assert independent['bernstein_coefficients'] == stage['coefficients']
            assert independent['author_replay'] == 'byte-identical in an isolated flat directory; no stderr'
            assert independent['independent_checker_sha256'] == digest(stage['independent_checker'])
        else:
            assert independent['independently_recomputed_bernstein_coefficients'] == stage['coefficients']
            assert independent['author_replay_byte_identical'] is True
        assert R(independent['minimum_printed_coefficient']) == R(stage['minimum'])
        for field in ('manuscript', 'checker', 'data', 'arithmetic'):
            name = stage[field]
            assert independent['sha256'][name] == digest(name), name
        for name, expected in independent['sha256'].items():
            assert digest(name) == expected, ('additional independent binding', name)
        check_domain(data, stage)
        checked.append({**stage, 'status': 'PASS_INDEPENDENTLY_REVIEWED'})

    # Exact inter-theorem threshold, quarter-frame, owner and reserve checks.
    q0, q1, eps = R(9789, 2500), R(1957767069, 500000000), R(1, 1000)
    assert q1 < q0 and eps < R(3, 200) < R(2, 5)
    offsets = (-1, -1, 0, 0, 1, 1, 2)
    quarter_word = (0, 1, 0, 1, 0, 1, 1)
    assert tuple(offsets[i+1] - offsets[i] for i in range(6)) + (
        offsets[0] + 4 - offsets[6],) == quarter_word
    owners = ((1, 3), (1,), (1, 3), (3, 4), (1, 3), (3, 4), (2,))
    assert len(list(product(*owners))) == 32
    assert R(56793, 5000000) - R(93, 10) * eps == R(10293, 5000000) > 0
    assert sum(stage['quartics'] for stage in STAGES) == 3513
    assert sum(stage['coefficients'] for stage in STAGES) == 17565

    dependencies = (
        'HAND_CANDIDATE_MISMATCH_BOOTSTRAP.md',
        'verify_candidate_mismatch_bootstrap.py',
        'candidate_mismatch_bootstrap_arithmetic.json',
        'HAND_TERMINAL_WITH_AUTOMATIC_SLIDERS.md',
        'verify_automatic_slider_terminal.py',
        'automatic_slider_terminal_arithmetic.json',
        'AUTOMATIC_SLIDER_TERMINAL_INDEPENDENT_AUDIT.md',
        'verify_automatic_slider_terminal_independently.py',
        'automatic_slider_terminal_independent_audit.json',
        'HAND_EXACT_CENTER_SQUARE_COMPLETION.md',
        'COMPLETE_EQUALITY_PARAMETER_DOMAIN.md',
        'EQUALITY_PULLBACK_TO_ORIGINAL_SQUARES.md',
    )
    files = {}
    for name in sorted(all_files):
        raw = locate(name).read_bytes()
        files[name] = {'sha256': sha256(raw).hexdigest(), 'bytes': len(raw)}
    dep = {}
    for name in dependencies:
        raw = locate(name).read_bytes()
        dep[name] = {'sha256': sha256(raw).hexdigest(), 'bytes': len(raw)}
    result = dict(
        status='PASS_INDEPENDENTLY_REVIEWED_CONDITIONAL_HAND_CAPTURE',
        scope='For candidate roles, retained forward SAT, the displayed coarse tangent cuts, core avoidance, containment q<=Q1 and S<=1/1000: every required owner and 1/10<t<4/25 follow; the automatic-slider terminal gives q>=q* with its equality conditions.',
        excluded_scope='This manifest does not certify the global mismatch contraction to S<=1/1000 or omit the boundary/original transfer in an application.',
        radius_ceiling=str(q1), mismatch_premise=str(eps),
        roles=['H', 'G', 'A', 'B', 'T', 'D', 'E'],
        quarter_word=list(quarter_word), aligned_edges=[0, 2, 3, 4, 5],
        tangent_domains=[['1/2','1'],['-4/5','-1/20'],['0','1'],['-1','0'],
                         ['1/20','4/5'],['-1','-1/2'],['-1','0']],
        allowed_owners=[list(p) for p in owners],
        strict_tilt_interval=['1/10','4/25'],
        terminal_linear_reserve='10293/5000000',
        total_quartics=3513, total_bernstein_coefficients=17565,
        stages=checked, files=files, existing_dependencies=dep,
    )
    # Publish only after every expected review and exact interface has passed.
    OUTPUT.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ('status', 'total_quartics',
          'total_bernstein_coefficients', 'radius_ceiling', 'mismatch_premise')}, indent=2))
    print('Bound package files:', len(files), '; existing dependencies:', len(dep))


if __name__ == '__main__':
    main()
