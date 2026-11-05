"""Targeted fail-closed controls for the bounded-extra7/10 scalar cover.

This does not establish a physical caller. It exercises the independent
Fraction checkers at fixed committed bytes and records exact source identities.
"""
if not __debug__:
    raise RuntimeError('Assertions must be enabled')

import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path('/workspace/scratch/f9f48fcfb253')
PACKETS = ROOT / 'd_work/actual_ab_070_afad_review/research/nine/computer_assisted'
CASES = [
    ('actual_AB_two_link_row_070_bounded_extra_v1', 'check_conditional_three_angle.py',
     '4963058a1896b1518dd533f350c3ba13497c9b581c9068dde5356fb8df0c2af6',
     'cover', ROOT / 'd_work/ACTUAL_AB_070_ROOT_FRESH_REPLAY.json'),
]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    audits = []
    for number, (package, filename, expected_hash, folder, replay_path) in enumerate(CASES):
        directory = PACKETS / package
        checker = directory / filename
        assert digest(checker) == expected_hash
        spec = importlib.util.spec_from_file_location('new_ab_checker_' + str(number), checker)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        replay = json.loads(replay_path.read_text())
        assert replay['status'] == 'PASS_COMPLETE_EXACT_TWO_LINK_SCALAR_COVER'
        assert replay['domains'] == 28 and replay['frontier'] == 0
        assert replay['checker_sha256'] == expected_hash
        name = replay['audits'][0]['file']
        original = json.loads((directory / folder / name).read_text())
        expected = (original['signs'], original['owners'], original['selected_owner'])
        mutations = []

        def mutate(label, operation):
            altered = copy.deepcopy(original)
            operation(altered)
            mutations.append((label, altered))

        mutate('wrong_sign_domain', lambda d: d['signs'].__setitem__(0, -1))
        mutate('wrong_owner_domain', lambda d: d['owners'].__setitem__(0, 1 - d['owners'][0]))
        mutate('changed_root_endpoint', lambda d: d.__setitem__('root_upper', '1/2'))
        mutate('unresolved_frontier', lambda d: d.__setitem__('frontier', [[[0, 0]]]))
        mutate('missing_closed_leaf', lambda d: d['leaves'].pop())
        mutate('duplicated_closed_leaf', lambda d: d['leaves'].append(copy.deepcopy(d['leaves'][0])))
        mutate('weight_outside_absolute_support_bound',
               lambda d: d['leaves'][0]['weights'].__setitem__(0, d['leaves'][0]['weight_denominator'] + 1))
        mutate('false_integer_coefficient_minimum',
               lambda d: d['leaves'][0].__setitem__('coefficient_min', str(int(d['leaves'][0]['coefficient_min']) + 1)))
        mutate('false_origin_face',
               lambda d: d['leaves'][0].__setitem__('origin_leaf', not d['leaves'][0]['origin_leaf']))
        if number == 1:
            mutate('invalid_toll_branch', lambda d: d['leaves'][0].__setitem__('toll_branch', 2))
            mutate('zero_weight_denominator', lambda d: d['leaves'][0].__setitem__('weight_denominator', 0))
        rejected = []
        with tempfile.TemporaryDirectory(prefix='actual_ab_certificate_controls_') as temporary:
            target = Path(temporary) / name
            target.write_text(json.dumps(original) + '\n')
            module.check_file(target, expected)
            for label, altered in mutations:
                target.write_text(json.dumps(altered) + '\n')
                try:
                    module.check_file(target, expected)
                except AssertionError:
                    rejected.append(label)
                else:
                    raise AssertionError('Accepted damaged certificate: ' + label)
        optimized = subprocess.run([sys.executable, '-O', '-B', '-S', str(checker), '--help'],
                                   capture_output=True, text=True)
        assert optimized.returncode != 0 and 'Assertions are required' in optimized.stderr
        audits.append({
            'package': package, 'checker_sha256': expected_hash,
            'positive_complete_replay_sha256': digest(replay_path),
            'positive_domains': replay['domains'], 'positive_leaves': replay['leaves'],
            'positive_coefficients': replay['bernstein_coefficients'],
            'single_domain_positive_control': name, 'rejected_damage_controls': rejected,
            'optimized_python_rejected': True,
        })
    assert not any(name in sys.modules for name in ('scipy', 'numpy'))
    result = {
        'status': 'PASS_NEW_ACTUAL_AB_SCALAR_FAIL_CLOSED_CONTROLS',
        'controls': sum(len(a['rejected_damage_controls']) + 1 for a in audits),
        'audits': audits, 'source_sha256': digest(Path(__file__)),
        'physical_caller_separately_required': True,
        'new_original_cells': 0, 'new_masks': 0,
    }
    output = ROOT / 'd_work/ACTUAL_AB_070_ROOT_SCALAR_CONTROLS.json'
    assert not output.exists()
    output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'status': result['status'], 'controls': result['controls'],
                      'report_sha256': digest(output)}))


if __name__ == '__main__':
    main()
