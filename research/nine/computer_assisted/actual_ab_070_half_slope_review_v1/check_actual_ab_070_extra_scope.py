"""Exact domain controls for the selected-extra slope restriction."""
if not __debug__:
    raise RuntimeError('Assertions are required')

from copy import deepcopy
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import tempfile

ROOT = Path('/workspace/scratch/f9f48fcfb253')
PACKET = ROOT / 'd_work/actual_ab_070_afad_review/research/nine/computer_assisted/actual_AB_two_link_row_070_bounded_extra_v1'
CHECKER_SHA = '4963058a1896b1518dd533f350c3ba13497c9b581c9068dde5356fb8df0c2af6'


def main():
    checker = PACKET / 'check_conditional_three_angle.py'
    assert sha256(checker.read_bytes()).hexdigest() == CHECKER_SHA
    spec = importlib.util.spec_from_file_location('bounded_extra_checker', checker)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    name = 'spmm_o01_k0.json'
    raw = json.loads((PACKET / 'cover' / name).read_text())
    expected = (raw['signs'], raw['owners'], raw['selected_owner'])
    rejected = []
    with tempfile.TemporaryDirectory(prefix='bounded_extra_scope_') as temporary:
        path = Path(temporary) / name
        for label, box in [
            ('restriction_moved_from_extra_to_D', ['17/72', '29/70', '29/70']),
            ('restriction_moved_from_extra_to_B', ['29/70', '29/70', '17/72']),
            ('extra_restriction_omitted', ['29/70', '29/70', '29/70']),
        ]:
            changed = deepcopy(raw)
            changed['root_upper'] = box
            path.write_text(json.dumps(changed) + '\n')
            try:
                module.check_file(path, expected)
            except AssertionError:
                rejected.append(label)
            else:
                raise AssertionError('Accepted a changed physical angle domain: ' + label)

    # tan(theta)=2*x/(1-x*x) is increasing on [0,1). For tan<=1/2,
    # x*x+4*x-1<=0 gives x<=sqrt(5)-2. The larger rational bound is strict.
    half_angle_upper = F(17, 72)
    assert (2 + half_angle_upper) ** 2 - 5 == F(1, 5184) > 0
    assert F(99, 70) ** 2 - 2 == F(1, 4900) > 0
    assert 2 * F(7, 10) ** 2 == F(49, 50) < 1
    assert F(701, 1000) - F(7, 10) == F(1, 1000)
    intervals = [(F(-1), F(-1, 2)), (F(-1, 2), F(1, 2)), (F(1, 2), F(1))]
    assert intervals[0][0] == -1 and intervals[-1][1] == 1
    assert all(left[1] == right[0] for left, right in zip(intervals, intervals[1:]))

    # A rational scalar configuration demonstrates why the extra, not B,
    # must be restricted. This is not a nine-square packing counterexample.
    alpha, beta = F(21, 29), F(20, 29)
    assert alpha * alpha + beta * beta == 1 and alpha >= beta
    slope = beta / alpha
    r01 = (1 + alpha * alpha - beta * beta + 2 * alpha * beta) / 2
    r12 = (1 + alpha + beta) / 2
    toll = F(55, 64) * beta - F(119, 92) * (1 - alpha)
    c = r01 / alpha + r12 + F(1, 2) - (alpha + beta) / 2 + toll - 2
    deficit = c - F(701, 1000) * slope
    assert slope > F(1, 2) and deficit < 0
    report = {
        'status': 'PASS_BOUNDED_EXTRA_DOMAIN_AND_GUARD_NECESSITY_CONTROLS',
        'checker_sha256': CHECKER_SHA,
        'rejected_wrong_angle_domains': rejected,
        'half_angle_upper': str(half_angle_upper),
        'half_angle_enclosure_positive_reserve': '1/5184',
        'three_closed_slope_intervals': [[str(x) for x in interval] for interval in intervals],
        'unrestricted_scalar_counterexample': {
            'D_frame': [str(alpha), str(beta)], 'extra_frame': [str(alpha), str(-beta)],
            'B_frame': ['1', '0'], 'owners': [0, 2],
            'extra_absolute_slope': str(slope), 'C_minus_701_over_1000_M': str(deficit),
            'physical_packing_counterexample_claimed': False,
        },
        'source_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
        'new_originals': 0, 'new_masks': 0,
    }
    path = ROOT / 'd_work/ACTUAL_AB_070_EXTRA_SCOPE_CONTROLS.json'
    assert not path.exists()
    path.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'status': report['status'], 'report_sha256': sha256(path.read_bytes()).hexdigest(),
                      'exact_unrestricted_scalar_deficit': str(deficit)}))


if __name__ == '__main__':
    main()
