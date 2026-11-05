"""Root physical-formula checks and damaged-cover controls for the 3/5 extension."""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from copy import deepcopy
from hashlib import sha256
import argparse
import importlib.util
import json
import tempfile

if not __debug__:
    raise RuntimeError('Exact checks require assertions.')


def load_checker(folder):
    source = folder / 'check_conditional_three_angle.py'
    spec = importlib.util.spec_from_file_location('bounded_extra_independent', source)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def evaluate(poly, point):
    return sum(c * point[0] ** e[0] * point[1] ** e[1] * point[2] ** e[2]
               for e, c in poly.items())


def physical_difference(frames, owners, selected):
    a = [p[0] for p in frames]
    b = [p[1] for p in frames]
    support = []
    for i in (0, 1):
        j = i + 1
        support.append((1 + a[i] * a[j] + b[i] * b[j]
                        + abs(b[i] * a[j] - a[i] * b[j])) / 2)
    good_toll = F(55, 64) * abs(b[0]) - F(119, 92) * (1 - a[0])
    halfwidth_difference = (a[2] + abs(b[2]) - a[0] - abs(b[0])) / 2
    return (support[0] / a[owners[0]] + support[1] / a[owners[1]]
            + good_toll + halfwidth_difference - 2
            - F(701, 1000) * abs(b[selected] / a[selected]))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('theorem_folder', type=Path)
    parser.add_argument('report', type=Path)
    args = parser.parse_args()
    checker = load_checker(args.theorem_folder)
    points = [tuple(map(F, p)) for p in [
        (0, 0, 0), ('1/8', 0, 0), (0, '1/8', 0), (0, 0, '1/8'),
        ('1/8', '1/8', '1/8'), ('3/8', '1/4', '3/8'),
        ('29/70', '5/18', '29/70'), ('1/16', '2/9', '1/3'),
        ('3/10', '1/10', 0)]]
    expansions = 0
    for u, v in product((-1, 1), repeat=2):
        signs = [1, u, v]
        for t, s in product((0, 1), repeat=2):
            owners = [t, 1 + s]
            for k in sorted(set(owners)):
                polynomials = checker.reconstruct(signs, owners, k)
                for point in points:
                    assert all(0 <= x <= upper for x, upper in zip(point, checker.UPPER))
                    frames = [((1 - x*x)/(1 + x*x), sign*2*x/(1 + x*x))
                              for x, sign in zip(point, signs)]
                    assert all(a*a + b*b == 1 for a, b in frames)
                    denominator = F(736000)
                    for x in point:
                        denominator *= 1 - x**4
                    values = [evaluate(p, point) for p in polynomials]
                    reconstructed = (values[0] + abs(values[1]) + abs(values[2])) / denominator
                    assert reconstructed == physical_difference(frames, owners, k)
                    expansions += 1
    assert expansions == 252

    cases = []
    for path in sorted((args.theorem_folder / 'cover').glob('*.json')):
        if path.name == 'MANIFEST.json':
            continue
        record = json.loads(path.read_text())
        if len(record['leaves']) > 1:
            cases.append((path, record))
    assert cases
    path, original = min(cases, key=lambda e: (len(e[1]['leaves']), e[0].name))
    expected = (original['signs'], original['owners'], original['selected_owner'])
    checker.check_file(path, expected)
    mutations = []
    def add(name, change):
        record = deepcopy(original)
        change(record)
        mutations.append((name, record))
    add('changed_middle_box', lambda r: r['root_upper'].__setitem__(1, '1/2'))
    add('changed_scalar_coefficient', lambda r: r.__setitem__('coefficient', '641/1000'))
    add('changed_variation', lambda r: r.__setitem__('target_variation', '3/5'))
    add('nonempty_frontier', lambda r: r['frontier'].append([]))
    add('excess_absolute_value_weight', lambda r: r['leaves'][0]['weights'].__setitem__(0, 9))
    add('changed_minimum', lambda r: r['leaves'][0].__setitem__('coefficient_min', str(int(r['leaves'][0]['coefficient_min']) + 1)))
    add('changed_positive_minimum', lambda r: r['leaves'][0].__setitem__('positive_coefficient_min', str(int(r['leaves'][0]['positive_coefficient_min']) + 1)))
    add('missing_leaf', lambda r: r['leaves'].pop(0))
    add('duplicate_leaf', lambda r: r['leaves'].append(deepcopy(r['leaves'][0])))
    add('false_origin_flag', lambda r: r['leaves'][0].__setitem__('origin_leaf', not r['leaves'][0]['origin_leaf']))
    rejected = []
    with tempfile.TemporaryDirectory(prefix='bounded_extra_root_controls_') as tmp:
        for name, damaged in mutations:
            damaged_path = Path(tmp) / (name + '.json')
            damaged_path.write_text(json.dumps(damaged))
            try:
                checker.check_file(damaged_path, expected)
            except (AssertionError, ValueError, KeyError, IndexError):
                rejected.append(name)
            else:
                raise AssertionError(('damaged cover accepted', name))
    assert len(rejected) == 10

    counter_frames = [(F(21, 29), F(20, 29)), (F(21, 29), F(-20, 29)), (F(1), F(0))]
    deficit = physical_difference(counter_frames, [0, 2], 0)
    assert deficit == F(-100711, 5602800) < 0
    assert abs(counter_frames[2][1] / counter_frames[2][0]) <= F(3, 5)
    assert abs(counter_frames[1][1] / counter_frames[1][0]) > F(3, 5)
    assert F(35, 6)**2 - 34 == F(1, 36)
    assert 3*F(5, 18)**2 + 10*F(5, 18) - 3 == F(1, 108)
    assert 2*F(7, 10)**2 == F(49, 50) < 1
    report = {
        'status': 'PASS_ROOT_PHYSICAL_FORMULA_AND_DAMAGED_COVER_CONTROLS',
        'physical_frame_formula_comparisons': expansions,
        'damaged_covers_rejected': rejected,
        'damaged_cover_fixture': path.name,
        'damaged_cover_fixture_sha256': sha256(path.read_bytes()).hexdigest(),
        'selected_extra_guard_required': True,
        'wrongly_bounding_B_instead_of_extra_scalar_deficit': str(deficit),
        'counterexample_selected_extra_slope': '20/21',
        'counterexample_B_slope': '0',
        'checker_sha256': sha256((args.theorem_folder / 'check_conditional_three_angle.py').read_bytes()).hexdigest(),
        'root_control_source_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
        'new_original_cells': 0,
        'new_masks': 0,
    }
    args.report.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report))


if __name__ == '__main__':
    main()
