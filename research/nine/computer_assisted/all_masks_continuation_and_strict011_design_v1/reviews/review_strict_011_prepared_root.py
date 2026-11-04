#!/usr/bin/env python3
"""Independent literal review of a prepared, uninstalled strict-011 root.

This imports neither the producer nor a geometry/numerical engine.  It checks
the elementary specification and source bindings; it is not a tree replay.
"""
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations, product
from pathlib import Path
import json

ROOT = Path('/workspace/scratch/f9f48fcfb253')
PREPARED = ROOT / 'global_work/strict_011_root_adapter_design'
OUTPUT = Path(__file__).with_name('STRICT_011_PREPARED_ROOT_INDEPENDENT_REVIEW.json')


def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()


def check():
    mapping = json.loads((PREPARED / 'SOURCE_MAP.json').read_text())
    sources = {}
    relocations = {}
    equivalent_paths = {
        'repo/research/nine/computer_assisted/strict_011_actual_AB_application_v1/PUBLICATION_MANIFEST.json':
        'global_work/strict_011_actual_ab_publication/PUBLICATION_MANIFEST.json',
    }
    for entry in mapping['sources']:
        path = ROOT / entry['path']
        if not path.exists():
            assert entry['path'] in equivalent_paths
            actual = ROOT / equivalent_paths[entry['path']]
            relocations[str(path)] = str(actual)
            path = actual
        assert path.stat().st_size == entry['bytes']
        assert digest(path) == entry['sha256']
        sources[str(path)] = entry['sha256']
    for name, entry in mapping['prepared_files'].items():
        path = PREPARED / name
        assert path.stat().st_size == entry['bytes']
        assert digest(path) == entry['sha256']
        sources[str(path)] = entry['sha256']
    for name in ('SOURCE_MAP.json', 'OPTIONAL_UNIVERSAL_CENTER_BOUND.md',
                 'OPTIONAL_UNIVERSAL_CENTER_BOUND.json'):
        sources[str(PREPARED / name)] = digest(PREPARED / name)

    spec = json.loads((PREPARED / 'FRESH_ROOT_SPEC_PREPARED.json').read_text())
    assert spec['mask'] == '011/00' and spec['radius_mode'] == 'strict'
    assert spec['target_q'] == '1105/256'
    assert spec['physical_originals'] == list(range(9))
    assert spec['original_corners'] == [[i, a, b] for i in range(9)
        for a, b in product((-1, 1), repeat=2)]
    pairs = list(combinations(range(9), 2))
    assert spec['original_pairs'] == [list(pair) for pair in pairs]
    covers = spec['owned_pair_cover']
    assert len(covers) == 36
    for pair, cover in zip(pairs, covers):
        assert cover['pair'] == list(pair)
        assert cover['alternatives'] == [list(c) for c in product(pair, (0, 1), (-1, 1))]
    expected_edges = ((0, 1, 0), (1, 2, 1), (2, 3, 1), (4, 5, 0), (5, 6, 0))
    assert len(spec['exact_mask_edges']) == 5
    for (i, j, bit), edge in zip(expected_edges, spec['exact_mask_edges']):
        assert edge == {'pair': [i, j], 'bit': bit,
            'cone': 'xj-xi >= abs(yj-yi)',
            'bit_relation': 'xj-xi < hi+hj' if bit else 'xj-xi >= hi+hj'}
    assert spec['corner_relation'] == 'Every original corner norm_squared < 1105/256'
    assert spec['pair_relation'] == 'Every original pair has disjoint open interiors; physical contact allowed'
    assert spec['strict_predicate_may_not_be_replaced_by_closed_relaxation'] is True
    assert spec['accepted_geometry_adapter'] is False and spec['proof_credit'] == 0
    assert spec['solver_called'] is False and spec['old_001_ancestry_imported'] is False

    initial = spec['initial']
    assert initial['id'] == 'prepared-full-strict-01100-root-v1'
    assert all(initial[key] == [] for key in ('path', 'choices', 'differences', 'diagonal'))
    assert initial['angles'] == [['-1', '1'] for _ in range(9)]
    bounds = [(F(-2), F(2))] * 18 + [(F(7, 10), F(1))] * 9
    bounds += [(F(-3, 4), F(3, 4))] * 9 + [(F(0), F(3, 4))] * 9
    bounds += [(F(1, 3), F(1, 2))] * 9
    assert [[F(x) for x in b] for b in initial['positions'] + initial['scalar']] == [list(b) for b in bounds]
    assert [F(x) for x in spec['absolute_original_variable_bounds']] == [max(abs(a), abs(b)) for a, b in bounds]

    # Reconstruct a complete literal map without executing the producer.
    expected = {}
    def add(name, terms, rhs=0, relation='<='):
        nonzero = sorted((int(k), F(v)) for k, v in terms.items() if F(v))
        expected[name] = (nonzero, F(rhs), relation, '<=')
    for k, (lo, hi) in enumerate(bounds):
        add(f'prepared_strict011_bound_upper_{k}', {k: 1}, hi)
        add(f'prepared_strict011_bound_lower_{k}', {k: -1}, -lo)
    for i in range(9):
        a, b, z = 18 + i, 27 + i, 36 + i
        add(f'prepared_strict011_fold_{i}', {z: 1, a: -1})
        add(f'prepared_strict011_abs_pos_{i}', {b: 1, z: -1})
        add(f'prepared_strict011_abs_neg_{i}', {b: -1, z: -1})
        add(f'prepared_strict011_width_floor_{i}', {a: -1, z: -1}, -1)
    for i, j, bit in expected_edges:
        for sign in (-1, 1):
            add(f'prepared_strict011_cone_{i}_{j}_{sign}',
                {2*i: 1, 2*j: -1, 2*i+1: -sign, 2*j+1: sign})
        sense = -1 if bit else 1
        add(f'prepared_strict011_mask_{i}_{j}_{bit}',
            {2*i: sense, 2*j: -sense, 18+i: F(sense, 2),
             18+j: F(sense, 2), 36+i: F(sense, 2), 36+j: F(sense, 2)},
            relation='<' if bit else '<=')
    rows = spec['elementary_necessary_affine_rows']
    assert len(rows) == spec['row_count'] == len(expected) == 159
    assert len({row['name'] for row in rows}) == len(rows)
    for row in rows:
        literal = ([(int(k), F(v)) for k, v in row['coefficients']], F(row['rhs']),
                   row['source_relation'], row['necessary_affine_relaxation_relation'])
        assert literal == expected[row['name']], row['name']

    q, rho = F(1105, 256), F(91, 60)
    assert q - F(1, 2) == F(977, 256) < 4
    assert F(7, 10)**2 < F(1, 2) < F(3, 4)**2
    assert F(3, 2)**2 > 2
    margin = rho*rho + rho + F(1, 2) - q
    assert margin == F(31, 57600) > 0
    optional = json.loads((PREPARED / 'OPTIONAL_UNIVERSAL_CENTER_BOUND.json').read_text())
    assert optional['note_sha256'] == digest(PREPARED / 'OPTIONAL_UNIVERSAL_CENTER_BOUND.md')
    assert F(optional['positive_polynomial_margin']) == margin
    assert optional['prepared_root_changed'] is False and optional['row_installed'] is False

    return dict(status='PASS_PREPARED_STRICT_011_ROOT_LITERAL_AND_PHYSICAL_DESIGN_REVIEW',
        scope='Prepared specification and hand derivations only; no geometry adapter installation or closure',
        physical_originals=9, original_corners=36, original_pairs=36, center_cones=5,
        complete_owned_pair_cover_alternatives=288, elementary_rows_reconstructed=159,
        strict_reverse_mask_edges=['BC', 'CD'], actual_mask_edges=['AB', 'EF', 'FG'],
        original_path_and_selected_pairs_empty=True, inherited_difference_maps_empty=True,
        old_001_geometry_imported=False, optimizer_called=False, tree_arithmetic_replayed=False,
        optional_universal_center_radius=str(rho), optional_positive_margin=str(margin),
        optional_bound_valid_even_for_closed_containment=True,
        prepared_root_changed=False, geometry_adapter_accepted=False,
        new_original_closures=0, new_mask_closures=0,
        source_sha256=sources, exact_byte_source_relocations=relocations,
        review_script_sha256=digest(__file__))


if __name__ == '__main__':
    report = check()
    with OUTPUT.open('x') as stream:
        json.dump(report, stream, indent=2)
        stream.write('\n')
    print(json.dumps({'status': report['status'], 'report': str(OUTPUT),
                      'sha256': digest(OUTPUT), 'elementary_rows': 159}))
