#!/usr/bin/env python3
"""Replay the published first real LP certificate using exact arithmetic only."""
if not __debug__:
    raise RuntimeError('The first-use replay requires assertions.')

import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.abc
import importlib.util
import json
from pathlib import Path
import sys

FOUNDATION_SHA = 'ac389f6184af6503294a13fb30c1da82e38d052a5d579bf43ccd4a0017b0485b'
PILOT_SHA = '94dacdafea838579c1bf81b74b64685a2729679549173ef47ee67a3310e84a78'
DISCOVERY_SHA = 'ddfedb0223c21441359d9b23d1cf49c77c7a87800d9e4f61e1b8f016abf44965'
BLOCKED = {'numpy', 'scipy', 'highspy', 'sympy', 'z3'}


class NoNumericalImports(importlib.abc.MetaPathFinder):
    def find_spec(self, fullname, path=None, target=None):
        if fullname.split('.')[0] in BLOCKED:
            raise ImportError('Numerical import is forbidden in exact replay: '+fullname)
        return None


def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()


def member(root, relative):
    assert isinstance(relative, str)
    raw = Path(relative)
    assert not raw.is_absolute() and '..' not in raw.parts
    path = (root/raw).resolve()
    assert path.is_relative_to(root) and path.is_file()
    return path


def verify_inventory(root, filename, expected=None):
    path = root/filename
    if expected is not None:
        assert digest(path) == expected
    inventory = json.loads(path.read_text())
    for relative, entry in inventory['files'].items():
        value = member(root, relative)
        assert value.stat().st_size == entry['bytes']
        assert digest(value) == entry['sha256'], relative
    return inventory


def load(name, path, expected):
    assert digest(path) == expected
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def run(packet, foundation, output):
    packet, foundation, output = map(lambda p: Path(p).resolve(), (packet, foundation, output))
    assert not output.exists() and not output.is_relative_to(packet) and not output.is_relative_to(foundation)
    assert not any(name.split('.')[0] in BLOCKED for name in sys.modules)
    sys.meta_path.insert(0, NoNumericalImports())
    publication = verify_inventory(packet, 'PUBLICATION_MANIFEST.json')
    assert publication['schema'] == 'strict011_discovery_first_actual_use_v1'
    assert publication['whole_mask_credit'] == publication['original_cell_credit'] == 0
    assert publication['foundation_checkpoint_sha256'] == FOUNDATION_SHA
    frozen = verify_inventory(foundation, 'CHECKPOINT_MANIFEST.json', FOUNDATION_SHA)
    discovery = verify_inventory(packet/'discovery', 'SOURCE_FREEZE.json', DISCOVERY_SHA)
    assert discovery['required_checkpoint_sha256'] == FOUNDATION_SHA
    pilot = packet/'actual_pilot'
    assert digest(pilot/'manifest.json') == PILOT_SHA
    wrapper_rel = 'strict_011_representative_cover_v1/verify_strict_011_complete_tree.py'
    wrapper = load('portable_first_actual_complete_cover', foundation/wrapper_rel,
                   frozen['files'][wrapper_rel]['sha256'])
    report = wrapper.verify(pilot/'manifest.json', foundation/'dependencies/workspace',
                            foundation/'strict_011_representative_root_v1')
    assert report['status'] == 'PASS_COMPLETE_STRICT011_REPRESENTATIVE_COVER_WITH_OPEN_DOMAINS'
    assert report['root_id'] == 'full-strict-01100-representative-root-v1'
    assert report['mask'] == '011/00' and report['radius_mode'] == 'strict'
    assert (report['physical_originals'], report['original_corners'], report['original_pairs'], report['marked_cones']) == (9,36,36,5)
    assert (report['nodes'], report['excluded_leaves'], report['open_leaves']) == (5,1,3)
    assert report['complete_unions'] == {'proxy':1}
    assert report['exact_totals'] == {'rounds':0,'deductions':0,'printed_rows_checked':4}
    assert report['excluded_leaf_ids'] == [1] and report['open_leaf_ids'] == [2,3,4]
    assert not report['complete'] and not report['whole_mask_proved'] and not report['conditional_theorem_used']
    manifest = json.loads((pilot/'manifest.json').read_text())
    terminal_entry = next(e for e in manifest['nodes'] if e['id'] == 1)
    terminal_path = member(pilot, terminal_entry['file'])
    assert digest(terminal_path) == terminal_entry['sha256']
    record = json.loads(terminal_path.read_text())
    terminal = record['terminal']
    expected_rows = {
        'strict011v2:inset_tangent:0:1': ({18:F(-1,2),36:F(-1,2),45:F(-1)},F(-1)),
        'strict011v2:inset_tangent:1:1': ({19:F(-1,2),37:F(-1,2),46:F(-1)},F(-1)),
        'strict011v2:mask:0:1:0': ({0:F(1),2:F(-1),18:F(1,2),36:F(1,2),19:F(1,2),37:F(1,2)},F(0)),
        'strict011v2:proxy:0:1:0:-1': ({0:F(-1),2:F(1),45:F(1),46:F(1)},F(0))}
    assert len(terminal['rows']) == 4 and {r['name'] for r in terminal['rows']} == set(expected_rows)
    indexed = {}
    for row in terminal['rows']:
        terms = {k:F(v) for k,v in row['coefficients']}
        assert len(terms) == len(row['coefficients'])
        assert (terms,F(row['rhs'])) == expected_rows[row['name']]
        assert row['index'] not in indexed
        indexed[row['index']] = row
    assert len(terminal['weights']) == 4 and {k for k,w in terminal['weights']} == set(indexed)
    coefficients, rhs = [F(0)]*54, F(0)
    for index, weight in terminal['weights']:
        assert type(weight) is int and weight == 274877906944
        factor = F(weight,1<<40)
        assert factor == F(1,4)
        row = indexed[index]
        rhs += factor*F(row['rhs'])
        for column,value in row['coefficients']:
            coefficients[column] += factor*F(value)
    absolute = list(map(F,terminal['absolute_variable_bounds']))
    assert len(absolute) == 54 and min(absolute) >= 0
    payment = sum(bound*abs(coefficient) for bound,coefficient in zip(absolute,coefficients))
    assert coefficients == [F(0)]*54 and rhs == -F(1,2) and payment == 0
    assert terminal['weighted_coefficients'] == list(map(str,coefficients))
    assert F(terminal['weighted_rhs']) == rhs and F(terminal['reserve']) == F(1,2)
    # Rehash all source and certificate bytes after the exact replay.
    verify_inventory(packet, 'PUBLICATION_MANIFEST.json')
    verify_inventory(foundation, 'CHECKPOINT_MANIFEST.json', FOUNDATION_SHA)
    assert not any(name.split('.')[0] in BLOCKED for name in sys.modules)
    result = dict(status='PASS_PORTABLE_FIRST_ACTUAL_LP_EXACT_REPLAY',
        foundation_checkpoint_sha256=FOUNDATION_SHA,
        publication_manifest_sha256=digest(packet/'PUBLICATION_MANIFEST.json'),
        discovery_source_freeze_sha256=DISCOVERY_SHA,
        source_script_sha256=digest(Path(__file__)),
        actual_manifest_sha256=PILOT_SHA,
        exact_tree_report=report,
        literal_dual=dict(nonzero_weights=4,each_weight='1/4',weighted_rhs='-1/2',
            nonzero_residual_columns=0,residual_absolute_bound_payment='0',reserve='1/2'),
        actual_nonzero_residual_exercised=False,numerical_imports=False,
        original_cell_credit=0,whole_mask_credit=0)
    with output.open('x') as stream:
        json.dump(result,stream,indent=2,sort_keys=True)
        stream.write('\n')
    print(json.dumps(dict(status=result['status'],output=str(output),sha256=digest(output),
                          nodes=5,excluded_leaves=1,open_leaves=3,reserve='1/2')))
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--foundation',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    run(Path(__file__).resolve().parent,args.foundation,args.output)
