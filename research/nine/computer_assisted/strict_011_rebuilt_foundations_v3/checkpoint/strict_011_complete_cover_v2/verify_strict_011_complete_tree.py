#!/usr/bin/env python3
"""Fresh full strict011 exact 4/8/2 tree replay, with no legacy ancestry.

The mathematical adapter and generic rational core are hash-pinned.  Every
node, including OPEN leaves, is checked from its exact reconstructed parent.
No producer, optimizer, conditional theorem, or symmetry layer is imported.
"""
if not __debug__:
    raise RuntimeError('Exact complete-tree replay rejects optimized Python.')

import argparse
from collections import Counter
from copy import deepcopy
from fractions import Fraction as F
import hashlib
import importlib.util
from itertools import product
import json
from pathlib import Path, PurePosixPath
import time

MODEL_BINDING = '68fc9bdf42eae978da0a49acc003333a7c658a7fde90b91182ef93d2986891cb'
ADAPTER_SHA = 'de6942227f66cf3f6b979595af06ac5e794b903a5ce158d8b4c3e82e35ab4be7'
ARITHMETIC_SHA = '1d069c90f289dce136e41afeb5d564ec7016ac06f58eeb733ca7552801b6fafc'
PROXY_SHA = '3b46b8a966c712e23894ae4cd7964355730f2bfe3c58a04871ade9d35ddf1277'


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read_module(name, path, expected):
    assert digest(path) == expected, str(path)
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def local_file(folder, name):
    assert type(name) is str
    relative = PurePosixPath(name)
    assert not relative.is_absolute() and '..' not in relative.parts and relative.parts
    path = (folder/name).resolve()
    assert path.is_relative_to(folder) and path.is_file()
    return path


def verify(manifest_path, workspace, model_folder):
    started = time.monotonic()
    manifest_path, workspace, model_folder = map(lambda p: Path(p).resolve(),
                                                (manifest_path, workspace, model_folder))
    folder = manifest_path.parent
    frozen = {}

    def pin(path, expected=None):
        path = Path(path).resolve()
        value = digest(path)
        if expected is not None:
            assert value == expected, str(path)
        assert path not in frozen or frozen[path] == value
        frozen[path] = value
        return value

    pin(Path(__file__))
    binding_path = model_folder/'PREMISE_BINDINGS.json'
    pin(binding_path, MODEL_BINDING)
    binding = json.loads(binding_path.read_text())
    for name, entry in binding['local_files'].items():
        path = local_file(model_folder, name)
        assert path.stat().st_size == entry['bytes']
        pin(path, entry['sha256'])
    adapter_path = model_folder/'independent_strict_011_adapter.py'
    generic_path = workspace/'b_work/independent_physical_sat_replay.py'
    proxy_path = workspace/'b_work/independent_physical_proxy_cover.py'
    for path, expected in ((adapter_path, ADAPTER_SHA), (generic_path, ARITHMETIC_SHA), (proxy_path, PROXY_SHA)):
        pin(path, expected)
    I = read_module('fresh_strict011_exact_adapter', adapter_path, ADAPTER_SHA)
    G = read_module('fresh_strict011_exact_arithmetic', generic_path, ARITHMETIC_SHA)
    X = read_module('fresh_strict011_exact_proxy', proxy_path, PROXY_SHA)
    adapter = I.Adapter()
    manifest_hash = pin(manifest_path)
    manifest = json.loads(manifest_path.read_text())
    assert set(manifest) == {'schema', 'root_document', 'root', 'nodes'}
    assert manifest['schema'] == 'fresh_full_strict011_complete_tree_v1'
    assert type(manifest['root']) is int and manifest['root'] >= 0
    root_ref = manifest['root_document']
    assert set(root_ref) == {'file', 'sha256'}
    document_path = local_file(folder, root_ref['file'])
    pin(document_path, root_ref['sha256'])
    assert root_ref['sha256'] == binding['local_files']['snapshots/ROOT_DOCUMENT.json']['sha256']
    initial = I.verify_root(json.loads(document_path.read_text()))
    assert I.state_view(initial) == json.loads((model_folder/'snapshots/ROOT_DOCUMENT.json').read_text())['initial']
    assert isinstance(manifest['nodes'], list) and manifest['nodes']
    entries = {}
    node_files = set()
    for entry in manifest['nodes']:
        assert set(entry) in ({'id', 'file', 'sha256'}, {'id', 'file', 'sha256', 'split'})
        node_id = entry['id']
        assert type(node_id) is int and node_id >= 0 and node_id not in entries
        path = local_file(folder, entry['file'])
        assert path not in node_files and path != document_path
        node_files.add(path)
        entries[node_id] = entry
    assert manifest['root'] in entries
    visited, active, totals, splits = set(), set(), Counter(), Counter()
    open_leaves, closed_leaves, audits = [], [], []

    def walk(node_id, expected_state):
        assert node_id in entries and node_id not in visited and node_id not in active
        active.add(node_id)
        I.validate_state(expected_state)
        entry = entries[node_id]
        path = local_file(folder, entry['file'])
        pin(path, entry['sha256'])
        record = json.loads(path.read_text())
        audit, state = G.check_record(record, expected_state, adapter)
        for key in ('rounds', 'deductions', 'printed_rows_checked'):
            totals[key] += audit[key]
        audits.append(dict(node=node_id, file=entry['file'], sha256=entry['sha256'], arithmetic=audit))
        if state is None:
            assert 'split' not in entry, 'An excluded node has no children.'
            closed_leaves.append(node_id)
            closed = True
        elif 'split' not in entry:
            open_leaves.append(node_id)
            closed = False
        else:
            split = entry['split']
            kind = split['kind']
            children = split['children']
            assert isinstance(children, list)
            if kind in ('sat', 'proxy'):
                assert set(split) == {'kind', 'pair', 'children'}
                pair = split['pair']
                assert type(pair) is list and len(pair) == 2
                assert all(type(i) is int for i in pair) and 0 <= pair[0] < pair[1] < 9
                expected = set(product(tuple(pair), (0, 1), (-1, 1))) if kind == 'sat' else set(product((0, 1), (-1, 1)))
                actual = []
                for child in children:
                    assert set(child) == {'choice', 'node'} and type(child['node']) is int
                    assert type(child['choice']) is list and all(type(i) is int for i in child['choice'])
                    actual.append(tuple(child['choice']))
                assert len(actual) == len(expected) and len(set(actual)) == len(expected) and set(actual) == expected
                successors = [(child['node'], G.sat_child(state, pair, child['choice'], adapter)
                    if kind == 'sat' else X.proxy_child(state, pair, child['choice'], adapter)) for child in children]
            else:
                assert kind == 'angle'
                assert set(split) == {'kind', 'original', 'cut', 'children'}
                original, cut = split['original'], F(split['cut'])
                assert type(original) is int and 0 <= original < 9
                assert str(cut) == split['cut']
                sides = []
                for child in children:
                    assert set(child) == {'side', 'node'} and type(child['node']) is int
                    assert type(child['side']) is int
                    sides.append(child['side'])
                assert len(sides) == 2 and set(sides) == {0, 1}
                successors = [(child['node'], I.angle_child(state, original, cut, child['side'])) for child in children]
            assert len({node for node, _ in successors}) == len(successors)
            splits[kind] += 1
            results = [walk(child, child_state) for child, child_state in successors]
            closed = all(results)
        active.remove(node_id)
        visited.add(node_id)
        return closed

    complete = walk(manifest['root'], initial)
    assert visited == set(entries), 'Every declared record must belong to this complete cover.'
    assert not active and complete == (not open_leaves)
    assert len(closed_leaves)+len(open_leaves)+sum(splits.values()) == len(entries)
    assert 4*splits['proxy']+8*splits['sat']+2*splits['angle'] == len(entries)-1
    for path, expected in frozen.items():
        assert digest(path) == expected, 'A frozen replay input changed: '+str(path)
    return dict(status='PASS_COMPLETE_STRICT011_PHYSICAL_TREE' if complete else 'PASS_COMPLETE_STRICT011_COVER_WITH_OPEN_DOMAINS',
        root_id=initial['id'], mask='011/00', radius_mode='strict', target_q='1105/256',
        physical_originals=9, original_corners=36, original_pairs=36, marked_cones=5,
        complete=complete, whole_mask_proved=complete, root_ancestry='FRESH_FULL_CALLER',
        normalized_root=False, conditional_theorem_used=False,
        nodes=len(entries), excluded_leaves=len(closed_leaves), open_leaves=len(open_leaves),
        excluded_leaf_ids=closed_leaves, open_leaf_ids=open_leaves,
        complete_unions=dict(splits), exact_totals=dict(totals), node_audits=audits,
        manifest_sha256=manifest_hash, root_model_binding_sha256=MODEL_BINDING,
        frozen_input_sha256={str(path): value for path, value in frozen.items()},
        numerical_diagnostics_used=False, original_cell_ledger_credit=0,
        automatic_mask_ledger_credit=0, seconds=time.monotonic()-started)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('manifest', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--workspace', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--model-folder', type=Path, default=Path(__file__).resolve().parent.parent/'strict_011_full_root_v2')
    args = parser.parse_args()
    report = verify(args.manifest, args.workspace, args.model_folder)
    with args.output.open('x') as stream:
        json.dump(report, stream, indent=2); stream.write('\n')
    print(json.dumps({k: report[k] for k in ('status', 'nodes', 'excluded_leaves', 'open_leaves', 'complete_unions', 'exact_totals', 'whole_mask_proved')}))


if __name__ == '__main__':
    main()
