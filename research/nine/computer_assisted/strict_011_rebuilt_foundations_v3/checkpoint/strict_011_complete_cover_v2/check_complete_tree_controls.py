#!/usr/bin/env python3
"""Build and replay small complete strict011 covers without a solver."""
if not __debug__:
    raise RuntimeError('Exact complete-tree controls reject optimized Python.')

import argparse
from copy import deepcopy
from fractions import Fraction as F
import hashlib
import importlib.util
from itertools import product
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import verify_strict_011_complete_tree as T


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write(path, value):
    with path.open('x') as stream:
        json.dump(value, stream, indent=2); stream.write('\n')


def printed(rows, indices):
    return [dict(index=k, name=rows[k][2], coefficients=[[j, str(c)] for j, c in rows[k][0]],
                 rhs=str(rows[k][1])) for k in sorted(indices)]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--workspace', type=Path, default=HERE.parents[1])
    parser.add_argument('--output-directory', type=Path, required=True)
    args = parser.parse_args()
    workspace, output = args.workspace.resolve(), args.output_directory.resolve()
    output.mkdir(parents=True, exist_ok=False)
    model = HERE.parent/'strict_011_full_root_v2'
    P = T.read_module('fresh011_control_producer', model/'strict_011_root.py',
                     '1912ce1b92f721127957158af83c30655ecc32a8f7a98e46fc801e327a936494')
    G = T.read_module('fresh011_control_arithmetic', workspace/'b_work/independent_physical_sat_replay.py', T.ARITHMETIC_SHA)
    root = P.fresh_state()
    root_bytes = (model/'snapshots/ROOT_DOCUMENT.json').read_bytes()
    root_hash = hashlib.sha256(root_bytes).hexdigest()
    reports, manifests = {}, {}

    def zero(state):
        return dict(status='OPEN', initial=P.state_view(state), rounds=[], final=P.state_view(state))

    def proxy_record(state, sign):
        rows, bounds, propagated, terminal = P.collect(state)
        assert terminal is None
        if sign == -1:
            wanted = {'strict011v2:proxy:0:1:0:-1': 1, 'strict011v2:cone_inset:0:1': 1,
                      'strict011v2:bound:45:-1': 2, 'strict011v2:bound:46:-1': 2}
        else:
            wanted = {'strict011v2:proxy:0:1:0:1': 1,
                      'strict011v2:bound:45:-1': 1, 'strict011v2:bound:46:-1': 1}
        weights = [[k, wanted[row[2]]*(1 << 40)] for k, row in enumerate(rows) if row[2] in wanted]
        assert len(weights) == len(wanted)
        coefficients = [F(0)]*len(bounds)
        rhs = F(0)
        for k, weight in weights:
            factor = F(weight, 1 << 40)
            rhs += factor*rows[k][1]
            for column, coefficient in rows[k][0]:
                coefficients[column] += factor*coefficient
        literal = printed(rows, {k for k, _ in weights})
        if sign == -1:
            assert not any(coefficients) and rhs < 0
            return dict(status='CANDIDATE_CLOSED', initial=P.state_view(state), rounds=[],
                terminal_state=P.state_view(state), terminal=dict(kind='positive_exact_reserve',
                    weights=weights, rows=literal, absolute_variable_bounds=list(map(str, bounds)),
                    weighted_coefficients=list(map(str, coefficients)), weighted_rhs=str(rhs), reserve=str(-rhs))), None
        assert [(k, c) for k, c in enumerate(coefficients) if c] == [(0, F(1)), (2, F(-1))]
        upper = G.ceiling_grid(rhs)
        after = deepcopy(propagated)
        dx, dy = after['differences'][0, 1]
        after['differences'][0, 1] = ((max(dx[0], -upper), dx[1]), dy)
        round_record = dict(before=P.state_view(state), propagated=P.state_view(propagated),
            printed_rows=literal, absolute_variable_bounds=list(map(str, bounds)),
            proposals=[dict(kind='difference', key=[0, 1, 0], sign=-1, objective=[[2, -1], [0, 1]],
                weights=weights, summed_rhs=str(rhs), residual_coefficients=[], residual_correction='0',
                proved_upper=str(rhs), upper=str(upper))], physical_frame_inferences=[], after=P.state_view(after))
        return dict(status='OPEN', initial=P.state_view(state), rounds=[round_record], final=P.state_view(after)), after

    def save_tree(name, records, splits):
        folder = output/name; folder.mkdir()
        with (folder/'root_document.json').open('xb') as stream:
            stream.write(root_bytes)
        entries = []
        for node, record in sorted(records.items()):
            filename = f'node_{node:04d}.json'
            write(folder/filename, record)
            entry = dict(id=node, file=filename, sha256=sha(folder/filename))
            if node in splits:
                entry['split'] = deepcopy(splits[node])
            entries.append(entry)
        manifest = dict(schema='fresh_full_strict011_complete_tree_v1',
            root_document=dict(file='root_document.json', sha256=root_hash), root=0, nodes=entries)
        write(folder/'manifest.json', manifest)
        report = T.verify(folder/'manifest.json', workspace, model)
        assert not report['whole_mask_proved']
        write(folder/'EXACT_REPLAY.json', report)
        reports[name], manifests[name] = report, (folder, manifest)

    save_tree('fresh_root_open', {0: zero(root)}, {})
    records, children, final_plus = {0: zero(root)}, [], None
    for node, choice in enumerate(product((0, 1), (-1, 1)), 1):
        child = P.physical_child(root, 'proxy', (0, 1), choice)
        if choice[0] == 0:
            records[node], final = proxy_record(child, choice[1])
            if choice[1] == 1:
                final_plus = final; plus_node = node
        else:
            records[node] = zero(child)
        children.append(dict(choice=list(choice), node=node))
    splits = {0: dict(kind='proxy', pair=[0, 1], children=children)}
    save_tree('complete_AB_proxy_union', records, splits)
    assert reports['complete_AB_proxy_union']['excluded_leaves'] == 1
    assert reports['complete_AB_proxy_union']['open_leaves'] == 3
    assert reports['complete_AB_proxy_union']['exact_totals'] == dict(rounds=1, deductions=1, printed_rows_checked=7)
    nested_records, nested_splits = deepcopy(records), deepcopy(splits)
    nested_splits[plus_node] = dict(kind='angle', original=3, cut='0',
                                  children=[dict(side=0, node=5), dict(side=1, node=6)])
    for side in (0, 1):
        nested_records[5+side] = zero(P.angle_child(final_plus, 3, 0, side))
    save_tree('proxy_bound_then_complete_angle', nested_records, nested_splits)
    assert reports['proxy_bound_then_complete_angle']['nodes'] == 7
    assert reports['proxy_bound_then_complete_angle']['open_leaves'] == 4
    sat_records, sat_children = {0: zero(root)}, []
    for node, choice in enumerate(product((7, 8), (0, 1), (-1, 1)), 1):
        sat_records[node] = zero(P.physical_child(root, 'sat', (7, 8), choice))
        sat_children.append(dict(choice=list(choice), node=node))
    save_tree('complete_HI_SAT_union', sat_records,
              {0: dict(kind='sat', pair=[7, 8], children=sat_children)})
    save_tree('complete_D_angle_union',
        {0: zero(root), 1: zero(P.angle_child(root, 3, 0, 0)), 2: zero(P.angle_child(root, 3, 0, 1))},
        {0: dict(kind='angle', original=3, cut='0', children=[dict(side=0, node=1), dict(side=1, node=2)])})

    rejected = []
    def damage(name, fixture, mutate, record_node=None):
        folder, original_manifest = manifests[fixture]
        manifest = deepcopy(original_manifest)
        if record_node is not None:
            entry = next(entry for entry in manifest['nodes'] if entry['id'] == record_node)
            record = json.loads((folder/entry['file']).read_text())
            mutate(record)
            filename = f'damaged_record_{len(rejected):02d}.json'
            write(folder/filename, record)
            entry.update(file=filename, sha256=sha(folder/filename))
        else:
            mutate(manifest)
        path = folder/f'damaged_manifest_{len(rejected):02d}.json'
        write(path, manifest)
        try:
            T.verify(path, workspace, model)
        except (AssertionError, ValueError, KeyError, IndexError, TypeError):
            rejected.append(name)
        else:
            raise AssertionError('Damaged complete-tree input accepted: '+name)

    damage('omit proxy alternative', 'complete_AB_proxy_union', lambda m: m['nodes'][0]['split']['children'].pop())
    damage('duplicate proxy alternative', 'complete_AB_proxy_union', lambda m: m['nodes'][0]['split']['children'].__setitem__(3, deepcopy(m['nodes'][0]['split']['children'][0])))
    damage('omit SAT alternative', 'complete_HI_SAT_union', lambda m: m['nodes'][0]['split']['children'].pop())
    damage('omit angle half', 'complete_D_angle_union', lambda m: m['nodes'][0]['split']['children'].pop())
    damage('wrong angle cut', 'complete_D_angle_union', lambda m: m['nodes'][0]['split'].__setitem__('cut', '1/4'))
    damage('cycle to root', 'complete_D_angle_union', lambda m: m['nodes'][0]['split']['children'][0].__setitem__('node', 0))
    damage('repeat child domain', 'complete_D_angle_union', lambda m: m['nodes'][0]['split']['children'][1].__setitem__('node', 1))
    damage('invent complete flag', 'fresh_root_open', lambda m: m.__setitem__('complete', True))
    damage('wrong root document hash', 'fresh_root_open', lambda m: m['root_document'].__setitem__('sha256', '0'*64))
    damage('narrowed serialized initial root', 'fresh_root_open', lambda r: r['initial']['angles'].__setitem__(3, ['0', '1']), 0)
    damage('narrowed serialized child initial', 'complete_AB_proxy_union', lambda r: r['initial']['positions'].__setitem__(0, ['-1', '0']), 3)
    damage('erase inherited weighted difference bound', 'proxy_bound_then_complete_angle', lambda r: r['initial'].__setitem__('differences', []), 5)
    damage('changed closed-node multiplier', 'complete_AB_proxy_union', lambda r: r['terminal']['weights'][0].__setitem__(1, r['terminal']['weights'][0][1]+1), 1)
    damage('changed literal row coefficient', 'complete_AB_proxy_union', lambda r: r['terminal']['rows'][0]['coefficients'][0].__setitem__(1, '77'), 1)
    damage('erase strict positive reserve', 'complete_AB_proxy_union', lambda r: r['terminal'].__setitem__('reserve', '0'), 1)
    damage('invent terminal on OPEN domain', 'complete_AB_proxy_union', lambda r: r.__setitem__('status', 'CANDIDATE_CLOSED'), 3)
    # A disconnected extra record cannot silently disappear from accounting.
    folder, manifest = manifests['fresh_root_open']
    original_bytes = (folder/'node_0000.json').read_bytes()
    with (folder/'orphan.json').open('xb') as stream:
        stream.write(original_bytes)
    damage('unreferenced declared node', 'fresh_root_open', lambda m: m['nodes'].append(dict(id=99, file='orphan.json', sha256=sha(folder/'orphan.json'))))
    optimized = subprocess.run([sys.executable, '-B', '-S', '-O', str(Path(T.__file__).resolve()), '--help'],
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    assert optimized.returncode != 0 and 'rejects optimized Python' in optimized.stderr
    rejected.append('optimized Python before import dispatch')
    for name, (folder, manifest) in manifests.items():
        assert sha(folder/'manifest.json') == reports[name]['manifest_sha256']
    report = dict(status='PASS_FRESH_STRICT011_COMPLETE_TREE_CONTROLS',
        scope='Complete-tree attachment and exact conditional fixture; full strict011 remains OPEN',
        fixtures={name:dict(status=r['status'], nodes=r['nodes'], excluded_leaves=r['excluded_leaves'],
                    open_leaves=r['open_leaves'], unions=r['complete_unions'], exact_totals=r['exact_totals'],
                    report_sha256=sha(manifests[name][0]/'EXACT_REPLAY.json')) for name, r in reports.items()},
        damaged_controls_rejected=rejected,
        manually_closed_domain='AB negative-x physical inset alternative; no whole-mask exclusion',
        model_binding_sha256=T.MODEL_BINDING,
        source_sha256={str(path):sha(path) for path in (Path(__file__).resolve(), Path(T.__file__).resolve())},
        no_numeric_solver_called=True, normalized_root_installed=False,
        whole_mask_credit=0, original_cell_credit=0)
    write(output/'COMPLETE_TREE_CONTROLS.json', report)
    print(json.dumps({'status':report['status'], 'fixtures':len(reports), 'damaged_controls':len(rejected),
        'real_exact_proxy_exclusions':1, 'whole_mask_credit':0}))


if __name__ == '__main__':
    main()
