"""Bounded discovery: one complete physical H/I cover per retained B16 leaf.

All arithmetic and coverage conclusions require the unchanged independent
replayer. No numerical status promotes an original cell.
"""
from pathlib import Path
from itertools import product
from copy import deepcopy
import argparse
import hashlib
import json
import os
import sys
import time

WORK = Path('/workspace/scratch/f9f48fcfb253/b_work')
sys.path.insert(0, str(WORK))
import atomic_json_checkpoint_snapshot as ATOMIC
import b_center_exact_moment_runtime_v1 as RT
import b_completed_round_angle_search_explicit as SEARCH
import b_physical_preflight as PREFLIGHT
from run_coupled_sat_cover import restore

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('source', type=Path)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    source = args.source.resolve()
    output = args.output.resolve()
    assert not output.exists()
    manifest = json.loads((source / 'manifest.json').read_text())
    assert manifest['completed'] is True
    for group in ('sources', 'accepted_geometric_sources'):
        for p, digest in manifest[group].items():
            assert sha(p) == digest, p
    output.mkdir()
    (output / 'PREVIOUS_COMPLETE_MANIFEST.json').write_bytes((source / 'manifest.json').read_bytes())
    nodes = []
    for entry in manifest['nodes']:
        p = source / entry['file']
        assert sha(p) == entry['sha256']
        n = json.loads(p.read_text())
        assert n['index'] == len(nodes)
        nodes.append(n)
        os.link(p, output / entry['file'])
    original_count = len(nodes)
    targets = [n['index'] for n in nodes if n['status'] == 'OPEN' and not n['children']]
    assert len(targets) * 8 <= 500
    ctx = RT.Context(WORK / 'b16a_I32_complete_H_checkpoint')
    for n in nodes:
        ctx.AH.add_seed_record(n['record'])
    manifest['sources'].update(RT.source_bindings())
    for p in (Path(__file__).resolve(), Path(SEARCH.__file__).resolve(),
              Path(PREFLIGHT.__file__).resolve(), Path(ATOMIC.__file__).resolve(),
              output / 'PREVIOUS_COMPLETE_MANIFEST.json'):
        manifest['sources'][str(p)] = sha(p)
    manifest['hi_cover_discovery'] = dict(
        original_nodes=original_count, original_open_leaves=targets,
        pair=[7, 8], complete_eight_way_unions=True, bound_rounds=0,
        max_new_nodes=500, numerical_status_is_not_a_proof=True)
    started = time.monotonic()

    def save():
        for n in sorted(nodes, key=lambda n: n['depth'], reverse=True):
            if n['children']:
                n['status'] = ('CANDIDATE_COVER_CLOSED' if all(
                    nodes[k]['status'] != 'OPEN' for k in n['children']) else 'OPEN')
        for n in nodes:
            ATOMIC.write_json(output / f"node_{n['index']:04d}.json", n)
        manifest['nodes'] = [dict(index=n['index'], file=f"node_{n['index']:04d}.json",
            sha256=sha(output / f"node_{n['index']:04d}.json"),
            status=n['status'], depth=n['depth']) for n in nodes]
        manifest.update(status=nodes[0]['status'], seconds=time.monotonic() - started)
        ATOMIC.write_json(output / 'manifest.json', manifest)

    save()
    for index in targets:
        n = nodes[index]
        state = restore(ctx, n['record'])
        assert not any(tuple(pair) == (7, 8) and kind == 'sat'
                       for pair, kind, ch in state['choices'])
        n.update(split=dict(kind='sat', pair=[7, 8],
                            selection='complete_original_extra_square_cover'),
                 children=[], complete_closed_children=True)
        for choice in product((7, 8), (0, 1), (-1, 1)):
            child = ctx.child(state, (7, 8), choice)
            view = RT.E.stateview(child)
            k = len(nodes)
            node = dict(index=k, parent=index, depth=n['depth'] + 1,
                choice=list(choice), initial=deepcopy(view), status='OPEN', children=[],
                record=dict(status='OPEN', initial=deepcopy(view), final=deepcopy(view), rounds=[]))
            nodes.append(node)
            n['children'].append(k)
        # Every sibling is published before any numerical solve.
        save()
        for k in n['children']:
            node = nodes[k]
            child = restore(ctx, node['record'])
            quick = PREFLIGHT.search(ctx, child, ctx.preflight_phase)
            result = quick if quick is not None else SEARCH.search_node(RT.E, ctx, child, 0)[0]
            if result['status'] in ('OPEN', 'CANDIDATE_CLOSED'):
                assert result['initial'] == node['initial']
                node.update(record=result, status=result['status'])
            else:
                ATOMIC.write_json(output / f'no_conclusion_{k:04d}.json', result)
            save()
            print('HI_CHILD', index, k, node['choice'], node['status'],
                  'SECONDS', round(time.monotonic() - started, 2), flush=True)
    for group in ('sources', 'accepted_geometric_sources'):
        for p, digest in manifest[group].items():
            assert sha(p) == digest, p
    print('COMPLETE_HI_DISCOVERY', len(nodes), 'OPEN_LEAVES',
          sum(n['status'] == 'OPEN' and not n['children'] for n in nodes), flush=True)

if __name__ == '__main__':
    assert __debug__
    main()
