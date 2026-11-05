"""Assemble a COMPLETE conditional discovery tree into its whole C cover.

This performs byte binding, exact state equality, and structural case accounting.
It performs no bound/contradiction arithmetic and grants no original-cell credit.
The resulting whole cover still requires the existing fresh original-domain gate.
"""
from pathlib import Path
from itertools import product
from copy import deepcopy
import argparse
import hashlib
import json
import time


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def read_bound(path):
    path = Path(path).resolve()
    for _ in range(8):
        before = path.stat()
        raw = path.read_bytes()
        after = path.stat()
        if (before.st_ino, before.st_size, before.st_mtime_ns) == (
            after.st_ino, after.st_size, after.st_mtime_ns
        ) and len(raw) == after.st_size:
            return json.loads(raw), dict(path=str(path), sha256=sha(raw), bytes=len(raw)), raw
        time.sleep(0.1)
    raise AssertionError('Input changed while reading: ' + str(path))


def node_path(manifest, node):
    return Path(node.get('source_file', manifest.parent / node['file'])).resolve()


def structural(manifest):
    nodes = {n['index']: n for n in manifest['nodes']}
    pending = {n['index']: n for n in manifest['pending']}
    stopped = {n['index']: n for n in manifest['stopped']}
    assert len(nodes) == len(manifest['nodes']) and 0 in nodes
    assert len(pending) == len(manifest['pending']) and not set(nodes) & set(pending)
    assert len(stopped) == len(manifest['stopped']) and set(stopped) <= set(nodes)
    visited, frontier, closed = set(), set(), {}

    def visit(index, parent):
        if index in pending:
            assert index not in frontier and pending[index]['parent'] == parent
            frontier.add(index)
            return False
        assert index in nodes and index not in visited
        n = nodes[index]
        assert n['parent'] == parent and n['file'] == f'node_{index:05}.json'
        assert n['status'] in ('OPEN', 'CANDIDATE_CLOSED', 'CANDIDATE_COVER_CLOSED')
        visited.add(index)
        split = n.get('split')
        if split is None:
            assert n['status'] in ('OPEN', 'CANDIDATE_CLOSED')
            value = n['status'] == 'CANDIDATE_CLOSED'
            assert value != (index in stopped)
        else:
            assert index not in stopped and n['status'] != 'CANDIDATE_CLOSED'
            children = split['children']
            assert len(children) == len(set(children))
            entries = [nodes.get(i, pending.get(i)) for i in children]
            assert all(e is not None for e in entries)
            edges = [e['edge'] for e in entries]
            kind = split['kind']
            assert all(e['kind'] == kind for e in edges)
            if kind in ('proxy', 'sat'):
                pair = tuple(split['pair'])
                assert len(pair) == 2 and 0 <= pair[0] < pair[1] < 9
                expected = set(product((0, 1), (-1, 1))) if kind == 'proxy' else set(product(pair, (0, 1), (-1, 1)))
                choices = [tuple(e['choice']) for e in edges]
                assert len(choices) == len(set(choices)) and set(choices) == expected
                assert all(e['pair'] == list(pair) for e in edges)
            else:
                assert kind == 'angle' and len(children) == 2
                assert sorted(e['choice'] for e in edges) == [0, 1]
                assert all(e['owner'] == split['owner'] and e['cut'] == split['cut'] for e in edges)
            outcomes = [visit(i, index) for i in children]
            value = all(outcomes)
            if n['status'] == 'CANDIDATE_COVER_CLOSED':
                assert value
        closed[index] = value
        return value

    result = visit(0, None)
    assert visited == set(nodes) and frontier == set(pending)
    return nodes, pending, stopped, closed, result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('whole', type=Path)
    parser.add_argument('conditional', type=Path)
    parser.add_argument('index', type=int)
    parser.add_argument('output', type=Path, nargs='?')
    parser.add_argument('--plan', action='store_true')
    args = parser.parse_args()
    whole_path, conditional_path = args.whole.resolve(), args.conditional.resolve()
    whole, whole_binding, _ = read_bound(whole_path)
    conditional, conditional_binding, _ = read_bound(conditional_path)
    assert whole['schema'] == 'whole_c_selective_dfs_continuation_v1'
    assert conditional['schema'] == 'conditional_c_selective_dfs_continuation_v1'
    old, old_pending, old_stopped, _, _ = structural(whole)
    new, new_pending, new_stopped, _, new_closed = structural(conditional)
    index = args.index
    assert index in old and old[index]['status'] == 'OPEN'
    assert index != 0
    first, first_binding, _ = read_bound(node_path(whole_path, old[index]))
    second, second_binding, _ = read_bound(node_path(conditional_path, new[0]))
    assert first['status'] == 'OPEN'
    assert first['final'] == second['initial'] == conditional['original']
    assert whole['original']['id'] == conditional['original']['id']
    assert conditional['original']['path'][:len(whole['original']['path'])] == whole['original']['path']
    assert new[0]['depth'] == old[index]['depth']

    removed, stack = set(), [index]
    while stack:
        current = stack.pop()
        assert current not in removed
        removed.add(current)
        stack.extend(old.get(current, {}).get('split', {}).get('children', []))
    assert removed <= set(old) | set(old_pending)
    binding = dict(
        scope='DISCOVERY_ASSEMBLY_ONLY', whole=whole_binding,
        conditional=conditional_binding, graft_index=index,
        old_root_record=first_binding, conditional_root_record=second_binding,
        state_join='old final == conditional initial == conditional original',
        removed_processed_nodes=len(set(old) & removed),
        removed_pending_cases=len(set(old_pending) & removed),
        retained_external_pending_cases=len(set(old_pending) - removed),
        conditional_processed_nodes=len(new),
        conditional_pending_cases=len(new_pending),
        conditional_stopped_cases=len(new_stopped),
        conditional_candidate_complete=bool(conditional['conditional_candidate_closed'] and new_closed),
        arithmetic_replay_performed=False, new_original_cells=0, new_masks=0,
        assembly_source=dict(path=str(Path(__file__).resolve()), sha256=sha(Path(__file__).read_bytes())),
    )
    if args.plan:
        assert args.output is None
        print(json.dumps(binding, indent=2))
        return

    assert args.output is not None
    assert conditional['conditional_candidate_closed'] and new_closed
    assert not new_pending and not new_stopped
    output = args.output.resolve()
    assert not output.exists()
    output.mkdir(parents=True)
    next_index = max(set(old) | set(old_pending)) + 1
    remap = {0: index}
    for k in sorted(set(new) - {0}):
        remap[k] = next_index
        next_index += 1

    # Copy the new root record, prepending any old certified propagation.
    joined = deepcopy(second)
    joined['initial'] = deepcopy(first['initial'])
    joined['rounds'] = deepcopy(first['rounds']) + deepcopy(second['rounds'])
    joined['seconds'] = first.get('seconds', 0) + second.get('seconds', 0)
    joined_name = f'node_{index:05}.json'
    joined_raw = (json.dumps(joined, indent=2) + '\n').encode()
    (output / joined_name).write_bytes(joined_raw)

    nodes = {}
    for k, n in old.items():
        if k not in removed:
            nodes[k] = dict(deepcopy(n), source_file=str(node_path(whole_path, n)))
    source_records = {}
    for k, n in new.items():
        translated = deepcopy(n)
        j = remap[k]
        translated['index'] = j
        translated['file'] = f'node_{j:05}.json'
        translated['parent'] = old[index]['parent'] if k == 0 else remap[n['parent']]
        if k == 0:
            translated['edge'] = deepcopy(old[index]['edge'])
            translated.pop('source_file', None)
        else:
            path = node_path(conditional_path, n)
            record, record_binding, _ = read_bound(path)
            assert record['initial']['id'] == whole['original']['id']
            source_records[str(path)] = record_binding['sha256']
            translated['source_file'] = str(path)
        if 'split' in translated:
            translated['split']['children'] = [remap[i] for i in translated['split']['children']]
        nodes[j] = translated
    result = deepcopy(whole)
    source_hashes = dict(whole['discovery_source_sha256'])
    for path, digest in conditional['discovery_source_sha256'].items():
        assert path not in source_hashes or source_hashes[path] == digest
        source_hashes[path] = digest
    source_hashes[str(Path(__file__).resolve())] = sha(Path(__file__).read_bytes())
    result.update(
        source_manifest=whole_binding,
        discovery_source_sha256=source_hashes,
        nodes=[nodes[i] for i in sorted(nodes)],
        pending=[deepcopy(p) for p in whole['pending'] if p['index'] not in removed],
        stopped=[deepcopy(p) for p in whole['stopped'] if p['index'] not in removed],
        whole_candidate_closed=False,
        closed_leaves=sum(n['status'] == 'CANDIDATE_CLOSED' for n in nodes.values()),
        seconds=whole.get('seconds', 0) + conditional.get('seconds', 0),
        independent_replay_pending=True, no_original_cell_or_mask_credit=True,
    )
    _, _, _, closure, complete = structural(result)
    for n in result['nodes']:
        if n.get('split') and closure[n['index']]:
            n['status'] = 'CANDIDATE_COVER_CLOSED'
    result['whole_candidate_closed'] = complete
    assert structural(result)[-1] == complete
    binding.update(
        index_map={str(k): v for k, v in remap.items()},
        retained_conditional_records=source_records,
        joined_root=dict(path=str(output / joined_name), sha256=sha(joined_raw)),
        whole_candidate_closed=complete,
    )
    result['complete_conditional_graft'] = binding
    (output / 'GRAFT_BINDING.json').write_text(json.dumps(binding, indent=2) + '\n')
    (output / 'MANIFEST.json').write_text(json.dumps(result, indent=2) + '\n')
    # Input lineage is frozen for the successful assembly.
    for item in (whole_binding, conditional_binding, first_binding, second_binding):
        assert sha(Path(item['path']).read_bytes()) == item['sha256']
    for path, digest in source_records.items():
        assert sha(Path(path).read_bytes()) == digest
    print(json.dumps(dict(status='ASSEMBLED_COMPLETE_CONDITIONAL_DISCOVERY_TREE',
                         output=str(output), nodes=len(result['nodes']),
                         pending=len(result['pending']), stopped=len(result['stopped']),
                         whole_candidate_closed=complete, arithmetic_replay_performed=False,
                         new_original_cells=0, new_masks=0)))


if __name__ == '__main__':
    main()
