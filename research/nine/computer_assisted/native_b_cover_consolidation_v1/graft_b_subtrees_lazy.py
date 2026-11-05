#!/usr/bin/env python3
"""Untrusted B cover assembly with bounded memory and exact state joins.

With --allow-open this preserves partial covers for discovery continuation.
No arithmetic proof or original-cell credit is granted by this assembler.
"""
from pathlib import Path
from copy import deepcopy
import argparse, hashlib, json

CLOSED = ('CANDIDATE_CLOSED', 'CANDIDATE_COVER_CLOSED')
ALLOWED = ('OPEN',) + CLOSED


def sha(path):
    with Path(path).open('rb') as handle:
        return hashlib.file_digest(handle, 'sha256').hexdigest()


def payload(origin):
    raw = origin['path'].read_bytes()
    assert hashlib.sha256(raw).hexdigest() == origin['sha256']
    return json.loads(raw)


def graph(nodes):
    seen = set()
    def visit(index):
        assert index not in seen and 0 <= index < len(nodes)
        seen.add(index)
        node = nodes[index]
        assert node['index'] == index and node['status'] in ALLOWED
        assert len(node['children']) == len(set(node['children']))
        if node['children']:
            assert node['complete_closed_children'] is True
            assert len(node['children']) == {'proxy': 4, 'sat': 8, 'angle': 2,
                                             'difference': 2}[node['split']['kind']]
        for child in node['children']:
            assert nodes[child]['parent'] == index
            assert nodes[child]['depth'] == node['depth'] + 1
            visit(child)
    assert nodes[0]['parent'] is None and nodes[0]['depth'] == 0
    visit(0)
    assert len(seen) == len(nodes)


def read_tree(path):
    path = Path(path).resolve()
    manifest = json.loads(path.read_text())
    assert manifest['completed'] is True
    assert manifest['schema'] == 'B_proxy_first_complete_physical_tree_discovery_v1'
    nodes, origins = [], []
    for entry in manifest['nodes']:
        index = len(nodes)
        assert entry['index'] == index and entry['file'] == f'node_{index:04d}.json'
        origin = dict(path=path.parent/entry['file'], sha256=entry['sha256'])
        node = payload(origin)
        del node['record']
        assert (node['index'], node['status'], node['depth']) == (index, entry['status'], entry['depth'])
        nodes.append(node); origins.append(origin)
    for group in ('sources', 'accepted_geometric_sources'):
        for source, digest in manifest[group].items():
            assert sha(source) == digest, source
    graph(nodes)
    return path, manifest, nodes, origins


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('base', type=Path)
    ap.add_argument('output', type=Path)
    ap.add_argument('grafts', nargs='+', help='old_node_index=/path/to/manifest.json')
    ap.add_argument('--allow-open', action='store_true')
    args = ap.parse_args()
    base, manifest, nodes, origins = read_tree(args.base)
    out = args.output.resolve()
    assert not out.exists()
    original_count = len(nodes)
    old_root_initial = deepcopy(nodes[0]['initial'])
    old_record_initial = payload(origins[0])['record']['initial']
    original_parent = deepcopy(manifest['parent'])
    sources = deepcopy(manifest['sources'])
    geometric = deepcopy(manifest['accepted_geometric_sources'])
    inputs = {str(base): sha(base)}
    removed, replacement_records, grafts = set(), {}, []

    for spec in args.grafts:
        text, raw_path = spec.split('=', 1)
        target = int(text)
        path, incoming, children, child_origins = read_tree(Path(raw_path))
        assert 0 <= target < len(nodes) and target not in removed
        incoming_open = [n['index'] for n in children if not n['children'] and n['status'] == 'OPEN']
        if not args.allow_open:
            assert not incoming_open and children[0]['status'] in CLOSED
        old = nodes[target]
        old_record = replacement_records.get(target)
        if old_record is None:
            old_record = payload(origins[target])['record']
        new_record = payload(child_origins[0])['record']
        assert old_record['status'] == 'OPEN'
        assert old_record['final'] == new_record['initial']
        assert old['initial'] == old_record['initial']
        def discard(index):
            assert index not in removed
            removed.add(index)
            for child in nodes[index]['children']:
                discard(child)
        for child in old['children']:
            discard(child)
        local_map = {0: target}
        for child in children[1:]:
            local_map[child['index']] = len(nodes)
            nodes.append(None); origins.append(None)
        merged = deepcopy(new_record)
        merged['initial'] = deepcopy(old_record['initial'])
        merged['rounds'] = old_record['rounds'] + new_record['rounds']
        merged['continued_completed_rounds'] = len(old_record['rounds'])
        merged['seconds'] = old_record.get('seconds', 0) + new_record.get('seconds', 0)
        replacement_records[target] = merged
        replacement = deepcopy(old)
        replacement['status'] = children[0]['status']
        replacement['children'] = [local_map[c] for c in children[0]['children']]
        for key in ('split', 'complete_closed_children'):
            if key in children[0]:
                replacement[key] = deepcopy(children[0][key])
            else:
                replacement.pop(key, None)
        nodes[target] = replacement
        for child, origin in zip(children[1:], child_origins[1:]):
            updated = deepcopy(child)
            updated['index'] = local_map[child['index']]
            updated['parent'] = local_map[child['parent']]
            updated['depth'] = old['depth'] + child['depth']
            updated['children'] = [local_map[c] for c in child['children']]
            nodes[updated['index']] = updated
            origins[updated['index']] = origin
        for destination, group in ((sources, 'sources'), (geometric, 'accepted_geometric_sources')):
            for source, digest in incoming[group].items():
                assert source not in destination or destination[source] == digest
                destination[source] = digest
        inputs[str(path)] = sha(path)
        grafts.append(dict(old_target=target, source=str(path), source_sha256=sha(path),
                           subtree_nodes=len(children), incoming_open_leaves=len(incoming_open),
                           initial_matches_old_final=True, all_incoming_cases_retained=True))
        del old_record, new_record, children, child_origins

    kept = [i for i in range(len(nodes)) if i not in removed]
    mapping = {old: new for new, old in enumerate(kept)}
    result = []
    for old in kept:
        node = deepcopy(nodes[old])
        node['index'] = mapping[old]
        if node['parent'] is not None:
            node['parent'] = mapping[node['parent']]
        node['children'] = [mapping[c] for c in node['children']]
        result.append(node)
    for node in sorted(result, key=lambda n: n['depth'], reverse=True):
        if node['children']:
            node['status'] = ('CANDIDATE_COVER_CLOSED' if all(
                result[c]['status'] in CLOSED for c in node['children']) else 'OPEN')
    graph(result)
    assert result[0]['initial'] == old_root_initial
    root_record = replacement_records.get(0)
    if root_record is None:
        root_record = payload(origins[0])['record']
    assert root_record['initial'] == old_record_initial
    assert manifest['parent'] == original_parent

    out.mkdir(parents=True)
    entries = []
    for old, node in zip(kept, result):
        record = replacement_records.get(old)
        if record is None:
            record = payload(origins[old])['record']
        path = out/f'node_{node["index"]:04d}.json'
        path.write_text(json.dumps(dict(node, record=record), indent=2)+'\n')
        entries.append(dict(index=node['index'], file=path.name, sha256=sha(path),
                            status=node['status'], depth=node['depth']))
        del record
    sources.update(inputs)
    sources[str(Path(__file__).resolve())] = sha(__file__)
    report = dict(status='ASSEMBLED_NATIVE_DISCOVERY_COVER_ARITHMETIC_REPLAY_REQUIRED',
                  base=str(base), base_sha256=sha(base), grafts=grafts,
                  original_nodes=original_count, removed_descendant_nodes=len(removed),
                  new_nodes=len(result), open_leaves=sum(
                      n['status'] == 'OPEN' and not n['children'] for n in result),
                  all_remaining_pending_domains_retained=True,
                  root_original_parent_unchanged=True, root_initial_state_unchanged=True,
                  all_nodes_reachable=True, bounded_record_memory=True,
                  arithmetic_replay=False, new_original_cells=0, new_masks=0)
    provenance = out/'GRAFT_PROVENANCE.json'
    provenance.write_text(json.dumps(report, indent=2)+'\n')
    sources[str(provenance)] = sha(provenance)
    manifest.pop('continuation', None)
    manifest.pop('deferred_subtree_indices', None)
    manifest.update(nodes=entries, sources=sources, accepted_geometric_sources=geometric,
                    status=result[0]['status'], seconds=0, subtree_assembly=report)
    (out/'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')
    for group in (sources, geometric):
        for source, digest in group.items():
            assert sha(source) == digest
    print(json.dumps(report), flush=True)


if __name__ == '__main__':
    main()
