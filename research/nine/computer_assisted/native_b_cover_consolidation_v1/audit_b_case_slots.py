#!/usr/bin/env python3
"""Check stored B case slots and graph identities; no proof arithmetic."""
from pathlib import Path
from itertools import product
import argparse, hashlib, json

ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('manifest', type=Path)
ap.add_argument('output', type=Path)
a = ap.parse_args()
raw = a.manifest.read_bytes()
manifest = json.loads(raw)
nodes = []
original_id = None
for entry in manifest['nodes']:
    data = (a.manifest.parent/entry['file']).read_bytes()
    assert hashlib.sha256(data).hexdigest() == entry['sha256']
    node = json.loads(data)
    assert node['index'] == entry['index'] == len(nodes)
    assert node['status'] == entry['status'] and node['depth'] == entry['depth']
    assert node['record']['initial'] == node['initial']
    if original_id is None:
        original_id = node['initial']['id']
    assert node['initial']['id'] == original_id
    assert len(node['initial']['angles']) == 9
    assert len(node['initial']['positions']) == 18
    assert len(node['initial']['scalar']) == 36
    record_status = node['record']['status']
    nodes.append({k: node[k] for k in ('index','parent','depth','status','choice','children')})
    nodes[-1]['split'] = node.get('split')
    nodes[-1]['complete_closed_children'] = node.get('complete_closed_children')
    if node['status'] == 'CANDIDATE_CLOSED':
        assert not node['children'] and record_status == 'CANDIDATE_CLOSED'
    else:
        assert record_status == 'OPEN'
    del node, data
seen = set()
unions = dict(proxy=0, sat=0, angle=0, difference=0)
pending = []
closed = ('CANDIDATE_CLOSED','CANDIDATE_COVER_CLOSED')
def visit(index):
    assert index not in seen
    seen.add(index)
    node = nodes[index]
    children = node['children']
    assert len(children) == len(set(children))
    if children:
        assert node['complete_closed_children'] is True
        kind = node['split']['kind']
        unions[kind] += 1
        choices = [nodes[c]['choice'] for c in children]
        if kind in ('angle','difference'):
            assert all(type(c) is int for c in choices)
            assert sorted(choices) == [0,1]
        elif kind == 'proxy':
            assert sorted(map(tuple, choices)) == sorted(product((0,1),(-1,1)))
        else:
            assert kind == 'sat'
            pair = node['split']['pair']
            assert len(pair) == 2 and len(set(pair)) == 2
            assert sorted(map(tuple, choices)) == sorted(product(pair,(0,1),(-1,1)))
        expected = 'CANDIDATE_COVER_CLOSED' if all(nodes[c]['status'] in closed for c in children) else 'OPEN'
        assert node['status'] == expected
    elif node['status'] == 'OPEN':
        pending.append(index)
    for child in children:
        assert nodes[child]['parent'] == index
        assert nodes[child]['depth'] == node['depth'] + 1
        visit(child)
assert nodes[0]['parent'] is None and nodes[0]['depth'] == 0
visit(0)
assert len(seen) == len(nodes)
report = dict(status='PASS_COMPLETE_STORED_CASE_SLOTS_AND_GRAPH_ONLY',
              manifest_sha256=hashlib.sha256(raw).hexdigest(), original_id=original_id,
              nodes=len(nodes), complete_case_unions=unions,
              open_leaf_indices=sorted(pending), open_leaves=len(pending),
              all_nodes_reachable=True, node_and_record_initial_states_identical=True,
              arithmetic_replay=False, original_domain_replay=False,
              new_original_cells=0, new_masks=0,
              checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
a.output.write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps({k: report[k] for k in ('status','nodes','open_leaves','complete_case_unions')}), flush=True)
