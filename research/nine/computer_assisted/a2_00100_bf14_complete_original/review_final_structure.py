"""Independent bounded-memory structural review; no row arithmetic credit."""
from pathlib import Path
from copy import deepcopy
from fractions import Fraction as F
from itertools import product
from collections import Counter
import hashlib
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
CLOSED = {'CANDIDATE_CLOSED', 'CANDIDATE_COVER_CLOSED'}
inputs = {}


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read_manifest(path):
    path = Path(path)
    data = path.read_bytes()
    inputs[str(path)] = hashlib.sha256(data).hexdigest()
    manifest = json.loads(data)
    assert manifest['schema'] == 'B_proxy_first_complete_physical_tree_discovery_v1'
    assert manifest['completed'] is True
    assert manifest['original_cells_closed'] == manifest['masks_closed'] == 0
    return manifest


def read_node(manifest_path, entry):
    path = manifest_path.parent / entry['file']
    data = path.read_bytes()
    assert hashlib.sha256(data).hexdigest() == entry['sha256']
    inputs[str(path)] = entry['sha256']
    node = json.loads(data)
    assert all(node[key] == entry[key] for key in ('index', 'status', 'depth'))
    return node


def review_tree(path):
    manifest = read_manifest(path)
    nodes, leaves = [], []
    for index, entry in enumerate(manifest['nodes']):
        assert entry['index'] == index
        node = read_node(path, entry)
        record = node['record']
        assert record['initial'] == node['initial']
        current = record['initial']
        for step, round_ in enumerate(record['rounds']):
            assert round_['before'] == current
            if 'after' in round_:
                current = round_['after']
            else:
                assert step == len(record['rounds']) - 1
                assert record['status'] == 'CANDIDATE_CLOSED'
                current = None
        if record['status'] == 'OPEN':
            assert record['final'] == current
        else:
            assert record['status'] == 'CANDIDATE_CLOSED' and 'final' not in record
            if record['terminal']['kind'] == 'positive_exact_reserve':
                assert F(record['terminal']['reserve']) > 0
                assert record['terminal_state'] == current
        small = {key: node[key] for key in ('index', 'parent', 'depth', 'choice', 'status', 'children', 'initial')}
        small['final'] = record.get('final')
        small['record_status'] = record['status']
        small['split'] = node.get('split')
        small['complete_closed_children'] = node.get('complete_closed_children')
        nodes.append(small)
        if not node['children']:
            assert node['status'] == record['status'] == 'CANDIDATE_CLOSED'
            terminal = record['terminal']
            detail = {key: value for key, value in terminal.items() if key not in (
                'rows', 'weights', 'absolute_variable_bounds', 'weighted_coefficients')}
            leaves.append(dict(index=index, parent=node['parent'], depth=node['depth'],
                               terminal_kind=terminal['kind'], detail=detail,
                               node_file=str(path.parent / entry['file']), node_sha256=entry['sha256'],
                               terminal_literal_sha256=hashlib.sha256(
                                   json.dumps(terminal, sort_keys=True, separators=(',', ':')).encode()).hexdigest()))
    visited, covers = set(), []

    def visit(index, parent=None, depth=0):
        assert type(index) is int and 0 <= index < len(nodes) and index not in visited
        visited.add(index)
        node = nodes[index]
        assert node['parent'] == parent and node['depth'] == depth
        children = node['children']
        if not children:
            assert node['status'] == 'CANDIDATE_CLOSED'
            return
        assert node['record_status'] == 'OPEN' and node['status'] == 'CANDIDATE_COVER_CLOSED'
        assert node['complete_closed_children'] is True
        split = node['split']
        kind = split['kind']
        if kind == 'proxy':
            choices = [list(choice) for choice in product((0, 1), (-1, 1))]
        elif kind == 'sat':
            pair = split['pair']
            assert len(pair) == 2 and 0 <= pair[0] < pair[1] < 9
            choices = [list(choice) for choice in product(pair, (0, 1), (-1, 1))]
        else:
            assert kind in ('angle', 'difference')
            choices = [0, 1]
        assert len(children) == len(set(children)) == len(choices)
        for child_index, choice in zip(children, choices):
            child = nodes[child_index]
            assert child['choice'] == choice
            expected = deepcopy(node['final'])
            if kind in ('proxy', 'sat'):
                expected['path'].append([kind, split['pair'], choice])
            elif kind == 'angle':
                owner, cut = split['owner'], F(split['cut'])
                lo, hi = expected['angles'][owner]
                assert F(lo) < cut < F(hi)
                expected['angles'][owner] = [lo, str(cut)] if choice == 0 else [str(cut), hi]
                expected['path'].append(['angle_cut', [owner, str(cut)], choice])
            else:
                row = next(row for row in expected['differences'] if row['pair'] == split['pair'])
                axis, cut = split['axis'], F(split['cut'])
                lo, hi = row['intervals'][axis]
                assert F(lo) < cut < F(hi)
                row['intervals'][axis] = [lo, str(cut)] if choice == 0 else [str(cut), hi]
            assert child['initial'] == expected, ('child state', index, child_index)
            visit(child_index, index, depth + 1)
        covers.append(dict(index=index, depth=depth, kind=kind, split=split,
                           children=children, all_closed_faces_retained=True))

    visit(0)
    assert visited == set(range(len(nodes)))
    assert manifest['status'] == nodes[0]['status'] == 'CANDIDATE_COVER_CLOSED'
    return manifest, nodes, leaves, covers


conditional_path = ROOT / 'f14_209_all_BF_combined/manifest.json'
cm, cn, cl, cc = review_tree(conditional_path)
conditional_base_path = ROOT / 'f14_209_all_CH_combined/manifest.json'
cbm = read_manifest(conditional_base_path)
assert cm['parent'] == cbm['parent'] and cm['accepted_geometric_sources'] == cbm['accepted_geometric_sources']
for index, entry in enumerate(cbm['nodes']):
    old = read_node(conditional_base_path, entry)
    new = read_node(conditional_path, cm['nodes'][index])
    if index not in (111, 119):
        old.pop('status'); new.pop('status')
        assert old == new, ('changed conditional sibling', index)
    else:
        assert not old['children'] and old['record']['status'] == 'OPEN'
        assert old['initial'] == new['initial']
        prefix = old['record']['rounds']
        assert new['record']['rounds'][:len(prefix)] == prefix
        if len(new['record']['rounds']) > len(prefix):
            assert new['record']['rounds'][len(prefix)]['before'] == old['record']['final']
        assert new['split']['kind'] == 'sat' and new['split']['pair'] == [1, 5]

final_path = ROOT / 'f14_complete_candidate/manifest.json'
fm, fn, fl, fc = review_tree(final_path)
base_path = ROOT / 'f14_domain214_three_round_sweep/manifest.json'
bm = read_manifest(base_path)
assert fm['parent'] == bm['parent'] and fm['accepted_geometric_sources'] == bm['accepted_geometric_sources']
target, base_count = 209, len(bm['nodes'])
assert base_count == 537 and len(cn) == 143 and len(fn) == 679
unchanged_bytes = status_only_changes = 0
for index, entry in enumerate(bm['nodes']):
    if index == target:
        continue
    final_entry = fm['nodes'][index]
    if final_entry['sha256'] == entry['sha256']:
        unchanged_bytes += 1
    else:
        old = read_node(base_path, entry)
        new = read_node(final_path, final_entry)
        old.pop('status'); new.pop('status')
        assert old == new, ('changed original sibling', index)
        status_only_changes += 1
old = read_node(base_path, bm['nodes'][target])
root = read_node(conditional_path, cm['nodes'][0])
replacement = read_node(final_path, fm['nodes'][target])
assert old['record']['final'] == root['initial'] == root['record']['initial']
assert replacement['initial'] == replacement['record']['initial'] == old['initial']
assert replacement['record']['rounds'] == old['record']['rounds'] + root['record']['rounds']
assert fn[0]['initial'] == read_node(base_path, bm['nodes'][0])['initial']
mapping = {0: target, **{i: base_count + i - 1 for i in range(1, len(cn))}}
for index in range(1, len(cn)):
    old = read_node(conditional_path, cm['nodes'][index])
    new = read_node(final_path, fm['nodes'][mapping[index]])
    old['index'] = mapping[index]
    old['parent'] = mapping[old['parent']]
    old['depth'] += replacement['depth']
    old['children'] = [mapping[child] for child in old['children']]
    assert old == new, ('conditional remap', index)

register_path = ROOT.parents[1] / 'gates/A2_00100_FIXED_FRONTIER.json'
register = json.loads(register_path.read_text())
original = next(cell for cell in register['cells'] if cell['id'] == 'negative-f14f5bc4eafdf50d')
assert fn[0]['initial']['id'] == original['id'] and fn[0]['initial']['path'] == original['path']
inputs[str(register_path)] = sha(register_path)
inputs[str(Path(__file__).resolve())] = sha(__file__)
for name in ('drivers/graft_complete_b_leaf_streaming.py', 'drivers/combine_same_initial_leaf_covers.py'):
    inputs[str(ROOT / name)] = sha(ROOT / name)
report = dict(
    status='PASS_FINAL_BF14_STRUCTURE_AND_ATTACHMENT_ARITHMETIC_ACCEPTANCE_PENDING',
    original_id=original['id'], original_path=original['path'],
    final_manifest=str(final_path), final_manifest_sha256=sha(final_path),
    whole_original_root_parent_and_initial_unchanged=True,
    exact_global209_to_conditional_attachment=True,
    target_old_rounds_concatenated_exactly=True,
    base_siblings_byte_identical=unchanged_bytes,
    base_siblings_only_candidate_status_changed=status_only_changes,
    conditional_descendants_remapped_without_other_changes=142,
    conditional_nodes=len(cn), conditional_leaves=len(cl),
    conditional_complete_unions=dict(Counter(cover['kind'] for cover in cc)),
    nodes=len(fn), terminal_leaves=len(fl), open_leaves=0,
    complete_unions=dict(Counter(cover['kind'] for cover in fc)),
    terminal_kinds=dict(Counter(leaf['terminal_kind'] for leaf in fl)),
    all_child_domains_independently_reconstructed=True,
    all_round_state_links_checked=True, closed_split_faces_retained=True,
    literal_weight_arithmetic_checked_here=False,
    final_native_and_portable_arithmetic_replays_still_required=True,
    strict_radius_conclusion_only='q < 1105/256',
    new_original_cells=0, new_masks=0, input_sha256=inputs,
)
(HERE / 'BF14_FINAL_STRUCTURAL_REVIEW.json').write_text(json.dumps(report, indent=2) + '\n')
(HERE / 'BF14_FINAL_COMPLETE_TERMINAL_TABLE.json').write_text(json.dumps(
    dict(status='STRUCTURAL_TABLE_FINAL_EXACT_REPLAY_PENDING', manifest_sha256=sha(final_path),
         original_id=original['id'], leaves=fl), indent=2) + '\n')
(HERE / 'BF14_FINAL_COMPLETE_COVER_TABLE.json').write_text(json.dumps(
    dict(status='STRUCTURAL_TABLE_FINAL_EXACT_REPLAY_PENDING', manifest_sha256=sha(final_path),
         original_id=original['id'], covers=sorted(fc, key=lambda row: row['index'])), indent=2) + '\n')
print(json.dumps({key: report[key] for key in (
    'status', 'nodes', 'terminal_leaves', 'open_leaves', 'complete_unions', 'terminal_kinds',
    'base_siblings_byte_identical', 'base_siblings_only_candidate_status_changed',
    'conditional_descendants_remapped_without_other_changes')}, indent=2), flush=True)
