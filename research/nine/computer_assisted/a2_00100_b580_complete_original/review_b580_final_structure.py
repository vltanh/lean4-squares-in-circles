"""Independent complete B580 graph, literal child-state and assembly review.

This does not replay weighted arithmetic and cannot grant original-cell credit.
"""
from pathlib import Path
from hashlib import sha256
from fractions import Fraction as F
from collections import Counter
from itertools import product
from copy import deepcopy
import json

REPO = Path('/workspace/scratch/6b34cccf3741/repo')
W = REPO / 'research/nine/.runs/closure_20261104'
OUT = Path('/workspace/scratch/6b34cccf3741/a_work')
FINAL = W / 'b580_complete_candidate755_v1/manifest.json'
EXPECTED_FINAL = '2f8125fc8107684ef2d31bb64cd82ea8c71a621dd671786355f4906daa28ea1a'
ORIGINAL_ID = 'negative-580db3624cf4c2e2'
ORIGINAL_PATH = [['angle', 3, 0], ['angle_cut', [0, '0'], 0],
                 ['position_cut', [11, '1/2'], 1], ['f_side_escape', [5, 7], [4]]]
bindings = {}


def bind(path, expected=None):
    path = Path(path)
    h = sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    value = h.hexdigest()
    if expected is not None:
        assert value == expected, (path, value, expected)
    bindings[str(path)] = value
    return value


def read(path, expected=None):
    bind(path, expected)
    return json.loads(Path(path).read_text())


def manifest(path, expected=None):
    m = read(path, expected)
    assert m['schema'] == 'B_proxy_first_complete_physical_tree_discovery_v1'
    assert m['completed'] is True
    assert m['original_cells_closed'] == m['masks_closed'] == 0
    return m


def node(path, m, index):
    entry = m['nodes'][index]
    assert entry['index'] == index
    n = read(path.parent / entry['file'], entry['sha256'])
    assert all(n[k] == entry[k] for k in ('index', 'depth', 'status'))
    assert n['record']['initial'] == n['initial']
    return n


def physical_state(state):
    assert state['id'] == ORIGINAL_ID
    assert state['path'][:len(ORIGINAL_PATH)] == ORIGINAL_PATH
    assert len(state['angles']) == 9
    assert len(state['positions']) == 18 and len(state['scalar']) == 36
    pairs = [tuple(row['pair']) for row in state['differences']]
    assert len(pairs) == len(set(pairs))
    assert all(len(pair) == 2 and 0 <= pair[0] < pair[1] < 9 for pair in pairs)


def review_complete_tree(path):
    m = manifest(path, EXPECTED_FINAL)
    thin, leaves, cover_table = [], [], []
    totals = Counter()
    for index in range(len(m['nodes'])):
        n = node(path, m, index)
        record = n['record']
        current = record['initial']
        physical_state(current)
        for step, rr in enumerate(record['rounds']):
            assert rr['before'] == current, ('round before', index, step)
            totals['rounds'] += 1
            totals['deductions'] += len(rr['proposals'])
            totals['premise_rows'] += len(rr['printed_rows'])
            if 'after' in rr:
                current = rr['after']
                physical_state(current)
            else:
                assert step == len(record['rounds']) - 1
                assert record['status'] == 'CANDIDATE_CLOSED'
                current = None
        if record['status'] == 'OPEN':
            assert record['final'] == current
        else:
            assert record['status'] == 'CANDIDATE_CLOSED'
            assert 'final' not in record
            terminal = record['terminal']
            totals['terminal_rows'] += len(terminal.get('rows', []))
            if terminal['kind'] == 'positive_exact_reserve':
                assert F(terminal['reserve']) > 0
                assert record['terminal_state'] == current
        small = {k: n[k] for k in ('index', 'parent', 'depth', 'choice', 'children', 'status', 'initial')}
        small.update(final=record.get('final'), record_status=record['status'],
                     split=n.get('split'), complete_closed_children=n.get('complete_closed_children'))
        thin.append(small)
        if not n['children']:
            assert n['status'] == record['status'] == 'CANDIDATE_CLOSED'
            terminal = record['terminal']
            detail = {k: v for k, v in terminal.items() if k not in (
                'rows', 'weights', 'absolute_variable_bounds', 'weighted_coefficients')}
            leaves.append(dict(index=index, parent=n['parent'], depth=n['depth'], choice=n['choice'],
                               terminal_kind=terminal['kind'], detail=detail,
                               rounds=len(record['rounds']),
                               deductions=sum(len(rr['proposals']) for rr in record['rounds']),
                               node_sha256=m['nodes'][index]['sha256']))
    seen = set()

    def visit(index, parent=None, depth=0):
        assert type(index) is int and 0 <= index < len(thin) and index not in seen
        seen.add(index)
        n = thin[index]
        assert n['parent'] == parent and n['depth'] == depth
        if not n['children']:
            assert n['status'] == 'CANDIDATE_CLOSED'
            return
        assert n['record_status'] == 'OPEN' and n['status'] == 'CANDIDATE_COVER_CLOSED'
        assert n['complete_closed_children'] is True
        split, children = n['split'], n['children']
        kind = split['kind']
        if kind == 'proxy':
            pair = split['pair']
            assert len(pair) == 2 and 0 <= pair[0] < pair[1] < 9
            choices = [list(x) for x in product((0, 1), (-1, 1))]
        elif kind == 'sat':
            pair = split['pair']
            assert len(pair) == 2 and 0 <= pair[0] < pair[1] < 9
            choices = [list(x) for x in product(pair, (0, 1), (-1, 1))]
        else:
            assert kind in ('angle', 'difference')
            choices = [0, 1]
        assert len(children) == len(set(children)) == len(choices)
        for child_index, choice in zip(children, choices):
            child = thin[child_index]
            assert child['choice'] == choice
            expected = deepcopy(n['final'])
            if kind in ('proxy', 'sat'):
                expected['path'].append([kind, split['pair'], choice])
            elif kind == 'angle':
                owner, cut = split['owner'], F(split['cut'])
                assert 0 <= owner < 9
                lo, hi = expected['angles'][owner]
                assert F(lo) < cut < F(hi)
                expected['angles'][owner] = [lo, str(cut)] if choice == 0 else [str(cut), hi]
                expected['path'].append(['angle_cut', [owner, str(cut)], choice])
            else:
                pair, axis, cut = split['pair'], split['axis'], F(split['cut'])
                assert len(pair) == 2 and 0 <= pair[0] < pair[1] < 9 and axis in (0, 1)
                row = next(row for row in expected['differences'] if row['pair'] == pair)
                lo, hi = row['intervals'][axis]
                assert F(lo) < cut < F(hi)
                row['intervals'][axis] = [lo, str(cut)] if choice == 0 else [str(cut), hi]
            assert child['initial'] == expected, ('child state', index, child_index)
            visit(child_index, index, depth + 1)
        cover_table.append(dict(index=index, depth=depth, kind=kind, split=split,
                                children=children, all_closed_faces_retained=True))

    visit(0)
    assert seen == set(range(len(thin)))
    assert m['status'] == thin[0]['status'] == 'CANDIDATE_COVER_CLOSED'
    assert len(thin) == 755 and len(leaves) == 537
    unions = Counter(c['kind'] for c in cover_table)
    assert unions == {'proxy': 96, 'angle': 101, 'sat': 21}
    assert len(thin) == 1 + sum({'proxy': 4, 'angle': 2, 'sat': 8, 'difference': 2}[k] * v for k, v in unions.items())
    return m, thin, leaves, cover_table, totals


assembly_reviews = []
reviewed_assemblies = set()


def review_assembly(path, m):
    if str(path) in reviewed_assemblies or 'same_initial_leaf_assembly' not in m:
        return
    reviewed_assemblies.add(str(path))
    provenance = read(path.parent / 'ASSEMBLY_PROVENANCE.json')
    assert provenance == m['same_initial_leaf_assembly']
    bp = Path(provenance['base'])
    bm = manifest(bp, provenance['base_sha256'])
    assert m['parent'] == bm['parent'] and m['accepted_geometric_sources'] == bm['accepted_geometric_sources']
    count = len(bm['nodes'])
    targets = {change['target'] for change in provenance['changes']}
    assert len(targets) == len(provenance['changes'])
    unchanged_bytes = status_only = 0
    for i in range(count):
        if i in targets:
            continue
        old_entry, new_entry = bm['nodes'][i], m['nodes'][i]
        if old_entry['sha256'] == new_entry['sha256']:
            bind(path.parent / new_entry['file'], new_entry['sha256'])
            bind(bp.parent / old_entry['file'], old_entry['sha256'])
            unchanged_bytes += 1
        else:
            old, new = node(bp, bm, i), node(path, m, i)
            old.pop('status'); new.pop('status')
            assert old == new, ('unchanged sibling', path, i)
            status_only += 1
    next_index = count
    replacements = []
    for change in provenance['changes']:
        target = change['target']
        vp = Path(change['variant'])
        vm = manifest(vp, change['variant_sha256'])
        assert vm['parent'] == bm['parent'] and vm['accepted_geometric_sources'] == bm['accepted_geometric_sources']
        old, replacement = node(bp, bm, target), node(vp, vm, target)
        assert old['record']['status'] == 'OPEN' and not old['children']
        assert old['initial'] == replacement['initial']
        prefix = old['record']['rounds']
        assert replacement['record']['rounds'][:len(prefix)] == prefix
        assert len(prefix) == change['old_rounds_preserved']
        for key in ('parent', 'depth', 'choice'):
            assert old[key] == replacement[key]
        reached, stack, variants = [], [target], {}
        while stack:
            i = stack.pop()
            assert i not in variants
            current = node(vp, vm, i)
            variants[i] = {k: current[k] for k in ('index', 'parent', 'children', 'depth')}
            reached.append(i)
            stack.extend(reversed(current['children']))
        assert len(reached) == change['replacement_nodes']
        mapping = {target: target}
        for i in reached[1:]:
            mapping[i] = next_index
            next_index += 1
        for i in reached:
            original = node(vp, vm, i)
            actual = node(path, m, mapping[i])
            original['index'] = mapping[i]
            original['children'] = [mapping[k] for k in original['children']]
            if i != target:
                original['parent'] = mapping[original['parent']]
            assert original == actual, ('remapped variant', path, i)
        replacements.append(dict(target=target, variant_sha256=bindings[str(vp)],
                                 descendant_count=len(reached), old_rounds_retained=len(prefix)))
        review_assembly(vp, vm)
    assert next_index == len(m['nodes'])
    assert node(path, m, 0)['initial'] == node(bp, bm, 0)['initial']
    assembly_reviews.append(dict(manifest=str(path), manifest_sha256=bindings[str(path)],
                                 base=str(bp), base_sha256=bindings[str(bp)],
                                 unchanged_sibling_bytes=unchanged_bytes,
                                 sibling_candidate_status_only_changes=status_only,
                                 replacements=replacements, all_remapped_records_literal=True))
    review_assembly(bp, bm)


m, thin, leaves, covers, totals = review_complete_tree(FINAL)
review_assembly(FINAL, m)
parent_path = W / 'b_native/b_family_native_discovery_checkpoint_v1/native/whole_B_roots' / (ORIGINAL_ID + '.json')
parent = read(parent_path, 'a9ac5ea57c4a74e39f413fdfe5c8e054453874fe9decdf2d1e9d49c510d27bf3')
assert parent['id'] == ORIGINAL_ID and parent['path'] == ORIGINAL_PATH
assert thin[0]['initial'] == parent['final']
assert m['parent']['sha256'] == bindings[str(parent_path)]
assert Path(m['parent']['path']).resolve() == parent_path.resolve()
pre = read(OUT / 'B580_ORIGINAL_PHYSICAL_PRE_REVIEW.json',
           '5bd202d070c91e3e842c3093bb520f1a82f3dbefd6da7257de1abb96b17c69b9')
assert pre['status'] == 'PASS_B580_ORIGINAL_PHYSICAL_DOMAIN_PRE_REVIEW'
assert pre['original_id'] == ORIGINAL_ID and pre['all_231_definition_tuples_unchanged']
frozen_path = W / 'b_native/b_family_native_discovery_checkpoint_v1/native/b16a_I32_complete_H_checkpoint/ancestry/legacy/current_proof/original_register.json'
frozen = read(frozen_path, 'ea000e84c04675fe22424e5c20d3df9d735d659065349800aef2699170bff604')
current = read(REPO / 'research/nine/gates/A2_00100_FIXED_FRONTIER.json')
fields = ('id', 'sign', 'baseline_frontier_index', 'path')
definitions = lambda x: {cell['id']: {key: cell[key] for key in fields} for cell in x['cells']}
assert len(frozen['cells']) == len(current['cells']) == 231
assert len(definitions(frozen)) == len(definitions(current)) == 231
assert definitions(frozen) == definitions(current)
for name in ('combine_same_initial_leaf_covers_streaming.py', 'graft_complete_b_leaf_streaming.py'):
    path = W / 'drivers' / name
    bind(path, m['sources'][str(path)])
bind(__file__)
result = dict(status='PASS_B580_COMPLETE_STRUCTURE_AND_PHYSICAL_ATTACHMENT_ARITHMETIC_PENDING',
              original_id=ORIGINAL_ID, original_path=ORIGINAL_PATH,
              final_manifest=str(FINAL), final_manifest_sha256=bindings[str(FINAL)],
              nodes=len(thin), terminal_leaves=len(leaves), open_leaves=0,
              complete_unions=dict(Counter(c['kind'] for c in covers)),
              terminal_kinds=dict(Counter(t['terminal_kind'] for t in leaves)),
              totals=dict(totals), assembly_reviews=assembly_reviews,
              all_child_states_independently_reconstructed=True,
              all_round_state_links_checked=True, all_shared_closed_faces_retained=True,
              original_parent_id_path_and_initial_state_identical=True,
              all_231_original_definition_tuples_unchanged=True,
              all_nine_original_labels_and_corners_and_pair_domains_retained=True,
              fixed_H_I_order_preserved=True, H_I_permutation_transport_assumed=False,
              physical_pre_review_sha256=bindings[str(OUT / 'B580_ORIGINAL_PHYSICAL_PRE_REVIEW.json')],
              weighted_arithmetic_replayed_in_this_review=False,
              fresh_native_and_portable_arithmetic_still_required=True,
              new_original_cells=0, new_masks=0, blocking_findings=[], source_sha256=bindings)
(OUT / 'B580_FINAL_STRUCTURAL_REVIEW.json').write_text(json.dumps(result, indent=2) + '\n')
for name, values in [('TERMINAL', leaves), ('COVER', sorted(covers, key=lambda x: x['index']))]:
    (OUT / f'B580_FINAL_COMPLETE_{name}_TABLE.json').write_text(json.dumps(dict(
        status='COMPLETE_STRUCTURAL_TABLE_ARITHMETIC_PENDING', original_id=ORIGINAL_ID,
        manifest_sha256=bindings[str(FINAL)], entries=values), indent=2) + '\n')
print(json.dumps({k: v for k, v in result.items() if k not in ('source_sha256', 'assembly_reviews')}, indent=2), flush=True)
