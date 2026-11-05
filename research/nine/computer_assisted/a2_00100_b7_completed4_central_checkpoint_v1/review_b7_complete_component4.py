"""Bind the complete B7 component4 hand/table attachment to its fresh exact replay."""
from pathlib import Path
from fractions import Fraction as F
from copy import deepcopy
from itertools import combinations
import hashlib
import json

W = Path(__file__).resolve().parent.parent
TREE = W / 'b7_component4_three_survivors_unsplit3_v1'
PURE = W / 'b7_component4_four_central_F_boxes_v1'
REPORT = W / 'b7_component4_complete949_fresh_exact.json'
INNER = {929, 935, 941, 947}
OUTER = {926, 927, 930, 932, 933, 936, 938, 939, 942, 944, 945, 948}
OLD_CLOSED = {821, 824, 825, 828}
ROOT_PATH = [['angle', 3, 0], ['angle_cut', [0, '0'], 0],
             ['position_cut', [11, '1/2'], 0], ['f_side_escape', [5, 7], [2]]]


def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def main():
    assert digest(REPORT) == '059ac26ff956b184bd14afeac50e563263e87793f4f3764fe450f5a3d453965b'
    assert digest(TREE / 'manifest.json') == '9f0f107567f4095644b842f6e787347ac1770495124f653134ea71ce4e2ed108'
    assert digest(PURE / 'manifest.json') == '6ed2023b52bd9f3b05d6a705c69a4d7b10b94f9e2d614c43c95facbee27e3d24'
    report, manifest, pure = read(REPORT), read(TREE / 'manifest.json'), read(PURE / 'manifest.json')
    assert report['status'] == 'PASS_PARTIAL_PHYSICAL_TREE'
    assert report['entire_registered_original_domain_retained'] is True
    assert report['initial_original_id'] == 'negative-7c60be8b07a358e9'
    assert report['initial_path'] == ROOT_PATH
    assert [report[k] for k in ('nodes', 'excluded_leaves', 'open_leaves')] == [949, 505, 41]
    assert report['central_F_box_occurrences'] == 6
    assert not report['complete'] and not report['whole_original_proved']
    assert report['new_original_ledger_credit'] == report['new_mask_ledger_credit'] == 0
    assert manifest['parent'] == pure['parent']
    audits = {a['index']: a for a in report['node_audits']}
    leaves = {a['index']: a for a in report['leaf_table']}
    assert set(audits) == set(range(949))
    children = {i: [] for i in audits}
    for i, audit in audits.items():
        if audit['parent'] is not None:
            children[audit['parent']].append(i)

    def descendants(root):
        seen, stack = set(), [root]
        while stack:
            index = stack.pop()
            assert index not in seen
            seen.add(index)
            stack.extend(children[index])
        return seen

    component = descendants(4)
    component_leaves = component.intersection(leaves)
    assert len(component) == 33
    assert component_leaves == INNER | OUTER | OLD_CLOSED
    assert all(leaves[i]['excluded'] for i in component_leaves)
    component260 = descendants(260)
    assert len(component260) == 425
    assert len(component260.intersection(leaves)) == 213
    assert all(leaves[i]['excluded'] for i in component260.intersection(leaves))
    changed, byte_identical, appended_rounds = [], 0, {}
    for index, entry in enumerate(manifest['nodes']):
        assert entry['index'] == pure['nodes'][index]['index'] == index
        path, old_path = TREE / entry['file'], PURE / pure['nodes'][index]['file']
        assert digest(path) == entry['sha256']
        assert digest(old_path) == pure['nodes'][index]['sha256']
        if entry['sha256'] == pure['nodes'][index]['sha256']:
            byte_identical += 1
        else:
            node, old = read(path), read(old_path)
            changed.append(index)
            for key in set(node) | set(old):
                if key not in ('status', 'record'):
                    assert node.get(key) == old.get(key), (index, key)
            if node['record'] != old['record']:
                assert index in OUTER
                old_rounds = old['record']['rounds']
                assert node['record']['initial'] == old['record']['initial']
                assert node['record']['rounds'][:len(old_rounds)] == old_rounds
                appended_rounds[index] = len(node['record']['rounds']) - len(old_rounds)
            else:
                assert children[index], index
        if index in component:
            node = read(path)
            assert node['initial'] == node['record']['initial']
            state = node['initial']
            assert state['id'] == report['initial_original_id'] and state['path'][:4] == ROOT_PATH
            assert len(state['angles']) == 9 and len(state['positions']) == 18 and len(state['scalar']) == 36
            assert {tuple(d['pair']) for d in state['differences']} == set(combinations(range(9), 2))
            assert node['parent'] == audits[index]['parent']
            assert node['depth'] == audits[index]['depth']
            assert set(node['children']) == set(children[index])
    assert set(appended_rounds) == OUTER
    node4 = read(TREE / manifest['nodes'][4]['file'])
    assert node4['initial']['path'] == ROOT_PATH + [['proxy', [7, 8], [1, 1]]]
    assert node4['split']['kind'] == 'sat' and node4['split']['pair'] == [4, 7]
    expected_sat = {(owner, axis, sign) for owner in (4, 7) for axis in (0, 1) for sign in (-1, 1)}
    assert {tuple(audits[i]['choice']) for i in children[4]} == expected_sat
    position_cuts = []
    for index in sorted(component - component_leaves - {4}):
        node = read(TREE / manifest['nodes'][index]['file'])
        split = node['split']
        assert split['kind'] == 'position'
        coordinate, at = split['coordinate'], F(split['cut'])
        state = node['record']['final']
        lo, hi = map(F, state['positions'][coordinate])
        assert lo < at < hi and len(node['children']) == 2
        for side, child in enumerate(node['children']):
            value = read(TREE / manifest['nodes'][child]['file'])
            expected = deepcopy(state)
            expected['positions'][coordinate] = list(map(str, (lo, at) if side == 0 else (at, hi)))
            assert value['choice'] == side and value['initial'] == expected
        position_cuts.append(dict(parent=index, coordinate=coordinate, cut=str(at), children=node['children']))
    assert len(position_cuts) == 12
    table = []
    for index in sorted(component_leaves):
        node = read(TREE / manifest['nodes'][index]['file'])
        audit, leaf = audits[index]['audit'], leaves[index]
        assert audit['status'] == 'PASS_EXCLUDED_PHYSICAL_DOMAIN'
        if index in INNER:
            box = [tuple(map(F, ab)) for ab in node['initial']['positions'][10:12]]
            upper = sum(max(lo*lo, hi*hi) for lo, hi in box)
            assert upper == F(181, 2500) and F(729, 10000) - upper == F(1, 2000)
            assert leaf['terminal_kind'] == 'accepted_all_nine_original_F_center_box_exclusion_27_100'
        table.append(dict(index=index, parent=node['parent'], choice=node['choice'],
                          rounds=audit['rounds'], deductions=audit['deductions'],
                          printed_rows=audit['printed_rows_checked'],
                          terminal=leaf['terminal_kind'], exact_reserve=audit['reserve']))
    for path, expected in report['source_sha256'].items():
        assert digest(path) == expected
    hand = W / 'B7_COMPLETE_COMPONENT4_PHYSICAL_HAND_ATTACHMENT.md'
    lines = [
        '# B7: complete component 4, with the remaining original domain retained', '',
        'This attachment proves only component 4 of the fixed original `negative-7c60be8b07a358e9` in mask `001/00`. The entire original is still OPEN. The fresh 949-domain cover has 505 excluded terminal domains and 41 OPEN terminal domains; original-cell credit and mask credit are both zero.', '',
        '## Physical scope and complete covers', '',
        'The immutable original path is `' + json.dumps(ROOT_PATH, separators=(',', ':')) + '`. Component 4 adds the original H/I proxy choice `[1,1]`. No original labels are exchanged. Every state retains all nine frames, 36 corner constraints, 36 physical pairs, the five original cones, actual AB/BC/EF/FG and strictly weak CD. The claim remains for q < Q = 1105/256.', '',
        'The first cover in this component is the complete eight-way separating-axis cover for the actual E/H pair [4,7]: either original E or original H supplies axis 0 or 1, with both signs. Four children (821, 824, 825, 828) were already excluded. Each of the other four children (822, 823, 826, 827) is covered by three literal closed position cuts on original F: x_F = 1/5, y_F = -9/50, y_F = 9/50. Both sides of every cut retain the shared face. The 12 two-way unions yield four inner boxes and twelve outer complements. The replay checks the parent-to-child initial states before any later bounds are used.', '',
        '## Inner boxes and outer complements', '',
        'For each inner box, |x_F| <= 1/5 and |y_F| <= 9/50, so |c_F|^2 <= 181/2500 = 729/10000 - 1/2000. The already published all-nine central-capacity hand theorem requires every original center to have norm strictly greater than 27/100, even at the closed radial bound Q. It therefore excludes the entire closed box, including every shared face. The accepted theorem SHA-256 is `b0b2858252d2a3bee205d40f97958da445ece0a3a4e05bd693340b2e94884257`; the published source archive is bound by `baf3da1dbcbffdbc9d0a4723bc9ec8db4ef5fc0d62e7d29a455178ac435ce54a`.', '',
        'All twelve complementary domains are excluded by the unchanged independent rational row decoder and frame/interval terminals. Numerical points and producer statuses are not premises. The table below is derived from the fresh exact report, not the numerical discovery summary.', '',
        '| Terminal | Parent | Last choice | Rounds | Deductions | Printed rows | Exact conclusion |',
        '|---:|---:|---|---:|---:|---:|---|']
    for row in table:
        conclusion = row['terminal']
        if row['exact_reserve'] is not None:
            reserve = F(row['exact_reserve']); assert reserve > 0
            floor = F(1)
            while floor > reserve:
                floor /= 2
            conclusion += ' (reserve >= ' + str(floor) + ')'
        lines.append(f"| {row['index']} | {row['parent']} | {row['choice']} | {row['rounds']} | {row['deductions']} | {row['printed_rows']} | {conclusion} |")
    lines += ['', '## Fresh replay and limits of the conclusion', '',
              'The component has 33 domains and exactly 20 terminal domains, all excluded. The full original cover still has 41 OPEN leaves. The previously completed component 260 remains present with 425 domains and 213 excluded terminals. These are component results, not additional original cells.', '',
              'The final native manifest SHA-256 is `' + digest(TREE / 'manifest.json') + '`. The fresh report SHA-256 is `' + digest(REPORT) + '`. It independently checked 342 bound rounds, 57,118 deductions, 220,172 printed rows, 1,657 relative-support chord rows, 22 all-nine central rows and six literal original-F central-box terminal occurrences over the entire retained original cover. The physical review rechecks all 12 cuts, the full E/H eight-way choices, the unchanged original scope, and every terminal in this component.', '',
              'Publication additionally requires the portable packet to replay from its declared copied inputs, with the historical source aliases mapped to the same frozen bytes. No Lean, Lake or CI run is used for this acceptance.']
    hand.write_text('\n'.join(lines) + '\n')
    result = dict(status='PASS_COMPLETE_B7_COMPONENT4_WITH_OPEN_ORIGINAL_RETAINED',
        original_id=report['initial_original_id'], original_path=ROOT_PATH, component=4,
        component_nodes=33, component_excluded_terminals=20, component_open_terminals=0,
        all_component_indices=sorted(component), terminal_table=table, position_cuts=position_cuts,
        full_original_nodes=949, full_original_excluded_leaves=505, full_original_open_leaves=41,
        pure_cover_payloads_byte_identical=byte_identical, changed_payloads=changed,
        only_twelve_outer_records_extended=True, literal_old_round_prefixes_retained=True,
        appended_outer_rounds=appended_rounds,
        previous_component260_nodes=425, previous_component260_excluded_terminals=213,
        all_original_physical_predicates_and_closed_faces_retained=True,
        fresh_complete_arithmetic_replay_verified=True, all_replay_source_bindings_rehashed=True,
        source_sha256={str(p): digest(p) for p in (Path(__file__), REPORT, TREE / 'manifest.json',
                          PURE / 'manifest.json', hand)},
        whole_original_proved=False, new_original_cells=0, new_masks=0,
        ledger_closed=224, ledger_open=7, portable_replay_still_required=True)
    output = W / 'B7_COMPLETE_COMPONENT4_FINAL_PHYSICAL_REVIEW.json'
    with output.open('x') as stream:
        json.dump(result, stream, indent=2); stream.write('\n')
    print(json.dumps(dict(status=result['status'], report_sha256=digest(output), hand_sha256=digest(hand),
                          component_nodes=33, component_terminals=20, original_open=41,
                          unchanged_payloads=byte_identical, changed_payloads=changed), indent=2))


if __name__ == '__main__':
    assert __debug__
    main()
