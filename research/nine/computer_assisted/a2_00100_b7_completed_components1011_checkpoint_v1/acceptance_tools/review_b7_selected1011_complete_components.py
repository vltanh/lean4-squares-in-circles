"""Bind the two newly complete B7 components to a fresh full exact replay.

This attachment checker does not replace the independent physical row decoder.
It checks literal covers, raw terminal sums, frozen source bytes, and scope.
"""
from pathlib import Path
from fractions import Fraction as F
from copy import deepcopy
from itertools import combinations, product
from datetime import datetime, timezone
import hashlib
import json

W = Path(__file__).resolve().parent.parent
TREE = W / 'b7_selected_negativeF_and_CI_completed1011_v1'
BASE = W / 'b7_input3_fixed26_merged993_v1'
REPORT = W / 'B7_SELECTED_NEGATIVE_F_AND_CI1011_FRESH_REPLAY.json'
ASSEMBLY = W / 'B7_SELECTED_NEGATIVE_F_AND_CI1011_ASSEMBLY_FREEZE.json'
OUTPUT = W / 'B7_SELECTED1011_COMPLETE_COMPONENTS_FINAL_PHYSICAL_REVIEW.json'
TABLE = W / 'B7_SELECTED1011_COMPLETE_COMPONENTS_LITERAL_TERMINAL_TABLE.json'
HAND = W / 'B7_SELECTED1011_COMPLETE_COMPONENTS_PHYSICAL_HAND.md'
ROOT_PATH = [['angle', 3, 0], ['angle_cut', [0, '0'], 0],
             ['position_cut', [11, '1/2'], 0], ['f_side_escape', [5, 7], [2]]]
MANIFEST_SHA = 'bb5aaf7a3d16638b5ed6c7a70c947407c1c470e777468c4d0e0549b16ca6a449'
BASE_SHA = '47932956f4a2ae30fd822ab75edf4658442796c22ad44f6174d99bff58f698c5'
ASSEMBLY_SHA = '3026311fc8371bada0a2e5aeec52d311db4e2612e1f5f15cc5a29c59232443e6'


def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def write_new(path, value):
    with Path(path).open('x') as stream:
        json.dump(value, stream, indent=2)
        stream.write('\n')


def terminal_sum(terminal):
    """Independently reconstruct the literal rational weighted inequality."""
    bounds = list(map(F, terminal['absolute_variable_bounds']))
    assert len(bounds) >= 54 and all(b >= 0 for b in bounds)
    rows = {r['index']: r for r in terminal['rows']}
    assert len(rows) == len(terminal['rows'])
    weights = terminal['weights']
    assert {k for k, _ in weights} == set(rows)
    assert len(weights) == len(rows)
    co, rhs = [F(0)] * len(bounds), F(0)
    for k, numerator in weights:
        assert type(numerator) is int and numerator > 0
        weight = F(numerator, 1 << 40)
        row = rows[k]
        rhs += weight * F(row['rhs'])
        seen = set()
        for j, coefficient in row['coefficients']:
            assert type(j) is int and 0 <= j < len(bounds) and j not in seen
            seen.add(j)
            co[j] += weight * F(coefficient)
    correction = sum(abs(c) * b for c, b in zip(co, bounds))
    reserve = -rhs - correction
    assert reserve > 0 and reserve == F(terminal['reserve'])
    assert co == list(map(F, terminal['weighted_coefficients']))
    assert rhs == F(terminal['weighted_rhs'])
    return dict(positive_reserve=str(reserve), raw_rows=len(rows),
                residual_coefficients=list(map(str, co)),
                residual_bound_correction=str(correction))


def main():
    assert __debug__
    assert digest(TREE / 'manifest.json') == MANIFEST_SHA
    assert digest(BASE / 'manifest.json') == BASE_SHA
    assert digest(ASSEMBLY) == ASSEMBLY_SHA
    report, manifest, base, assembly = map(read, (REPORT, TREE / 'manifest.json',
                                                BASE / 'manifest.json', ASSEMBLY))
    assert report['status'] == 'PASS_PARTIAL_PHYSICAL_TREE'
    assert report['entire_registered_original_domain_retained'] is True
    assert report['all_shared_closed_faces_retained'] is True
    assert report['initial_original_id'] == 'negative-7c60be8b07a358e9'
    assert report['initial_path'] == ROOT_PATH
    assert report['certificate_sha256'] == MANIFEST_SHA
    assert [report[k] for k in ('nodes', 'excluded_leaves', 'open_leaves')] == [1011, 543, 43]
    assert not report['complete'] and not report['whole_original_proved']
    assert report['new_original_ledger_credit'] == report['new_mask_ledger_credit'] == 0
    assert manifest['parent'] == base['parent']
    audits = {a['index']: a for a in report['node_audits']}
    leaves = {a['index']: a for a in report['leaf_table']}
    assert set(audits) == set(range(1011))
    children = {i: [] for i in audits}
    for i, audit in audits.items():
        if audit['parent'] is not None:
            children[audit['parent']].append(i)

    def node(i):
        return read(TREE / manifest['nodes'][i]['file'])

    def descendants(root):
        seen, stack = set(), [root]
        while stack:
            index = stack.pop()
            assert index not in seen
            seen.add(index)
            stack.extend(children[index])
        return seen

    components = {}
    for root, counts in {4: (33, 20), 260: (425, 213), 814: (13, 10),
                         816: (7, 4), 818: (9, 8), 820: (7, 4), 993: (9, 8)}.items():
        indices = descendants(root)
        terminals = indices.intersection(leaves)
        assert (len(indices), len(terminals)) == counts, (root, counts)
        assert all(leaves[i]['excluded'] for i in terminals)
        components[root] = dict(indices=sorted(indices), terminals=sorted(terminals),
                                domains=len(indices), excluded_terminals=len(terminals))

    all_pairs = set(combinations(range(9), 2))
    changed = {}
    for i, entry in enumerate(manifest['nodes']):
        assert entry['index'] == i
        path = TREE / entry['file']
        assert digest(path) == entry['sha256']
        if i < len(base['nodes']):
            old_entry = base['nodes'][i]
            assert old_entry['index'] == i
            old_path = BASE / old_entry['file']
            assert digest(old_path) == old_entry['sha256']
            if entry['sha256'] != old_entry['sha256']:
                old, current = read(old_path), node(i)
                assert old['initial'] == current['initial']
                assert old['record'] == current['record']
                changed[i] = sorted(k for k in set(old) | set(current)
                                    if old.get(k) != current.get(k))
    assert set(changed) == {814, 949, 954, 956}
    assert changed == {814: ['status'], 949: ['children', 'complete_closed_children', 'split'],
                       954: ['status'], 956: ['children', 'complete_closed_children', 'split', 'status']}
    assert manifest['nodes'][952]['sha256'] == base['nodes'][952]['sha256']
    assert not leaves[952]['excluded'] and not leaves[1002]['excluded']

    reviewed = set(components[814]['indices']) | set(components[993]['indices']) | {949, 1002}
    covers = []
    for i in sorted(reviewed):
        current = node(i)
        initial = current['initial']
        assert initial == current['record']['initial']
        assert initial['id'] == report['initial_original_id']
        assert initial['path'][:4] == ROOT_PATH
        assert len(initial['angles']) == 9 and len(initial['positions']) == 18
        assert len(initial['scalar']) == 36
        assert {tuple(d['pair']) for d in initial['differences']} == all_pairs
        assert current['parent'] == audits[i]['parent']
        assert current['depth'] == audits[i]['depth']
        assert set(current['children']) == set(children[i])
        if not children[i]:
            continue
        split, state = current['split'], current['record']['final']
        if split['kind'] == 'position':
            coordinate, at = split['coordinate'], F(split['cut'])
            lo, hi = map(F, state['positions'][coordinate])
            assert lo < at < hi and len(current['children']) == 2
            for side, child in enumerate(current['children']):
                expected = deepcopy(state)
                expected['positions'][coordinate] = list(map(str, (lo, at) if side == 0 else (at, hi)))
                value = node(child)
                assert value['choice'] == side and value['initial'] == expected
            covers.append(dict(parent=i, kind='position', coordinate=coordinate,
                               cut=str(at), children=current['children'], both_closed_faces=True))
        elif split['kind'] == 'sat':
            pair = split['pair']
            expected_choices = set(product(pair, (0, 1), (-1, 1)))
            assert len(current['children']) == 8
            assert {tuple(node(c)['choice']) for c in current['children']} == expected_choices
            for child in current['children']:
                value = node(child)
                expected = deepcopy(state)
                expected['path'] += [['sat', pair, value['choice']]]
                assert value['initial'] == expected
            covers.append(dict(parent=i, kind='sat', original_pair=pair,
                               children=current['children'], all_eight_choices=True))
        else:
            raise AssertionError((i, split))
    assert {(x['parent'], x['kind']) for x in covers} == {
        (814, 'position'), (954, 'position'), (956, 'sat'), (949, 'position'), (993, 'sat')}
    assert node(993)['split']['pair'] == [5, 8]
    assert node(956)['split']['pair'] == [2, 8]

    terminals = []
    for root in (814, 993):
        for i in components[root]['terminals']:
            current, audit, leaf = node(i), audits[i]['audit'], leaves[i]
            assert audit['status'] == 'PASS_EXCLUDED_PHYSICAL_DOMAIN' and leaf['excluded']
            terminal = current['record']['terminal']
            assert terminal['kind'] == leaf['terminal_kind']
            arithmetic = None
            if terminal['kind'] == 'positive_exact_reserve':
                arithmetic = terminal_sum(terminal)
                assert F(arithmetic['positive_reserve']) == F(audit['reserve'])
            elif terminal['kind'] == 'accepted_all_nine_original_F_center_box_exclusion_27_100':
                assert i == 955 and terminal['original'] == 5
                box = [tuple(map(F, ab)) for ab in current['initial']['positions'][10:12]]
                upper = sum(max(lo * lo, hi * hi) for lo, hi in box)
                assert upper == F(149, 2048)
                assert F(729, 10000) - upper == F(187, 1280000) > 0
                assert terminal['accepted_all_nine_arc_hand_sha256'] == 'b0b2858252d2a3bee205d40f97958da445ece0a3a4e05bd693340b2e94884257'
                arithmetic = dict(norm_squared_upper=str(upper), exact_squared_gap='187/1280000')
            terminals.append(dict(component=root, index=i, parent=current['parent'], choice=current['choice'],
                                  payload_sha256=manifest['nodes'][i]['sha256'],
                                  rounds=audit['rounds'], deductions=audit['deductions'],
                                  printed_rows=audit['printed_rows_checked'],
                                  terminal=terminal, literal_arithmetic=arithmetic))
    assert len(terminals) == 18
    pins = {}
    for mapping in (report['source_sha256'], assembly['source_sha256']):
        for path, expected in mapping.items():
            assert digest(path) == expected, path
            if path in pins:
                assert pins[path] == expected
            pins[path] = expected
    for path in (Path(__file__), REPORT, TREE / 'manifest.json', BASE / 'manifest.json', ASSEMBLY):
        pins[str(path)] = digest(path)
    write_new(TABLE, dict(schema='b7-selected1011-literal-terminal-table-v1',
                         original_id=report['initial_original_id'], original_path=ROOT_PATH,
                         components={str(k): components[k] for k in (814, 993)},
                         literal_covers=covers, literal_terminals=terminals,
                         exact_report_sha256=digest(REPORT), whole_original_proved=False,
                         original_credit=0, source_sha256=pins))
    lines = [
        '# B7: complete G/I branch and negative-F half', '',
        'The complete retained cover of original `negative-7c60be8b07a358e9` in mask `001/00` now has 1,011 domains, 543 excluded terminal domains, and 43 OPEN terminal domains. This attachment records two completed components. The original remains OPEN and receives zero additional original-cell or mask credit.', '',
        '## Original physical scope', '',
        'The immutable original path is `' + json.dumps(ROOT_PATH, separators=(',', ':')) + '`. Every domain retains all nine distinct original squares, all 36 corner conditions, all 36 physical pairs, the five cones, actual AB/BC/EF/FG, strictly weak CD, and the original H/I labels. The claim is for q < Q = 1105/256. No global classification at closed Q is asserted.', '',
        '## Component 814: the original G-axis positive G/I branch', '',
        'This component begins at the original H/I proxy [1,-1] and G/I separating-axis choice [G,0,+1]. Two closed cuts on the original F coordinate, y_F = -3/64 and y_F = 3/64, cover it by a lower complement, a central strip, and an upper complement. The lower complement 953 is excluded by its exact terminal. The central box 955 has squared center norm at most 149/2048, below (27/100)^2 by exactly 187/1280000; the accepted all-nine central-capacity theorem excludes that entire closed box.', '',
        'The upper complement 956 has the complete eight-way separating-axis cover for the actual C/I pair [2,8]: either original square supplies axis 0 or 1, with both signs. All eight children 1003–1010 are excluded. Component 814 therefore has 13 domains and 10 excluded terminals, with no OPEN leaf.', '',
        '## Component 993: the negative-F half under 949', '',
        'Within the G/I choice [G,0,-1], the closed cut x_F = 0 at domain 949 retains both halves. The x_F <= 0 half 993 has the complete eight-way separating-axis cover for the actual F/I pair [5,8]. All eight children 994–1001 are excluded. This half has nine domains and eight excluded terminals. Its x_F >= 0 companion 1002 stays OPEN; the other old complement 952 is retained byte-for-byte and also stays OPEN. Whole component 813 remains OPEN.', '',
        '## Literal terminal table', '',
        'The accompanying JSON contains every literal terminal row, positive integer weight, rational residual coefficient, absolute bound, exact reserve, and terminal recipe for the following 18 leaves. These sums are reconstructed independently here; the fresh full-cover checker separately validates every printed row against the unchanged physical decoder. Numerical discovery points and producer closure flags are not premises.', '',
        '| Component | Terminal | Parent | Last choice | Rounds | Deductions | Exact terminal |',
        '|---:|---:|---:|---|---:|---:|---|']
    for row in terminals:
        conclusion = row['terminal']['kind']
        arithmetic = row['literal_arithmetic'] or {}
        if 'positive_reserve' in arithmetic:
            reserve, floor = F(arithmetic['positive_reserve']), F(1)
            while floor > reserve:
                floor /= 2
            conclusion += ' (reserve >= ' + str(floor) + ')'
        lines.append(f"| {row['component']} | {row['index']} | {row['parent']} | {row['choice']} | {row['rounds']} | {row['deductions']} | {conclusion} |")
    lines += ['', '## Preservation, replay, and limits', '',
        'All 993 earlier domain records keep their identical initial state and complete record. Exactly 989 old payloads are byte-identical; the other four differ only in cover edges or propagated candidate status. The already completed components 4, 260, 816, 818, and 820 are retained and independently replayed. All shared closed faces remain covered.', '',
        'Fresh replay checked ' + str(report['local_rounds']) + ' bound rounds, ' + str(report['local_deductions']) + ' deductions, ' + str(report['local_printed_rows']) + ' printed rows, ' + str(report['relative_support_chord_rows_checked']) + ' relative-support chord rows, ' + str(report['central_nine_rows_checked']) + ' all-nine central rows, and ' + str(report['central_F_box_occurrences']) + ' original-F central-box terminal occurrences over the full retained original.', '',
        'Manifest SHA-256: `' + MANIFEST_SHA + '`. Fresh report SHA-256: `' + digest(REPORT) + '`. Literal table SHA-256: `' + digest(TABLE) + '`. The accepted central theorem has SHA-256 `b0b2858252d2a3bee205d40f97958da445ece0a3a4e05bd693340b2e94884257`, with source archive SHA-256 `baf3da1dbcbffdbc9d0a4723bc9ec8db4ef5fc0d62e7d29a455178ac435ce54a`.', '',
        'A portable copied-input replay and independent attachment review remain publication gates. This attachment grants zero original credit. No Lean, Lake, compilation, or CI is used.']
    with HAND.open('x') as stream:
        stream.write('\n'.join(lines) + '\n')
    pins[str(TABLE)], pins[str(HAND)] = digest(TABLE), digest(HAND)
    result = dict(status='PASS_B7_SELECTED1011_TWO_COMPLETE_COMPONENTS_WITH_OPEN_ORIGINAL',
                  recorded_utc=datetime.now(timezone.utc).isoformat(),
                  original_id=report['initial_original_id'], original_path=ROOT_PATH,
                  counts=[1011, 543, 43], completed_components=components,
                  new_complete_components=[814, 993], literal_terminal_count=18,
                  literal_cover_count=len(covers), all993_prior_records_unchanged=True,
                  byte_identical_old_payloads=989, changed_old_payload_fields=changed,
                  all_source_bindings_rehashed=True, source_binding_count=len(pins),
                  old952_unchanged_and_open=True, other_F_half1002_open=True,
                  full_original_open_indices=sorted(i for i, leaf in leaves.items() if not leaf['excluded']),
                  shared_closed_faces_retained=True, original_scope_retained=True,
                  fresh_exact_report_sha256=digest(REPORT), whole_original_proved=False,
                  new_original_cells=0, new_masks=0, ledger_closed=224, ledger_open=7,
                  portable_replay_still_required=True, source_sha256=pins)
    write_new(OUTPUT, result)
    print(json.dumps(dict(status=result['status'], output_sha256=digest(OUTPUT),
                          table_sha256=digest(TABLE), hand_sha256=digest(HAND),
                          literal_terminals=18, source_bindings=len(pins), counts=result['counts']), indent=2))


if __name__ == '__main__':
    main()
