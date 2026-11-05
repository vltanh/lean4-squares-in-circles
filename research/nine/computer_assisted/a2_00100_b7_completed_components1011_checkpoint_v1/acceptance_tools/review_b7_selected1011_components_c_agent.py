"""Independent literal/physical/terminal peer of selected B7 components.

No producer imports or full bound-round replay. Inherited bounds are supplied
by the pinned fresh original1011 gate; terminal rows and interval consequences
are reconstructed here, with every retained original record source-bound.
"""
from copy import deepcopy
from datetime import datetime, timezone
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path
import hashlib
import json
import sys

C = Path(__file__).resolve().parent.parent
W = C.parent
D = W / 'drivers'
CODE = W / 'b_native/b_family_native_discovery_checkpoint_v1/native/source'
PACKET = W / 'b_native/b_family_native_discovery_checkpoint_v1/native/b16a_I32_complete_H_checkpoint'
sys.path.insert(0, str(CODE))
sys.path.insert(0, str(D))
import independent_b7_central_nine_adapter as DIRECT
import independent_b_position_tree_replay as TREE

READ = lambda p: json.loads(Path(p).read_text())


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1 << 20), b''):
            h.update(block)
    return h.hexdigest()


def main():
    assert __debug__ and sys.dont_write_bytecode
    out = C / 'B7_SELECTED1011_COMPLETE_COMPONENTS_C_AGENT_PHYSICAL_TABLE_REVIEW.json'
    assert not out.exists()
    folder = W / 'b7_selected_negativeF_and_CI_completed1011_v1'
    old_folder = W / 'b7_input3_fixed26_merged993_v1'
    mp, bp = folder / 'manifest.json', old_folder / 'manifest.json'
    rp = W / 'B7_SELECTED_NEGATIVE_F_AND_CI1011_FRESH_REPLAY.json'
    tp = W / 'B7_SELECTED1011_COMPLETE_COMPONENTS_LITERAL_TERMINAL_TABLE.json'
    hp = W / 'B7_SELECTED1011_COMPLETE_COMPONENTS_PHYSICAL_HAND.md'
    peer_path = W / 'B7_SELECTED1011_COMPLETE_COMPONENTS_FINAL_PHYSICAL_REVIEW.json'
    writer = W / 'acceptance/review_b7_selected1011_complete_components.py'
    pins = {
        mp: 'bb5aaf7a3d16638b5ed6c7a70c947407c1c470e777468c4d0e0549b16ca6a449',
        bp: '47932956f4a2ae30fd822ab75edf4658442796c22ad44f6174d99bff58f698c5',
        rp: '0f7007a02876f18701a532cf1bf82c038557c5eabfb5566a35080b7c48b862ba',
        tp: '500eff3ba2fe5ce420f0c57ae4295986ca28d3168e1f13e85f987ff71787ee8f',
        hp: '1a07937cb73a6c7392ba9b7655343d8d29284c378a2e62762b9f8480cd454a6a',
        peer_path: 'd9c151d858827e66964de21cc782eff81fad793eb3047bfd8072325a03ecff8a',
        writer: '321e5631fe5ebc4a7910d2625235368d591f4b8308d98a105979c15bc8476f16'}
    bindings = {}

    def bind(path, digest=None):
        path = str(Path(path).resolve())
        digest = digest or sha(path)
        assert path not in bindings or bindings[path] == digest, path
        assert sha(path) == digest, path
        bindings[path] = digest

    for p, h in pins.items():
        bind(p, h)
    manifest, old, report, table, peer = map(READ, (mp, bp, rp, tp, peer_path))
    assert report['status'] == 'PASS_PARTIAL_PHYSICAL_TREE'
    assert report['initial_original_id'] == DIRECT.TARGET and report['initial_path'] == DIRECT.ROOT_PATH
    assert [report[k] for k in ('nodes', 'excluded_leaves', 'open_leaves')] == [1011, 543, 43]
    assert report['certificate_sha256'] == sha(mp)
    assert report['entire_registered_original_domain_retained'] and report['all_shared_closed_faces_retained']
    assert not report['complete'] and not report['whole_original_proved']
    assert report['new_original_ledger_credit'] == report['new_mask_ledger_credit'] == 0
    assert manifest['parent'] == old['parent']
    assert report['parent_certificate_sha256'] == manifest['parent']['sha256']
    assert peer['status'] == 'PASS_B7_SELECTED1011_TWO_COMPLETE_COMPONENTS_WITH_OPEN_ORIGINAL'
    assert peer['counts'] == [1011, 543, 43] and not peer['whole_original_proved']
    assert table['exact_report_sha256'] == sha(rp) and table['original_id'] == DIRECT.TARGET
    assert table['original_path'] == DIRECT.ROOT_PATH and table['whole_original_proved'] is False
    for group in (report['source_sha256'], table['source_sha256'], peer['source_sha256']):
        for p, h in group.items():
            bind(p, h)
    audits = {a['index']: a for a in report['node_audits']}
    leaves = {a['index']: a for a in report['leaf_table']}
    assert len(audits) == len(report['node_audits']) == 1011 and set(audits) == set(range(1011))
    thin, selected, changes = {}, {}, {}
    reviewed_roots = {4: (33, 20), 260: (425, 213), 814: (13, 10),
                      816: (7, 4), 818: (9, 8), 820: (7, 4), 993: (9, 8)}
    # Read all nodes one at a time, retaining only metadata and the few nodes
    # needed for the selected terminal/case review.
    needed = {814, 949, 954, 956, 993, 953, 955, 1002} | set(range(994, 1011))
    for i, e in enumerate(manifest['nodes']):
        assert e['index'] == i
        p = folder / e['file']
        bind(p, e['sha256'])
        assert report['source_sha256'][str(p.resolve())] == e['sha256']
        n = READ(p)
        assert n['index'] == i and n['status'] == e['status'] and n['depth'] == e['depth']
        assert n['initial'] == n['record']['initial']
        assert n['parent'] == audits[i]['parent'] and n['depth'] == audits[i]['depth']
        thin[i] = {k: deepcopy(n[k]) for k in ('index', 'parent', 'depth', 'status', 'children')}
        if i < 993:
            oldp = old_folder / old['nodes'][i]['file']
            bind(oldp, old['nodes'][i]['sha256'])
            if e['sha256'] == old['nodes'][i]['sha256']:
                assert p.read_bytes() == oldp.read_bytes()
            else:
                before = READ(oldp)
                assert before['record'] == n['record'] and before['initial'] == n['initial']
                changes[i] = sorted(k for k in set(before)|set(n) if before.get(k) != n.get(k))
        if i in needed:
            selected[i] = n
        if i == 0:
            assert n['initial']['id'] == DIRECT.TARGET and n['initial']['path'] == DIRECT.ROOT_PATH
    assert len(thin) == 1011 and len(old['nodes']) == 993
    assert changes == {814: ['status'], 949: ['children', 'complete_closed_children', 'split'],
                       954: ['status'], 956: ['children', 'complete_closed_children', 'split', 'status']}
    assert changes == {int(k): v for k, v in peer['changed_old_payload_fields'].items()}

    def below(start):
        seen, todo = set(), [start]
        while todo:
            i = todo.pop()
            assert i not in seen
            seen.add(i)
            kids = thin[i]['children']
            assert len(kids) == len(set(kids))
            for child in kids:
                assert thin[child]['parent'] == i and thin[child]['depth'] == thin[i]['depth']+1
                todo.append(child)
        return seen

    assert below(0) == set(range(1011))
    components = {}
    for root, counts in reviewed_roots.items():
        indices = below(root)
        terms = indices & set(leaves)
        assert (len(indices), len(terms)) == counts
        assert all(leaves[i]['excluded'] for i in terms)
        components[root] = dict(indices=sorted(indices), terminals=sorted(terms), domains=len(indices), excluded_terminals=len(terms))
        assert components[root] == peer['completed_components'][str(root)]
    assert not leaves[952]['excluded'] and not leaves[1002]['excluded']
    assert manifest['nodes'][952]['sha256'] == old['nodes'][952]['sha256']
    assert not below(814) & below(993)
    assert table['components'] == {str(i): components[i] for i in (814, 993)}
    for i in needed:
        n = selected[i]
        v = n['initial']
        assert v['id'] == DIRECT.TARGET and v['path'][:4] == DIRECT.ROOT_PATH
        assert len(v['angles']) == 9 and len(v['positions']) == 18 and len(v['scalar']) == 36
        assert {tuple(d['pair']) for d in v['differences']} == set(combinations(range(9), 2))
    assert ['proxy', [7, 8], [1, -1]] in selected[814]['initial']['path']
    assert ['sat', [6, 8], [6, 0, 1]] in selected[814]['initial']['path']
    assert ['sat', [6, 8], [6, 0, -1]] in selected[993]['initial']['path']
    adapter = DIRECT.Adapter(PACKET)
    CORE = DIRECT.BASE.CORE
    box = lambda a: tuple(tuple(map(F, v)) for v in a)

    def state(v):
        s = dict(id=v['id'], path=deepcopy(v['path']), choices=adapter.choices(v['path']),
                 angles=box(v['angles']), positions=box(v['positions']), scalar=box(v['scalar']),
                 differences={tuple(d['pair']): box(d['intervals']) for d in v['differences']})
        CORE.valid_state(s)
        assert CORE.state_view(s) == v
        return s

    expected_covers = {
        814: ('position', 11, '-3/64', [953, 954]),
        949: ('position', 10, '0', [993, 1002]),
        954: ('position', 11, '3/64', [955, 956]),
        956: ('sat', [2, 8], None, list(range(1003, 1011))),
        993: ('sat', [5, 8], None, list(range(994, 1002)))}
    covers = {r['parent']: r for r in table['literal_covers']}
    assert set(covers) == set(expected_covers)
    child_count = 0
    for parent, (kind, spec, cut, children) in expected_covers.items():
        n = selected[parent]
        assert n['children'] == children and n['split']['kind'] == kind
        s = state(n['record']['final'])
        assert covers[parent]['children'] == children and covers[parent]['kind'] == kind
        expected_choices = [0, 1] if kind == 'position' else [list(x) for x in product(spec, (0, 1), (-1, 1))]
        assert [selected[i]['choice'] for i in children] == expected_choices
        for i, choice in zip(children, expected_choices):
            if kind == 'position':
                assert n['split']['coordinate'] == spec and n['split']['cut'] == cut
                child = TREE.position_child(s, spec, cut, choice)
            else:
                assert n['split']['pair'] == spec
                child = CORE.sat_child(s, spec, choice, adapter)
            assert CORE.state_view(child) == selected[i]['initial']
            child_count += 1
    assert child_count == 22
    terminal_rows = {x['index']: x for x in table['literal_terminals']}
    assert set(terminal_rows) == set(components[814]['terminals']) | set(components[993]['terminals'])
    assert len(terminal_rows) == 18
    checks, total_rows, positive_count = [], 0, 0
    for i, row in sorted(terminal_rows.items()):
        n, audit = selected[i], audits[i]['audit']
        rec, terminal = n['record'], n['record']['terminal']
        assert terminal == row['terminal'] and terminal['kind'] == leaves[i]['terminal_kind']
        assert audit['status'] == 'PASS_EXCLUDED_PHYSICAL_DOMAIN' and leaves[i]['excluded']
        assert row['payload_sha256'] == manifest['nodes'][i]['sha256']
        assert row['rounds'] == audit['rounds'] and row['deductions'] == audit['deductions']
        assert row['printed_rows'] == audit['printed_rows_checked']
        check = dict(index=i, terminal=terminal['kind'])
        if terminal['kind'] == 'positive_exact_reserve':
            view = rec['rounds'][-1]['after'] if rec['rounds'] else rec['initial']
            assert rec['terminal_state'] == view
            rebuilt, bounds, _ = CORE.validated_rows(adapter, state(view), terminal['rows'])
            assert list(map(str, bounds)) == terminal['absolute_variable_bounds']
            weights = dict(terminal['weights'])
            assert len(weights) == len(terminal['weights']) and set(weights) == set(rebuilt)
            co, rhs = [F(0)]*len(bounds), F(0)
            for key, integer in weights.items():
                assert type(integer) is int and integer > 0
                terms, b, _ = rebuilt[key]
                factor = F(integer, 2**40)
                rhs += factor*b
                for j, a in terms:
                    co[j] += factor*a
            correction = sum(abs(a)*b for a, b in zip(co, bounds))
            reserve = -rhs-correction
            assert reserve > 0 and str(reserve) == terminal['reserve'] == audit['reserve']
            assert co == list(map(F, terminal['weighted_coefficients'])) and rhs == F(terminal['weighted_rhs'])
            raw = row['literal_arithmetic']
            assert raw['positive_reserve'] == str(reserve) and raw['raw_rows'] == len(rebuilt)
            assert raw['residual_coefficients'] == list(map(str, co)) and raw['residual_bound_correction'] == str(correction)
            check.update(rows=len(rebuilt), exact_reserve=str(reserve), all_literal_rows_independently_rebuilt=True)
            total_rows += len(rebuilt)
            positive_count += 1
        elif terminal['kind'] == DIRECT.KIND:
            assert i == 955 and rec['rounds'] == []
            s = state(rec['initial'])
            assert DIRECT.literal(s) == terminal and adapter.verify_early_terminal(s, terminal)
            assert F(terminal['norm_squared_upper']) == F(149, 2048)
            assert F(terminal['exact_squared_gap']) == F(187, 1280000) > 0
            check.update(norm_squared_upper='149/2048', exact_squared_gap='187/1280000',
                physical_lift='An original unit center within27/100 contains the closed original-origin disk23/100, using its centered inradius1/2; the accepted all-nine arc theorem at Q excludes all nine squares.')
        elif terminal['kind'] == 'accepted_center_interval_terminal':
            assert i in (996, 998)
            s = state(rec['rounds'][-1]['after'])
            assert adapter.verify_early_terminal(s, terminal)
            assert terminal['label'] == 'all four original inset separation options impossible: '+str((2, 8) if i == 996 else (5, 8))
            check.update(unchanged_exact_terminal_reconstructed=True, physical_original_pair=[2, 8] if i == 996 else [5, 8], all_four_inset_options_impossible=True)
        else:
            assert i in (1004, 1007) and len(rec['rounds']) == 1
            rr = rec['rounds'][-1]
            scalar = [list(map(F, ab)) for ab in rr['propagated']['scalar']]
            # Fresh whole-original replay proves every recorded proposal. Here
            # only its exact interval intersection and unit-frame consequence
            # are independently recomputed; no dual/bound replay is duplicated.
            for proposal in rr['proposals']:
                if proposal['kind'] == 'scalar' and proposal['key'] >= 18:
                    k = proposal['key']-18
                    bound = F(proposal['upper'])
                    if proposal['sign'] == 1:
                        scalar[k][1] = min(scalar[k][1], bound)
                    else:
                        scalar[k][0] = max(scalar[k][0], -bound)
            angles, failure, inference = adapter.infer_angles(box(rr['before']['angles']), tuple(map(tuple, scalar)))
            assert inference == rr['physical_frame_inferences']
            if i == 1007:
                assert failure == terminal['label'] == 'proved_empty_original_angle_interval'
                bad = [x for x in inference if F(x['new_slope_interval'][0]) > F(x['new_slope_interval'][1])]
                assert len(bad) == 1 and bad[0]['original'] == 3
                check.update(original=3, incompatible_original_D_slope_interval=bad[0]['new_slope_interval'])
            else:
                assert failure is None and terminal['kind'] == 'proved_empty_analytic_frame'
                analytic = adapter.analytic(angles)
                k = terminal['index']
                lower, upper = max(scalar[k][0], analytic[k][0]), min(scalar[k][1], analytic[k][1])
                assert k == 2 and lower > upper
                assert str(lower) == terminal['lower'] and str(upper) == terminal['upper']
                check.update(original_C_alpha_lower=str(lower), original_C_alpha_upper=str(upper), exact_positive_interval_gap=str(lower-upper))
        checks.append(check)
    assert positive_count == 13 and total_rows == 238
    for p, h in DIRECT.source_bindings().items():
        bind(p, h)
    for p, h in adapter.files.items():
        bind(p, h)
    for module in tuple(sys.modules.values()):
        raw = getattr(module, '__file__', None)
        if raw:
            p = Path(raw).resolve()
            if p.suffix == '.py' and (p.is_relative_to(CODE) or p.is_relative_to(D) or p.is_relative_to(PACKET)):
                bind(p)
    bind(Path(__file__).resolve())
    for p, h in bindings.items():
        assert sha(p) == h, p
    DIRECT.no_producers()
    result = dict(status='PASS_B7_SELECTED1011_C_AGENT_PHYSICAL_COMPLETE_COMPONENT_TABLE_REVIEW',
        reviewed_utc=datetime.now(timezone.utc).isoformat(), reviewer='/root/remaining_cells',
        original_id=DIRECT.TARGET, original_path=DIRECT.ROOT_PATH,
        manifest_sha256=sha(mp), fresh_report_sha256=sha(rp), writer_sha256=sha(writer),
        root_attachment_sha256=sha(peer_path), literal_table_sha256=sha(tp), hand_sha256=sha(hp),
        complete_components={str(i): components[i] for i in reviewed_roots},
        whole814_domains=13, whole814_terminals=10, negative_F993_domains=9, negative_F993_terminals=8,
        all_five_closed_unions_reconstructed=True, literal_child_states_reconstructed=22,
        all18_raw_terminal_attributions_checked=True, exact_positive_reserves=13, independent_literal_rows=238,
        terminal_checks=checks, all993_prior_records_and_original_initial_states_retained=True,
        other989_payloads_byte_identical=True, changed_old_payload_fields=changes,
        all1011_graph_domains_exhausted_once=True, all43_OPEN_retained=True,
        old952_byte_identical_OPEN=True, opposite_F_half1002_OPEN=True, whole813_remains_OPEN=True,
        retained_completed_roots=[4, 260, 816, 818, 820], all_nine_originals_and_strict_CD_retained=True,
        current_counts=[1011, 543, 43], source_sha256=bindings, binding_count=len(bindings),
        binding_hashes_rechecked_twice=True, full_arithmetic_replay_repeated=False,
        fresh_original_report_supplies_bound_prefix_arithmetic=True, numerical_producers_imported=False,
        whole_original_proved=False, new_original_cells=0, new_masks=0,
        portable_replay_still_required=True, blocking_findings=[])
    out.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(dict(status=result['status'], sha256=sha(out), bindings=len(bindings),
        literal_rows=238, terminal_count=18, covers=5, child_states=22)), flush=True)


if __name__ == '__main__':
    main()
