#!/usr/bin/env python3
"""Fresh exact three-terminal proof and complete91 composition with old reuse."""
from pathlib import Path
from copy import deepcopy
from fractions import Fraction as F
import argparse
import importlib.util
import json
import sys
import historical_leaf_source as H

LEAVES = (29, 30, 64)
TERMINAL = dict(kind='accepted_effective_angle_terminal',
                label='accepted D/G separator has positive vertical component')


def main():
    if not __debug__:
        raise RuntimeError('Exact terminal replay requires assertions')
    parser = argparse.ArgumentParser()
    parser.add_argument('--packet', type=Path, required=True)
    parser.add_argument('--tree', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args(); packet = args.packet.resolve(); tree = args.tree.resolve()
    output = args.output.resolve(); here = Path(__file__).resolve().parent
    assert not output.exists()
    freeze = H.read(here / 'SOURCE_BINDING.json')
    assert freeze['schema'] == 'C887_three_existing_terminal_sources_v1'
    for name, digest in freeze['files'].items():
        assert H.sha(here / name) == digest
    old_report, old_manifest, entries, old_records, source_inputs = H.validate_historical_proof(packet)
    manifest_path = tree / 'manifest.json'; manifest_sha = H.sha(manifest_path)
    manifest = H.read(manifest_path); expected = deepcopy(old_manifest)
    records = {}; replacements = []
    expected_nodes = {e['index']: e for e in expected['nodes']}
    for index, entry in entries.items():
        p = tree / entry['file']; value = H.read(p)
        if index not in LEAVES:
            assert H.sha(p) == entry['sha256']
            assert p.read_bytes() == (packet / H.TREE_REL / entry['file']).read_bytes()
        else:
            assert entry['parent'] == 27 and entry['depth'] == 12 and entry['children'] == []
            assert old_records[index]['rounds'] == []
            assert old_records[index]['initial'] == old_records[index]['final']
            wanted = deepcopy(old_records[index])
            wanted['status'] = 'CANDIDATE_CLOSED'; wanted['terminal'] = deepcopy(TERMINAL)
            del wanted['final']
            assert value == wanted
            expected_nodes[index]['status'] = 'CANDIDATE_CLOSED'
            expected_nodes[index]['sha256'] = H.sha(p)
            replacements.append(dict(index=index, old_sha256=entry['sha256'], new_sha256=H.sha(p)))
        records[index] = value
    expected['terminal_continuation'] = dict(
        schema='C887_published91_three_existing_terminal_continuation_v1',
        source_manifest_sha256=H.TREE_SHA, source_consumer_report_sha256=H.REPORT_SHA,
        fresh_terminal_leaf_indices=list(LEAVES), replacements=replacements,
        source_binding_sha256=H.sha(here / 'SOURCE_BINDING.json'),
        unchanged_parent_and_sibling_payloads=88, historical_weighted_arithmetic_reused=True,
        whole_original_exclusion_claimed=False, numerical_search_started=False)
    assert manifest == expected
    spec = importlib.util.spec_from_file_location('unchanged_c_terminal_transport', packet / 'replay_portable_c_height_packet_v3.py')
    transport = importlib.util.module_from_spec(spec); spec.loader.exec_module(transport)
    inventory, aliases, locate, output_aliases = transport.install(packet, output)
    import verify_c887_ownerfree_physical_tree as ORIGINAL
    core = ORIGINAL.SAT
    assert H.sha(core.__file__) == H.CORE_SHA
    checker = ORIGINAL.Checker(); adapter = ORIGINAL.Adapter(checker)
    assert adapter.K.V.Q == F(1105, 256)
    assert adapter.K.V.EDGES == ((0, 1, 0), (1, 2, 0), (2, 3, 1), (4, 5, 0), (5, 6, 0))
    covers, _ = H.validate_complete_parent_paths(entries, old_records, adapter, core, ORIGINAL)
    fresh = []; controls = []
    for index in LEAVES:
        initial = H.restore_state(old_records[index]['final'], adapter, core)
        assert initial['id'] == H.TARGET and initial['path'][:len(H.ORIGINAL_PATH)] == H.ORIGINAL_PATH
        choice = entries[index]['restriction']
        assert choice['kind'] == 'physical_sat' and choice['pair'] == [3, 6]
        assert choice['choice'] == {29: [3, 0, 1], 30: [3, 1, -1], 64: [6, 1, -1]}[index]
        assert initial['angles'][3][1] <= 0
        audit, after = core.check_record(records[index], initial, adapter)
        assert after is None and audit['status'] == 'PASS_EXCLUDED_PHYSICAL_DOMAIN'
        assert (audit['rounds'], audit['deductions'], audit['printed_rows_checked']) == (0, 0, 0)
        fresh.append(dict(index=index, exact_audit=audit, terminal=TERMINAL,
            full_path=initial['path'], D_angle=list(map(str, initial['angles'][3])),
            selected_DG_separator=choice['choice'], parent=27, depth=12,
            old_node_sha256=entries[index]['sha256'], new_node_sha256=H.sha(tree / entries[index]['file'])))
        for label, change in (
            ('wrong_original', lambda r: r['initial'].__setitem__('id', 'foreign')),
            ('omitted_parent_restriction', lambda r: r['initial']['path'].pop()),
            ('wrong_terminal_label', lambda r: r['terminal'].__setitem__('label', 'not the accepted label')),
            ('kept_OPEN_status', lambda r: r.__setitem__('status', 'OPEN'))):
            damaged = deepcopy(records[index]); change(damaged)
            try:
                core.check_record(damaged, initial, adapter)
            except (AssertionError, KeyError, ValueError, TypeError):
                controls.append(dict(index=index, rejected=label))
            else:
                raise AssertionError(('malformed terminal accepted', index, label))
    assert len(controls) == 12
    new_nodes = {e['index']: e for e in manifest['nodes']}; visited = set()

    def compose(index):
        assert index not in visited; visited.add(index)
        entry = new_nodes[index]
        if not entry['children']:
            closed = index in LEAVES
            assert entry['status'] == ('CANDIDATE_CLOSED' if closed else 'OPEN')
            return closed
        outcomes = [compose(child) for child in entry['children']]
        closed = all(outcomes)
        assert entry['status'] == ('CANDIDATE_COVER_CLOSED' if closed else 'OPEN')
        return closed

    closed = compose(0)
    assert not closed and visited == set(new_nodes) and manifest['status'] == 'OPEN'
    assert len(covers) == 18
    assert H.sha(manifest_path) == manifest_sha
    for entry in manifest['nodes']:
        assert H.sha(tree / entry['file']) == entry['sha256']
    for relative, digest in inventory.items():
        assert H.sha(packet / relative) == digest
    for relative, digest in freeze['files'].items():
        assert H.sha(here / relative) == digest
    assert not any(name in sys.modules for name in ('numpy', 'scipy', 'highspy',
        'physical_sat_engine_snapshot', 'physical_sat_diagonal_engine', 'ac_physical_context'))
    result = dict(status='PASS_COMPLETE_C887_COVER_WITH_THREE_FRESH_EXISTING_TERMINALS',
        original_id=H.TARGET, original_path=H.ORIGINAL_PATH, mask='001/00', squared_radius='1105/256',
        source_binding_sha256=H.sha(here / 'SOURCE_BINDING.json'), new_manifest_sha256=manifest_sha,
        accepted_old_complete_consumer_report_sha256=H.REPORT_SHA,
        accepted_old_complete_manifest_sha256=H.TREE_SHA, old_packet_manifest_sha256=H.PACKET_MANIFEST_SHA,
        historical_input_identities_rehashed=source_inputs,
        historical_57_round_bound_arithmetic_reused_not_repeated=True,
        unchanged_payloads_byte_verified=88, all_nodes=91, complete_parent_paths_checked=91,
        complete_proxy_covers=9, complete_sat_covers=6, complete_closed_angle_covers=3,
        retained_leaf_domains=73, excluded_leaf_domains=3, open_leaf_domains=70,
        fresh_terminal_leaf_indices=list(LEAVES), fresh_terminal_audits=fresh,
        complete_retained_cover_audits=covers, damaged_terminal_controls_rejected=controls,
        unchanged_independent_arithmetic_core_sha256=H.CORE_SHA,
        all_nine_originals_retained=True, original_corners=36, original_pairs=36, marked_cones=5,
        strict_weak_CD_retained=True, closed_shared_faces_retained=True,
        original_still_open=True, whole_original_exclusion_claimed=False,
        numerical_solver_called=False, new_mathematical_row_families=0,
        new_original_cells=0, new_masks=0, lean_lake_ci_run=False)
    destination = output / 'EXACT_REPLAY.json'
    destination.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(dict(status=result['status'], report_sha256=H.sha(destination),
        nodes=91, fresh_excluded_leaves=3, remaining_open_leaves=70,
        old_bound_arithmetic_repeated=False, numerical_solver_called=False)), flush=True)


if __name__ == '__main__':
    main()
