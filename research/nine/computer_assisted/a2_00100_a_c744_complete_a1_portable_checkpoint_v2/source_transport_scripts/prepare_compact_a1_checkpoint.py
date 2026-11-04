#!/usr/bin/env python3
"""Plan an immutable complete-A1 delta against the published OPEN A packet.

Saved reports identify inputs and provide expected counts. The new portable
entry point freshly repeats the source proof through the actual A3 consumer.
No report is substituted for that arithmetic replay.
"""
from pathlib import Path
import argparse, hashlib, json

HERE = Path(__file__).resolve().parent
WORKSPACE = HERE.parent.parent
BASE = HERE.parent / 'portable_A_prototype/packet'
BASE_MANIFEST_SHA = '6b730ae5e0dabed264d7e71ba6de72bc15f744d7bba619ed8f6c27a86b9097cf'
TARGET = 'positive-c744bc031d40ee64'
ORIGINAL_PATH = [['angle', 3, 1], ['angle_cut', [0, '0'], 0], ['inward_row_escape', [7, 8], [4]]]
REFERENCE = HERE.parent / 'compact_A1_publication/reference_ec6b94cb/REFERENCE_BINDING.json'
REFERENCE_SHA = '53d8dcb0396ffc6ef128de5048f779bb559b5de25b2c0d2e133f176f96604bb4'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--actual-report', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    assert not output.exists()
    assert sha(BASE / 'INPUT_MANIFEST.json') == BASE_MANIFEST_SHA
    base_inventory = json.loads((BASE / 'INPUT_MANIFEST.json').read_text())['files']
    base_bindings = json.loads((BASE / 'BINDINGS.json').read_text())['files']
    reused, new, reasons, pending, scanned = {}, {}, {}, [], set()
    by_hash = {}
    for original, entry in base_bindings.items():
        assert entry['sha256'] == base_inventory[entry['path']]
        assert sha(BASE / entry['path']) == entry['sha256']
        reused[original] = dict(member=entry['path'], sha256=entry['sha256'])
        by_hash.setdefault(entry['sha256'], entry['path'])

    def bind(path, expected=None, reason='exact checker input', scan=False):
        path = Path(path).resolve()
        assert path.is_relative_to(WORKSPACE), ('unmapped external input', str(path))
        digest = sha(path)
        assert expected is None or digest == expected, ('changed input', str(path), expected, digest)
        key = str(path)
        reasons.setdefault(key, set()).add(reason)
        if key in reused:
            assert reused[key]['sha256'] == digest, ('conflicting published alias', key)
        elif key in new:
            assert new[key]['sha256'] == digest
        elif digest in by_hash:
            reused[key] = dict(member=by_hash[digest], sha256=digest)
        else:
            new[key] = dict(sha256=digest, bytes=path.stat().st_size)
        if scan and path.suffix == '.json' and path not in scanned:
            pending.append(path)
        return dict(path=key, sha256=digest)

    def hash_map(mapping, reason):
        if not isinstance(mapping, dict):
            return
        for path, digest in mapping.items():
            if isinstance(path, str) and path.startswith(str(WORKSPACE) + '/'):
                assert isinstance(digest, str) and len(digest) == 64
                bind(path, digest, reason, scan=Path(path).name == 'manifest.json' or 'BINDING' in Path(path).name)

    def scan_consumed_references(value, source):
        # Historical snapshot/focus provenance is retained byte-for-byte but
        # is not a live input map. In particular do not follow an old mutable
        # node filename in focus_validation.retained_input_sha256.
        if not isinstance(value, dict):
            return
        for name in ('sources', 'source_sha256', 'input_sha256',
                     'checker_dependency_sha256', 'independent_source_files'):
            hash_map(value.get(name, {}), 'consumed reference in ' + str(source))
        for name in ('parent', 'prefix', 'whole_original_parent', 'conditional_parent',
                     'component_parent', 'source_checker', 'first_fresh_replay'):
            ref = value.get(name)
            if isinstance(ref, dict) and isinstance(ref.get('path'), str):
                if ref['path'].startswith(str(WORKSPACE) + '/'):
                    bind(ref['path'], ref.get('sha256'), 'bound ' + name, scan=name != 'source_checker')
        for name in ('files', 'proof_checkers'):
            refs = value.get(name, {})
            if isinstance(refs, dict):
                for relative, digest in refs.items():
                    if isinstance(relative, str) and not Path(relative).is_absolute():
                        if isinstance(digest, str) and len(digest) == 64:
                            candidate = source.parent / relative
                            if candidate.is_file():
                                bind(candidate, digest, 'relative inventory in ' + str(source))

    complete_path = HERE / 'A_C744_COMPONENT1_COMPLETE_EXACT_REPLAY.json'
    complete = json.loads(complete_path.read_text())
    actual_path = args.actual_report.resolve()
    actual = json.loads(actual_path.read_text())
    assert complete['status'] == 'PASS_COMPLETE_TWO_LINK_COMPLEMENT_TREE'
    assert complete['original_id'] == actual['original_id'] == TARGET
    assert complete['original_path'] == actual['original_path'] == ORIGINAL_PATH
    assert complete['component'] == 1 and complete['open_leaves'] == 0
    assert complete['nodes'] == 757 and complete['leaf_domains'] == complete['excluded_leaves'] == 566
    assert actual['component'] == 3 and actual['open_leaves'] == 1 and actual['nodes'] == 1
    assert actual['status'] == 'PASS_PARTIAL_TWO_LINK_COMPLEMENT_TREE'
    assert actual['completed_component1_consequence_occurrences_checked'] > 0
    fresh = actual['fresh_completed_component1_consequence_source']
    assert fresh['status'] == 'PASS_FRESH_COMPLETE_COMPONENT1_ORIGINAL_CONSEQUENCE'
    assert fresh['source_report']['report']['nodes'] == 757
    assert fresh['source_report']['report']['open_leaves'] == 0
    for report_path, report in ((complete_path, complete), (actual_path, actual)):
        bind(report_path, reason='completed native exact report')
        hash_map(report['input_sha256'], 'actual exact proof input')
        hash_map(report['checker_dependency_sha256'], 'actual exact checker source')

    def tree(folder, reason):
        folder = Path(folder).resolve()
        manifest = folder / 'manifest.json'
        data = json.loads(manifest.read_text())
        bind(manifest, reason=reason, scan=True)
        for node in data['nodes']:
            bind(folder / node['file'], node['sha256'], reason)
        return dict(folder=str(folder), manifest_sha256=sha(manifest), nodes=len(data['nodes']))

    a1 = tree(HERE / 'a_c744_component1_complete_candidate', 'complete closed A1 tree')
    a3 = tree(WORKSPACE / 'd_work/A_c744_component3_a1_consequence_whole_probe', 'unsplit conditional A3 actual-use probe')
    tree(WORKSPACE / 'd_work/A_c744_component3_whole_probe', 'older conditional A3 bound source')
    files = [
        'A_C744_COMPONENT1_CLOSED_CONSEQUENCE_BINDING.json',
        'A_C744_COMPONENT1_CONSEQUENCE_EXACT_CONTROLS.json',
        'A_C744_COMPONENT1_CONSUMER_SOURCE_MATERIALIZATION.json',
        'A_C744_COMPLETE_COMPONENT1_CONSEQUENCE_HAND_PROOF.md',
        'A_C744_COMPONENT1_CLOSED_NEGATION_DERIVATION.md',
        'independent_a_c744_component1_consequence.py',
        'a_c744_component1_consequence_rows.py',
        'ac_a_c744_component3_a1_consequence_runtime.py',
        'verify_a_c744_component3_a1_consequence_lazy_tree.py',
        'verify_a_c744_component_bound_a1_consequence_lazy_tree.py',
        'A_C744_COMPONENT3_SHARED_BOUND_STATE_BINDING.json',
        'independent_a_c744_component3_shared_bound_rows.py',
        'a_c744_component3_shared_bound_rows.py',
        'A_C744_COMPONENT3_SHARED_BOUND_STATE_HAND_PROOF.md',
        'verify_a_c744_component3_shared_bounds_tree.py',
        'ac_a_c744_component3_shared_bounds_runtime.py',
        'verify_ac_two_link_consequence_four_lazy_tree.py',
        'verify_ac_two_link_unit_corner_lazy_tree.py',
        'graft_a_c744_selected_closed_subtrees.py',
        'collapse_a_c744_zero_round_selected_subtree.py',
        'A_C744_SIBLING572_SELECTED_ATTACHMENT.json',
    ]
    for name in files:
        bind(HERE / name, reason='complete A1 consequence and A3 attachment', scan=name.endswith('.json'))
    for path in sorted((HERE.parent / 'a1_consequence_prepare').iterdir()):
        if path.is_file() and path.suffix in ('.py', '.in', '.md'):
            bind(path, reason='immutable source construction and literal controls')
    for name in ('A_C744_A1_CONSEQUENCE_CONSUMER_ROOT_DESIGN_REVIEW.md',
                 'A_C744_ZERO_ROUND_RESTORATION_ROOT_REVIEW.md',
                 'A_C744_LAZY_FINAL_DISPATCH_ROOT_REVIEW.md',
                 'A_C744_COMPONENT3_SHARED_BOUNDS_ROOT_REVIEW.md',
                 'A_C744_COMPONENT3_WHOLE_PROBE_EXACT_REPLAY.json',
                 'resume_a_component3_a1_consequence_round_tree_v10.py'):
        bind(WORKSPACE / 'd_work' / name, reason='root source or review', scan=name.endswith('.json'))
    for name in ('A_LAZY_COMPONENT_TREE_REPLAY_INDEPENDENT_REVIEW.md',
                 'A_LAZY_COMPONENT_TREE_REPLAY_INDEPENDENT_REVIEW.json',
                 'A_C744_COMPONENT3_SHARED_BOUND_INDEPENDENT_REVIEW.md',
                 'A_C744_COMPONENT3_SHARED_BOUND_INDEPENDENT_REVIEW.json'):
        bind(WORKSPACE / 'b_work' / name, reason='independent bounded-memory/domain review')

    assert sha(REFERENCE) == REFERENCE_SHA
    reference = json.loads(REFERENCE.read_text())
    assert reference['original_cell']['id'] == TARGET and reference['original_cell']['path'] == ORIGINAL_PATH
    assert reference['original_cell']['status'] == 'OPEN'
    bind(REFERENCE, REFERENCE_SHA, 'current committed register definition')
    for item in reference['files'].values():
        bind(item['path'], item['sha256'], 'current committed register and physical definition')
    while pending:
        path = pending.pop()
        if path in scanned:
            continue
        scanned.add(path)
        scan_consumed_references(json.loads(path.read_text()), path)
    for key, item in new.items():
        item['reasons'] = sorted(reasons[key])
    for key, item in reused.items():
        if key in reasons:
            item['reasons'] = sorted(reasons[key])
    expected_source = {key: complete[key] for key in
        ('nodes', 'leaf_domains', 'excluded_leaves', 'open_leaves', 'rounds', 'deductions', 'printed_rows_checked')}
    expected_actual = {key: actual[key] for key in
        ('nodes', 'leaf_domains', 'excluded_leaves', 'open_leaves', 'rounds', 'deductions',
         'printed_rows_checked', 'completed_component1_consequence_occurrences_checked',
         'unit_four_corner_row_occurrences_checked')}
    plan = dict(schema='complete_A1_consequence_thin_publication_plan_v1',
        repository='vltanh/lean4-squares-in-circles', reference_commit=reference['commit'],
        reference_binding=dict(path=str(REFERENCE), sha256=REFERENCE_SHA),
        proposed_package='research/nine/computer_assisted/a2_00100_a_c744_complete_component1_consequence',
        original_id=TARGET, original_path=ORIGINAL_PATH, original_status='OPEN', component1_status='CLOSED',
        scope='Complete component1 and its original-wide weak consequence; actual conditional component3 use remains OPEN.',
        base_A_portable_archive=dict(
            repository_folder='research/nine/computer_assisted/a2_00100_a_c744_portable_open_checkpoint',
            archive_sha256='e7ddb4f4e5b943a6f69a0aa861f6721ca49835311fa595ef40a10881b62e4343',
            input_manifest_sha256=BASE_MANIFEST_SHA, files_reused=len(reused), reused_files=dict(sorted(reused.items()))),
        new_payload_files=dict(sorted(new.items())), new_payload_files_count=len(new),
        new_payload_uncompressed_bytes=sum(item['bytes'] for item in new.values()),
        complete_component1=a1, actual_component3_probe=a3,
        exact_reports=dict(component1=bind(complete_path), actual_component3=bind(actual_path)),
        expected_source=expected_source, expected_actual=expected_actual,
        original_necessary_row=dict(coefficients=[[3, '-1'], [7, '1']], rhs='3/5'),
        no_base_bytes_duplicated=True, no_existing_input_overwritten=True, live_frontier_included=False,
        saved_reports_not_used_as_arithmetic_premises=True,
        portable_protocol='Fresh actual A3 consumer repeats the old complete A1 checker before using its consequence; literal controls are separately repeated.',
        new_original_cells=0, new_masks=0, lean_lake_ci_run=False)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(plan, indent=2) + '\n')
    print(json.dumps(dict(status='PASS_PREPARED_COMPLETE_A1_THIN_INPUT_PLAN', path=str(output),
        sha256=sha(output), new_files=len(new), new_bytes=plan['new_payload_uncompressed_bytes'],
        reused_aliases=len(reused), expected_source=expected_source, expected_actual=expected_actual), indent=2))


if __name__ == '__main__':
    main()
