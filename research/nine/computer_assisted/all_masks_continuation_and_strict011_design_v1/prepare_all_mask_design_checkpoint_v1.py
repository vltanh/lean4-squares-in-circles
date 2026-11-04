#!/usr/bin/env python3
"""Collect immutable planning/design evidence; never alter a closure register."""
import argparse
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

PLAN_SHA = '0fe9b64282a8adcc97896e8b0e0ced7d5ebb585a20dd4944052ea00d263d781f'
DESIGN_SHA = 'eebb35b564c98668d614b86f07c0aae18b761912e82f9fedfbfcfc525180265f'
PARENT = '2c0fb06a27cd568297c2b9320e005eb33ae89cdb'
HISTORICAL = '925e1112814a0758889cafa5c975c27414b86570'
CURRENT_REGISTER = '3dfaff7a880ab358930fb0ea835a1fdbe9959711f3c08ac47ee9817e7c693dde'
REGISTER = 'repo/research/nine/gates/A2_00100_FIXED_FRONTIER.json'
REVIEW_PINS = {
    'b_work/ALL_MASK_CONTINUATION_PLAN_INDEPENDENT_REVIEW.md': 'a18a4a5b4d911d489f07e725a6fc7516a33629f6de5fdaed035c0b94bb72df38',
    'b_work/ALL_MASK_CONTINUATION_PLAN_INDEPENDENT_REVIEW.json': '220cfcb8871f65c69a7a73149da2f4a3848a96b37cfe64649f9a4900768bd9cb',
    'ac_work/tree/review_strict_011_prepared_root.py': '83626b94dd64f767f42d2b8f90f8bb2ec6903b509e5749fd55c32fa2e026dacb',
    'ac_work/tree/STRICT_011_PREPARED_ROOT_INDEPENDENT_REVIEW.md': 'fede05d806d43582fe766a5202cabbded58535d1fa4326cc9398925a5a4a1c9c',
    'ac_work/tree/STRICT_011_PREPARED_ROOT_INDEPENDENT_REVIEW.json': 'ef974eab78baf11ddf66082c446dbb9be24c9310e6540265be82c41762c5a918',
}
OPTIONAL_PINS = {
    'OPTIONAL_UNIVERSAL_CENTER_BOUND.md': 'b1d5d06aca61bef6d351389dc1b3337270c8bf6bdb6707511a8da8cdccf9983c',
    'OPTIONAL_UNIVERSAL_CENTER_BOUND.json': '05d49956fe1f0db69cd9889466091d0b2af18cf70ec0d451e72634c3a4845444',
}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def write_json(path, value):
    with path.open('x') as stream:
        json.dump(value, stream, indent=2, sort_keys=True)
        stream.write('\n')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--workspace', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    root, out = args.workspace.resolve(), args.output.resolve()
    if out.exists():
        raise FileExistsError(out)
    plan_dir = root / 'global_work/all_mask_continuation_plan_v1'
    design_dir = root / 'global_work/strict_011_root_adapter_design'
    plan_bytes = (plan_dir / 'PLAN_BINDINGS.json').read_bytes()
    design_bytes = (design_dir / 'SOURCE_MAP.json').read_bytes()
    assert digest(plan_bytes) == PLAN_SHA
    assert digest(design_bytes) == DESIGN_SHA
    plan, design = json.loads(plan_bytes), json.loads(design_bytes)
    assert plan['repository_head_at_snapshot'] == HISTORICAL
    current = (root / REGISTER).read_bytes()
    assert digest(current) == CURRENT_REGISTER
    now = json.loads(current)
    assert (now['original_cells'], now['closed_cells'], now['open_cells']) == (231, 222, 9)
    assert now['whole_mask_closed'] is False
    sources = {}
    for entry in list(plan['sources'].values()) + design['sources']:
        key = entry['path']
        identity = {'sha256': entry['sha256'], 'bytes': entry['bytes']}
        if key in sources:
            assert sources[key] == identity, key
        sources[key] = identity
    out.mkdir(parents=True)
    origins = {}

    def put(relative, data):
        destination = out / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        with destination.open('xb') as stream:
            stream.write(data)

    for logical, expected in sorted(sources.items()):
        native = root / logical
        if logical == REGISTER:
            data = subprocess.check_output(['git', 'show', HISTORICAL + ':' + logical[5:]], cwd=root / 'repo')
            origin = {'kind': 'historical_git_blob', 'commit': HISTORICAL, 'repository_path': logical[5:]}
        elif native.is_file():
            data = native.read_bytes()
            origin = {'kind': 'unchanged_native_file', 'logical_path': logical}
        elif logical.startswith('repo/'):
            data = subprocess.check_output(['git', 'show', PARENT + ':' + logical[5:]], cwd=root / 'repo')
            origin = {'kind': 'published_git_blob', 'commit': PARENT, 'repository_path': logical[5:]}
        else:
            raise FileNotFoundError(native)
        assert len(data) == expected['bytes'] and digest(data) == expected['sha256'], logical
        put('source_snapshot/' + logical, data)
        origins[logical] = dict(expected, provenance=origin, packaged_path='source_snapshot/' + logical)

    put('plan/PLAN_BINDINGS.json', plan_bytes)
    for name, expected in plan['outputs'].items():
        data = (root / expected['path']).read_bytes()
        assert digest(data) == expected['sha256'] and len(data) == expected['bytes'], name
        put('plan/' + name, data)
    put('strict011_design/SOURCE_MAP.json', design_bytes)
    for name, expected in design['prepared_files'].items():
        data = (design_dir / name).read_bytes()
        assert digest(data) == expected['sha256'] and len(data) == expected['bytes'], name
        put('strict011_design/' + name, data)
    for name, expected in OPTIONAL_PINS.items():
        data = (design_dir / name).read_bytes()
        assert digest(data) == expected
        put('strict011_design/' + name, data)
    for path, expected in REVIEW_PINS.items():
        data = (root / path).read_bytes()
        assert digest(data) == expected
        put('reviews/' + Path(path).name, data)
    put('CURRENT_FIXED_REGISTER_SNAPSHOT.json', current)

    historical = json.loads((out / 'source_snapshot' / REGISTER).read_bytes())
    assert (historical['closed_cells'], historical['open_cells']) == (221, 10)
    before = {row['id']: row for row in historical['cells']}
    after = {row['id']: row for row in now['cells']}
    assert len(before) == len(after) == 231 and before.keys() == after.keys()
    changed = [key for key in before if before[key] != after[key]]
    assert changed == ['positive-821c9a2debeed0aa'], changed
    assert before[changed[0]]['status'] == 'OPEN' and after[changed[0]]['status'] == 'CLOSED'
    masks = json.loads((out / 'source_snapshot/repo/research/nine/gates/A2_MASK_FRONTIER.json').read_bytes())
    assert (masks['mask_count'], masks['closed_for_strict_radius_count'], masks['open_count']) == (32, 8, 24)
    state = {
        'schema': 'all_mask_plan_and_uninstalled_strict011_design_publication_state_v1',
        'status': 'REVIEWED_PLAN_AND_PREPARED_DESIGN_ONLY',
        'current_accepted_parent_commit': PARENT,
        'historical_plan_snapshot_commit': HISTORICAL,
        'historical_fixed_original_counts': {'total': 231, 'closed': 221, 'open': 10},
        'current_fixed_original_counts': {'total': 231, 'closed': 222, 'open': 9},
        'current_fixed_register_sha256': CURRENT_REGISTER,
        'accepted_change_since_historical_snapshot': changed,
        'all_other_230_cell_entries_unchanged': True,
        'current_open_original_ids': sorted(k for k, row in after.items() if row['status'] == 'OPEN'),
        'whole_mask_counts': {'total': 32, 'closed_strict': 8, 'open': 24},
        'remaining_reversal_classes': 14,
        'conditional_after_complete_00100_and_reversal': {'open_masks': 22, 'classes': 13},
        'positional_root_denominator': 7915,
        'roadmap_id_denominator': 15,
        'new_original_closures': 0, 'new_mask_closures': 0,
        'new_positional_root_exclusions': 0, 'new_roadmap_gate_closures': 0,
        'strict011_geometry_adapter_installed': False,
        'optional_universal_center_bound_installed': False,
        'numerical_solver_called': False, 'exact_tree_replay_performed_by_checkpoint': False,
        'lean_lake_ci_run': False, 'current_ledgers_modified': False,
        'portable_geometric_proof': False,
        'snapshot_files_are_historical_or_current_evidence_not_live_registers': True,
    }
    write_json(out / 'PUBLICATION_STATE.json', state)
    write_json(out / 'SOURCE_RECOVERY_AND_RECONCILIATION.json', {
        'schema': 'all_mask_design_source_recovery_v1',
        'sources': origins,
        'all_pinned_source_bytes_present_and_unchanged': True,
        'historical_plan_and_reviews_kept_byte_for_byte': True,
        'D821_current_acceptance': 'Published full portable proof at ' + PARENT,
        'historical_pending_flags_are_not_current_status': True,
        'transitive_proof_dependencies_not_collected': True,
        'reference_source_files_do_not_authorize_imports_or_proof_use': True,
    })
    put('prepare_all_mask_design_checkpoint_v1.py', Path(__file__).read_bytes())
    put('verify_checkpoint.py', (root / 'd_work/verify_all_mask_design_checkpoint_v1.py').read_bytes())
    put('README.md', (root / 'd_work/ALL_MASK_DESIGN_CHECKPOINT_README.md').read_bytes())
    files = {}
    for path in sorted(out.rglob('*')):
        if path.is_file():
            data = path.read_bytes()
            files[path.relative_to(out).as_posix()] = {'sha256': digest(data), 'bytes': len(data)}
    manifest = {
        'schema': 'all_mask_plan_and_prepared_strict011_design_manifest_v1',
        'status': 'SOURCE_AND_DESIGN_CHECKPOINT_NO_NEW_PROOF_CREDIT',
        'accepted_parent_commit': PARENT,
        'scope': 'Complete remaining-mask plan and uninstalled strict011 root design with exact source snapshots and reviews',
        'files': files, 'file_count_excluding_this_manifest': len(files),
        'total_bytes_excluding_this_manifest': sum(v['bytes'] for v in files.values()),
        'source_count_after_exact_path_deduplication': len(origins),
        'new_original_closures': 0, 'new_mask_closures': 0,
        'root_adapter_installed': False, 'self_contained_geometric_proof': False,
        'reference_only_source_categories': ['legacy_reference_prohibited_import', 'discovery_reference_only', 'fixed_original_reference_only'],
        'all_original_physical_constraints_retained': {'originals': 9, 'corners': 36, 'pairs': 36, 'cones': 5},
        'prepared_elementary_rows': 159, 'prepared_owned_pair_alternatives': 288,
    }
    write_json(out / 'PUBLICATION_MANIFEST.json', manifest)
    assert digest((root / REGISTER).read_bytes()) == CURRENT_REGISTER
    print(json.dumps({'status': 'PREPARED', 'path': str(out), 'files': len(files) + 1,
                      'bytes': manifest['total_bytes_excluding_this_manifest'],
                      'manifest_sha256': digest((out / 'PUBLICATION_MANIFEST.json').read_bytes())}))


if __name__ == '__main__':
    main()
