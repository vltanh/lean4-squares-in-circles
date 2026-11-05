#!/usr/bin/env python3
"""Fresh exact native replay of the published C887 complete D/G bound proof."""
if not __debug__:
    raise RuntimeError('Exact source replay requires assertions.')
from pathlib import Path, PurePosixPath
import hashlib
import json
import subprocess
import sys
import tarfile

ROOT = Path(__file__).resolve().parents[1]
PACKET = ROOT / 'd_work/external_c887_fresh_state_4efd'
NATIVE = Path('/workspace/scratch/8446ce74729c/pr11/research/nine/.runs/c_family')
ARCHIVE_SHA = '010bc1b9a89711bbf06bc4ad0ea867d5e9663458bdc2f35d982b970cec3fa665'
DEPENDENCY_SHA = 'f4d8441a29920b6ac05ab2b23cd85fe4e4587953ff9f1a2697bf99ddc1bc4847'
MANIFEST_SHA = '6d68b6fbd7184ff8a47001aafd6c5727a08b33955f40b8fcec814443fe9aeb3c'
ENTRY_SHA = '7043fdb894144a1d0cceee108338de2af85e963a2f11da774f834e5eef57f16e'

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def write(path, value):
    with path.open('x') as stream:
        json.dump(value, stream, indent=2, sort_keys=True); stream.write('\n')

def inputs():
    archive = PACKET / 'c887_fresh_whole_state_v1.tar.xz'
    assert sha(archive) == ARCHIVE_SHA
    assert sha(PACKET / 'DEPENDENCY_BINDINGS.json') == DEPENDENCY_SHA
    payload = {}
    with tarfile.open(archive, 'r:xz') as tar:
        for entry in tar:
            path = PurePosixPath(entry.name)
            assert not path.is_absolute() and '..' not in path.parts
            assert path.parts[0] == 'c887_fresh_whole_state_v1'
            assert not entry.issym() and not entry.islnk()
            if entry.isdir():
                continue
            assert entry.isfile()
            name = str(path.relative_to('c887_fresh_whole_state_v1'))
            assert name not in payload
            payload[name] = tar.extractfile(entry).read()
    assert len(payload) == 26
    manifest = json.loads(payload['MANIFEST.json'])
    assert set(payload) == {entry['path'] for entry in manifest['files']} | {'MANIFEST.json'}
    copied = {}
    for entry in manifest['files']:
        raw = payload[entry['path']]
        assert len(raw) == entry['bytes'] and hashlib.sha256(raw).hexdigest() == entry['sha256']
        if 'source_path' in entry:
            copied[entry['source_path']] = entry['sha256']
    bindings = json.loads((PACKET / 'DEPENDENCY_BINDINGS.json').read_text())
    saved = json.loads(payload['reports/fresh_whole_state_replay.json'])
    rejoined = json.loads(payload['reports/rejoined_tree_partial_replay.json'])
    assert len(bindings['input_sha256']) == 510
    assert len(rejoined['checker_dependency_sha256']) == 54
    pins = {}
    for group in (bindings['input_sha256'], bindings['local_height_transport']['input_sha256'],
                  rejoined['checker_dependency_sha256'], copied):
        for path, expected in group.items():
            assert path not in pins or pins[path] == expected
            pins[path] = expected
    for name in ('c887_fresh_ancestry.py', 'c887_fresh_dg_union_replay.py',
                 'check_c887_complete_cover.py', 'independent_c_general_rows_adapter.py',
                 'local_c_height_transport.py', 'replay_c887_original_prefix.py',
                 'verify_c887_fresh_dg_union.py'):
        local = PACKET / 'code' / name; native = NATIVE / name
        assert local.read_bytes() == native.read_bytes() == payload['code/' + name]
        pins[str(native)] = sha(native)
    assert pins[str(NATIVE / 'verify_c887_fresh_dg_union.py')] == ENTRY_SHA
    assert pins[str(NATIVE / 'c887_fresh_dg_union_refined/MANIFEST.json')] == MANIFEST_SHA
    for path, expected in pins.items():
        assert sha(path) == expected, path
    return pins, saved

def main():
    output = ROOT / 'd_work/c887_external_fresh_gate_v1'
    assert not output.exists()
    pins, saved = inputs()
    output.mkdir()
    report = output / 'FRESH_WHOLE_STATE_REPLAY.json'
    argv = [sys.executable, '-B', '-S', '-u', str(NATIVE / 'verify_c887_fresh_dg_union.py'),
            str(NATIVE / 'c887_fresh_dg_union_refined/MANIFEST.json'), str(report)]
    with (output / 'FRESH_WHOLE_STATE_REPLAY.log').open('x') as log:
        completed = subprocess.run(argv, check=False, stdout=log, stderr=subprocess.STDOUT)
    assert completed.returncode == 0, completed.returncode
    again, old_saved = inputs()
    assert again == pins and old_saved == saved
    result = json.loads(report.read_text())
    assert result['status'] == 'PASS_FRESH_WHOLE_C887_COMPLETE_DG_UNION_BOUNDS'
    assert result['original_id'] == 'negative-887236b78100baf3'
    assert result['original_path'] == [['angle',3,0],['angle_cut',[0,'0'],1],['alternate_four_escape',[1,7],[1]]]
    assert result['certified_state'] == saved['certified_state']
    assert result['whole_original_excluded'] is False
    assert result['old_starting_state_implied'] and result['old_state_interval_deficits'] == []
    assert result['all_eight_closed_alternatives_checked'] and result['child_auxiliaries_discarded']
    assert result['original_parent_path_unchanged'] and not result['missing_archived_bound_state_assumed']
    assert result['no_selected_child_assumed'] and not result['numerical_producer_imported']
    assert result['new_original_cells'] == result['new_masks'] == 0
    assert result['new_row_counts']['rotating_tangent'] == 0
    root_audit = result['initial_original_bounds']['round_audit']
    assert (root_audit['rounds'], root_audit['deductions'], root_audit['printed_rows_checked']) == (6,624,1288)
    cover = result['complete_union']['complete_cover']
    assert cover['all_eight_physical_alternatives'] and cover['closed_faces_retained']
    assert cover['excluded_alternatives'] == 4 and len(cover['children']) == 8
    receipt = dict(status='PASS_ROOT_FRESH_EXACT_C887_WHOLE_ORIGINAL_DG_UNION_BOUNDS',
        helper_sha256=sha(__file__), published_commit='4efd616976b22fb3dd1802a0314deba461753099',
        archive_sha256=ARCHIVE_SHA, dependency_binding_sha256=DEPENDENCY_SHA,
        exact_native_source_and_input_pins=pins, native_inputs_rehashed_before_and_after=len(pins),
        native_subprocess_argv=argv, native_subprocess_observed_exit_code=completed.returncode,
        fresh_report_sha256=sha(report), fresh_log_sha256=sha(output/'FRESH_WHOLE_STATE_REPLAY.log'),
        six_root_rounds_freshly_replayed=True, root_deductions=624, root_printed_rows=1288,
        complete_DG_alternatives=8, excluded_DG_alternatives=4,
        certified_whole_original_hull_identical_to_published=True,
        missing_old_starting_archive_not_used=True, old_target_used_only_as_weaker_statement=True,
        numerical_solver_called=False, source_or_active_tree_bytes_changed=False,
        new_original_cells=0, new_masks=0, lean_lake_ci_run=False)
    write(output/'ROOT_FRESH_REPLAY_RECEIPT.json',receipt)
    print(json.dumps({k:receipt[k] for k in ('status','native_inputs_rehashed_before_and_after',
        'fresh_report_sha256','root_deductions','complete_DG_alternatives','excluded_DG_alternatives')}),flush=True)

if __name__ == '__main__':
    main()
