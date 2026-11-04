#!/usr/bin/env python3
"""Independent byte/member and receipt audit; no numerical or geometric solver."""
from pathlib import Path, PurePosixPath
import hashlib
import json
import subprocess
import tarfile
import time

ROOT = Path('/workspace/scratch/f9f48fcfb253/ac_work/compact_A1_publication')
OUT = Path('/workspace/scratch/f9f48fcfb253/d_work/A_C744_COMPLETE_A1_THIN_ARCHIVE_ROOT_AUDIT.json')
PINS = {
    'PUBLICATION_READY.json': 'aeb210d0092f77ce33f3a0c10505cd0d8d30bd90e363e67da502f59f7fb446bf',
    'TRANSPORT_SOURCE_BINDINGS.json': '5d8bf21b128699cfedeba6d3873dfeeadcce5dc31a41ad1119a67260e60ea019',
    'delta_v2/DELTA_MANIFEST.json': '70c971d00fb804d0765cce66ef540b3c79e18a0eed29b08d5f63793b94eedf4d',
    'delta_v2/INPUT_MANIFEST.json': 'd8ca6d465aa3831e26d6d0149b8ce734a1043c51694f81a9ce9b9a4e3baaf965',
    'fresh_replay_v2/PORTABLE_RECEIPT.json': 'b4803409d7b163a8b4f8704ebfe4fd90d2f7edf9f7034b33cd1133cdf1d94d36',
    'fresh_replay_v2/A3_ACTUAL_COMPLETE_A1_CONSEQUENCE_REPLAY_COMPLETE_COMPONENT1_SOURCE/complete_component1_replay.json': '16cf7ecdaed399633ca3c72d926a5587599686eed18f7dd7a5f6770bba9c5ec1',
    'fresh_replay_v2/A3_ACTUAL_COMPLETE_A1_CONSEQUENCE_REPLAY.json': 'c1766b6dc98ef41dfc05d6499ed257100fa5cf1d634e26c361aee989abd0a17b',
    'fresh_replay_v2/A1_CONSEQUENCE_LITERAL_SCOPE_CONTROLS.json': '28273c40c1aabc1cff29406c2dceda0e8dfcf00db723325d60dbbc580c2d8774',
}

def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for b in iter(lambda: f.read(1024 * 1024), b''):
            h.update(b)
    return h.hexdigest()

def main():
    started = time.monotonic()
    assert not OUT.exists(), OUT
    for name, pin in PINS.items():
        assert digest(ROOT / name) == pin, name
    ready = json.loads((ROOT / 'PUBLICATION_READY.json').read_text())
    archive = Path(ready['archive'])
    assert archive == ROOT / 'complete_a1_consequence_delta_v2.tar.xz'
    assert archive.stat().st_size == ready['archive_bytes'] == 63425472
    assert digest(archive) == ready['archive_sha256'] == '8378b765edebbba407e394ed98743193a556255687f7ddb8480bafe31d5710f2'
    subprocess.run(['xz', '-t', str(archive)], check=True)

    delta = ROOT / 'delta_v2'
    declaration = json.loads((delta / 'DELTA_MANIFEST.json').read_text())
    expected = dict(declaration['files'])
    expected['DELTA_MANIFEST.json'] = PINS['delta_v2/DELTA_MANIFEST.json']
    assert len(expected) == 859
    sizes = {}
    for name, pin in expected.items():
        pp = PurePosixPath(name)
        assert not pp.is_absolute() and '..' not in pp.parts
        p = delta / name
        assert p.is_file() and not p.is_symlink()
        assert digest(p) == pin, name
        sizes[name] = p.stat().st_size
    assert sum(sizes.values()) == 607136233

    actual = {}
    with tarfile.open(archive, mode='r|xz') as tar:
        for member in tar:
            pp = PurePosixPath(member.name)
            assert member.isfile() and not member.issym() and not member.islnk(), member.name
            assert not pp.is_absolute() and '..' not in pp.parts
            assert pp.parts[0] == 'complete_a1_consequence_delta_v2'
            name = str(PurePosixPath(*pp.parts[1:]))
            assert name in expected and name not in actual, name
            assert member.size == sizes[name]
            h = hashlib.sha256()
            stream = tar.extractfile(member)
            assert stream is not None
            for b in iter(lambda: stream.read(1024 * 1024), b''):
                h.update(b)
            assert h.hexdigest() == expected[name], name
            actual[name] = {'sha256': h.hexdigest(), 'bytes': member.size}
    assert set(actual) == set(expected)

    bindings = json.loads((ROOT / 'TRANSPORT_SOURCE_BINDINGS.json').read_text())
    for name, item in bindings['files'].items():
        p = ROOT / name
        assert p.stat().st_size == item['bytes'] and digest(p) == item['sha256'], name
    for name, item in bindings['source_transport_scripts'].items():
        p = Path(name)
        assert p.stat().st_size == item['bytes'] and digest(p) == item['sha256'], name

    receipt = json.loads((ROOT / 'fresh_replay_v2/PORTABLE_RECEIPT.json').read_text())
    assert receipt['status'] == 'PASS_FRESH_PORTABLE_COMPLETE_A1_CONSEQUENCE_AND_ACTUAL_A3_USE'
    assert receipt['complete_component1'] == dict(nodes=757, leaf_domains=566, excluded_leaves=566,
        open_leaves=0, rounds=230, deductions=74846, printed_rows_checked=134855,
        report_sha256=PINS['fresh_replay_v2/A3_ACTUAL_COMPLETE_A1_CONSEQUENCE_REPLAY_COMPLETE_COMPONENT1_SOURCE/complete_component1_replay.json'])
    assert receipt['actual_component3_use']['open_leaves'] == 1
    assert receipt['actual_component3_use']['completed_component1_consequence_occurrences_checked'] == 2
    assert receipt['actual_component3_use']['report_sha256'] == PINS['fresh_replay_v2/A3_ACTUAL_COMPLETE_A1_CONSEQUENCE_REPLAY.json']
    assert receipt['original_necessary_row'] == {'coefficients': [[3, '-1'], [7, '1']], 'rhs': '3/5'}
    for field in ['all_packet_writes_and_mutations_forbidden', 'external_workspace_reads_forbidden_in_every_child',
                  'numerical_imports_forbidden', 'all_inputs_rehashed_at_completion',
                  'conditional_A3_order_not_claimed_on_whole_original', 'whole_original_exclusion_not_claimed']:
        assert receipt[field] is True, field
    assert receipt['native_saved_reports_used_as_arithmetic_premises'] is False
    assert receipt['lean_lake_ci_run'] is False
    assert receipt['new_original_cells'] == receipt['new_masks'] == 0
    assert receipt['original_status'] == 'OPEN' and receipt['component1_status'] == 'CLOSED'
    assert receipt['input_files'] == 2249
    assert receipt['packet_manifest_sha256'] == PINS['delta_v2/INPUT_MANIFEST.json']
    for name, pin in expected.items():
        assert digest(delta / name) == pin, name
    report = dict(status='PASS_ROOT_COMPLETE_A1_THIN_ARCHIVE_AND_RECEIPT_AUDIT',
        archive_sha256=digest(archive), archive_bytes=archive.stat().st_size,
        xz_integrity_passed=True, regular_members=len(actual), uncompressed_bytes=sum(sizes.values()),
        members_rehashed=True, source_members_rehashed_before_and_after=True,
        unsafe_paths_links_duplicates_or_extra_members=0,
        outer_bound_files=len(bindings['files']), transport_scripts=len(bindings['source_transport_scripts']),
        pinned_metadata=PINS, required_published_base=ready['required_base'],
        fresh_receipt_arithmetic_counts=receipt['complete_component1'],
        actual_component3_use=receipt['actual_component3_use'],
        no_new_arithmetic_replay_claimed=True, new_original_cells=0, new_masks=0,
        whole_original_status='OPEN', component1_status='CLOSED',
        source_sha256=digest(Path(__file__)), seconds=time.monotonic()-started)
    OUT.write_text(json.dumps(report, indent=2, sort_keys=True)+'\n')
    print(json.dumps({k: report[k] for k in ['status','regular_members','outer_bound_files','transport_scripts','seconds']}), flush=True)

if __name__ == '__main__':
    main()
