"""Independent whole-member and ordered-part audit of the complete D821 release.

No arithmetic discovery, proof-input edits, extraction or raw tar copy.
The native/cold proof comparison removes only elapsed time and explicitly
bound filename transport aliases. Every other mathematical field must agree.
"""
from pathlib import Path
from copy import deepcopy
import hashlib
import json
import os
import subprocess
import tarfile
import time

WORK = Path('/workspace/scratch/f9f48fcfb253')
PACKET = Path('/tmp/d821_complete_portable_v1_20261104/d821_complete_original_package')
ARCHIVES = WORK / 'global_work/d821_complete_archive_v1'
TARGET = 'positive-821c9a2debeed0aa'
PATH = [['angle', 3, 1], ['angle_cut', [0, '0'], 1],
        ['alternate_four_escape', [1, 7], [3]]]
PINS = {
    'INPUT_MANIFEST.json': '5aa6efecb64df25da202b895d609598e8d66d8f13a77f172af3d0ccf25184a63',
    'release_audits/FRESH_COMPLETE_ORIGINAL_REPLAY.json':
        '29babcc1c812d09b07a84d7381414f6f0053e1d435b782ac673af3b024abb35f',
    'release_audits/FRESH_PORTABLE_RECEIPT.json':
        '8b873cf6dd8cc7ad608383e326303464e709e86151ad0bf66e55cffd6ade51e3',
    'COMPLETE_TERMINAL_TABLE.json':
        'b03e757483783857be389caf2687fe2b13060b9338a0e5c56ad36e2b91b4e661',
    'COMPLETE_TERMINAL_TABLE.md':
        'fb399861ae87d51ca493836ea9bbced5565e35e076838ff4c0acd53f491ecf4b',
}


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(4 * 1024 * 1024), b''):
            digest.update(block)
    return digest.hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def literal(root, name):
    relative = Path(name)
    assert not relative.is_absolute() and '..' not in relative.parts
    path = root / relative
    assert not path.is_symlink() and path.resolve().is_relative_to(root)
    assert path.is_file()
    return path


def main():
    assert __debug__
    started = time.monotonic()
    output = WORK / 'd_work/D821_COMPLETE_ROOT_ARCHIVE_AUDIT.json'
    assert not output.exists()
    for name, digest in PINS.items():
        assert sha(literal(PACKET, name)) == digest, name
    input_manifest = read(PACKET / 'INPUT_MANIFEST.json')
    assert len(input_manifest['files']) == 2432
    assert input_manifest['external_workspace_reads_forbidden']
    assert input_manifest['numerical_imports_forbidden']
    ready_path = ARCHIVES / 'ARCHIVE_READY.json'
    ready = read(ready_path)
    assert ready['original_id'] == TARGET and ready['original_path'] == PATH
    assert ready['mask'] == '001/00' and ready['complete_original']
    assert ready['new_original_cell_credit'] == 1 and ready['new_mask_credit'] == 0
    assert ready['complete_closed_complement_domains'] == 5
    assert ready['tree_count'] == 46 and ready['node_count'] == 650
    assert ready['xz_integrity_pass'] and ready['all_member_hashes_match']
    assert ready['fresh_portable_replay_pass'] and ready['streaming_compression']
    assert ready['raw_tar_intermediate_created'] is False
    assert ready['packet_input_manifest_sha256'] == PINS['INPUT_MANIFEST.json']
    archive = literal(ARCHIVES, ready['archive'])
    assert sha(archive) == ready['archive_sha256']
    assert archive.stat().st_size == ready['archive_bytes']
    concatenated = hashlib.sha256()
    part_bytes = 0
    assert ready['parts']
    for index, entry in enumerate(ready['parts'], 1):
        assert entry['file'] == ready['archive'] + f'.part{index:03d}'
        part = literal(ARCHIVES, entry['file'])
        assert part.stat().st_size == entry['bytes']
        assert 0 < entry['bytes'] <= 8 * 1024 * 1024
        if index < len(ready['parts']):
            assert entry['bytes'] == 8 * 1024 * 1024
        assert sha(part) == entry['sha256']
        with part.open('rb') as stream:
            for block in iter(lambda: stream.read(4 * 1024 * 1024), b''):
                concatenated.update(block)
                part_bytes += len(block)
    assert part_bytes == ready['archive_bytes']
    assert concatenated.hexdigest() == ready['archive_sha256']
    subprocess.run(['xz', '-t', str(archive)], check=True)

    release_path = PACKET / 'RELEASE_MANIFEST.json'
    assert sha(release_path) == ready['release_manifest_sha256']
    release = read(release_path)
    assert release['original_id'] == TARGET and release['original_path'] == PATH
    assert release['complete_original'] and release['mathematical_inputs_unchanged']
    expected = dict(release['files'])
    assert 'RELEASE_MANIFEST.json' not in expected
    expected['RELEASE_MANIFEST.json'] = ready['release_manifest_sha256']
    assert len(expected) == 2436 == ready['all_archive_members_verified']
    assert set(input_manifest['files']).issubset(expected)
    assert all(expected[name] == digest for name, digest in input_manifest['files'].items())
    assert all(expected[name] == digest for name, digest in PINS.items())
    seen = set()
    with tarfile.open(archive, 'r|xz') as stream:
        for member in stream:
            if member.isdir():
                continue
            assert member.isfile() and member.name.startswith(PACKET.name + '/')
            name = member.name[len(PACKET.name) + 1:]
            assert name in expected and name not in seen
            assert not Path(name).is_absolute() and '..' not in Path(name).parts
            source = stream.extractfile(member)
            assert source is not None
            digest = hashlib.sha256()
            for block in iter(lambda: source.read(4 * 1024 * 1024), b''):
                digest.update(block)
            assert digest.hexdigest() == expected[name], name
            seen.add(name)
    assert seen == set(expected)
    actual = {str(p.relative_to(PACKET)) for p in PACKET.rglob('*') if p.is_file()}
    assert actual == set(expected)
    for name, digest in expected.items():
        assert sha(literal(PACKET, name)) == digest, name

    native_path = WORK / 'global_work/d821_work/D821_COMPLETE_ORIGINAL_EXACT_REPLAY.json'
    assert sha(native_path) == 'c56785bc3953b85b2c3069bb8bf61ec655d3d174c652595cc6e25928ae0a53b4'
    native = read(native_path)
    fresh = read(PACKET / 'release_audits/FRESH_COMPLETE_ORIGINAL_REPLAY.json')
    receipt = read(PACKET / 'release_audits/FRESH_PORTABLE_RECEIPT.json')
    assert receipt['status'] == 'PASS_FRESH_PORTABLE_COMPLETE_ORIGINAL_D821'
    assert receipt['packet_manifest_sha256'] == PINS['INPUT_MANIFEST.json']
    assert receipt['exact_report_sha256'] == PINS['release_audits/FRESH_COMPLETE_ORIGINAL_REPLAY.json']
    assert receipt['input_files'] == 2432 and receipt['input_bytes'] == 2422735486
    for key in ('all_inputs_rehashed_at_completion', 'exact_mathematical_sources_unchanged',
                'external_workspace_reads_forbidden', 'numerical_imports_forbidden'):
        assert receipt[key] is True
    assert receipt['new_original_cells'] == 1 and receipt['new_masks'] == 0
    assert receipt['lean_lake_ci_run'] is False
    bindings = read(PACKET / 'BINDINGS.json')['files']
    aliases = {}
    for logical, entry in bindings.items():
        actual_name = str(literal(PACKET, entry['path']))
        assert entry['sha256'] == expected[entry['path']]
        assert actual_name not in aliases or aliases[actual_name] == logical
        aliases[actual_name] = logical
    normalized = deepcopy(fresh)
    for field in ('input_sha256', 'checker_sha256'):
        checked = {}
        for name, digest in fresh[field].items():
            logical = aliases.get(name, name)
            assert logical not in checked or checked[logical] == digest
            checked[logical] = digest
        normalized[field] = checked
    old = deepcopy(native)
    del old['seconds']
    del normalized['seconds']
    assert normalized == old
    assert len(normalized['input_sha256']) == 889
    assert len(normalized['checker_sha256']) == 6
    assert native['status'] == 'PASS_COMPLETE_ORIGINAL_CELL'
    assert native['whole_original_proved'] is True
    assert native['original_id'] == TARGET and native['original_path'] == PATH
    assert native['complete_closed_complement_domains'] == 5
    assert len(native['grafted_cover_nodes']) == len(native['exact_tree_reports']) == 46
    assert native['plan_sha256'] == '6fc6a6f3840b99f99ddec479c8a3ea1bae0e3c2d1dd6c7010318150a9a95a3a9'
    assert sum(len(r['node_audits']) for r in native['exact_tree_reports'].values()) == 650

    result = dict(
        status='PASS_ROOT_D821_COMPLETE_ARCHIVE_AND_PART_AUDIT',
        original_id=TARGET, original_path=PATH,
        archive_sha256=ready['archive_sha256'], archive_bytes=part_bytes,
        complete_part_count=len(ready['parts']), every_part_hash_checked=True,
        concatenated_part_digest_matches_archive=True, independent_xz_integrity_pass=True,
        all_regular_members_verified=len(seen), all_source_packet_bytes_rehashed=True,
        all_2432_frozen_inputs_unchanged=True,
        release_manifest_sha256=ready['release_manifest_sha256'],
        fresh_complete_report_sha256=PINS['release_audits/FRESH_COMPLETE_ORIGINAL_REPLAY.json'],
        fresh_portable_receipt_sha256=PINS['release_audits/FRESH_PORTABLE_RECEIPT.json'],
        input_manifest_sha256=PINS['INPUT_MANIFEST.json'],
        archive_ready_sha256=sha(ready_path),
        native_and_cold_all_mathematical_fields_identical=True,
        only_comparison_normalizations=['elapsed_seconds', 'explicit_hash_bound_filename_aliases'],
        normalized_input_hashes=889, normalized_checker_hashes=6,
        raw_tar_intermediate_created=False, weighted_arithmetic_repeated_by_this_audit=False,
        numerical_optimizer_called=False, no_original_ledger_mutation_by_auditor=True,
        new_masks=0, source_sha256=sha(__file__), seconds=time.monotonic() - started)
    output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2), flush=True)


if __name__ == '__main__':
    main()
